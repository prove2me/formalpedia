-- Prove2me | solution 1 for StratifyMarkets.DoubleAuction.lemma_4_4
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T06:47:18.366201+00:00
-- url     : https://prove2.me/submissions/3e7d6f86-9358-493e-9e26-91cac3aec8d3

import Definitions.Def_StratifyMarkets_DoubleAuction_Prices
import Definitions.Def_StratifyMarkets_DoubleAuction_WorstRationed
import Mathlib
import Theorems.Thm_StratifyMarkets_DoubleAuction_theorem_4_2

set_option autoImplicit false

-- Solutions.StratifyMarketsParticipation
section
open MeasureTheory Set StratifyMarkets.DoubleAuction

namespace StratifyMarkets.Participation

def eligible {k : ℕ} (s : Set ℝ) [DecidablePred (· ∈ s)] (x : Fin k → ℝ) :=
  Finset.univ.filter (fun i => x i ∈ s)

theorem count_measurable {k : ℕ} (s : Set ℝ) [DecidablePred (· ∈ s)] (hs : MeasurableSet s) :
    Measurable (fun x : Fin k → ℝ => ((eligible s x).card : ℝ)) := by
  have h (x : Fin k → ℝ) : ((eligible s x).card : ℝ) = ∑ i, s.indicator (fun _ => (1:ℝ)) (x i) := by
    simp only [Set.indicator,eligible,Finset.sum_boole]
  simp_rw [h]
  exact Finset.measurable_sum _ fun i _ => (measurable_const.indicator hs).comp (measurable_pi_apply i)

theorem count_median_bounds {k : ℕ} (μ : Fin k → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (s : Set ℝ) [DecidablePred (· ∈ s)] (hs : MeasurableSet s) :
    (1/2 : ENNReal) ≤ Measure.pi μ {x | (∑ i, (μ i s).toReal) - 1 < ((eligible s x).card : ℝ)} ∧
    (1/2 : ENNReal) ≤ Measure.pi μ {x | ((eligible s x).card : ℝ) < (∑ i, (μ i s).toReal) + 1} := by
  classical
  let f := fun x => s.indicator (fun _ : ℝ => (1:ℝ)) x
  have hf : Measurable f := measurable_const.indicator hs
  have hber (i : Fin k) : ∀ᵐ x ∂Measure.pi μ, f (x i) = 0 ∨ f (x i) = 1 := by
    apply Filter.Eventually.of_forall
    intro x
    by_cases h : x i ∈ s <;> simp [f, Set.indicator, h]
  have hpi := ProbabilityTheory.iIndepFun_pi (μ := μ) (X := fun _ => f) (fun _ => hf.aemeasurable)
  have htail := (theorem_4_2 (Measure.pi μ) k (fun i x => f (x i))
    (fun i => hf.comp (measurable_pi_apply i)) hber hpi).2
  have sum_eq (x : Fin k → ℝ) : ∑ i, f (x i) = ((eligible s x).card : ℝ) := by
    simp only [f,Set.indicator,eligible,Finset.sum_boole]
  have hint (i : Fin k) : Integrable (fun x : Fin k → ℝ => f (x i)) (Measure.pi μ) :=
    ((measurePreserving_eval μ i).integrable_comp hf.aestronglyMeasurable).mpr
      ((integrable_const (1:ℝ)).indicator hs)
  have eint (i : Fin k) : (∫ x, f (x i) ∂Measure.pi μ) = (μ i s).toReal := by
    have eq := (measurePreserving_eval μ i).map_eq
    calc
      _ = ∫ y, f y ∂(Measure.pi μ).map (Function.eval i) :=
        (integral_map (measurable_pi_apply i).aemeasurable hf.aestronglyMeasurable).symm
      _ = _ := by rw [eq]; simp [f, integral_indicator hs, measureReal_def]
  rw [integral_finsetSum _ (fun i _ => hint i)] at htail
  simpa only [eint,sum_eq] using htail

theorem gains_integrable_sets {n m : ℕ} (I : DAInstance n m) (A B : Set ℝ)
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Integrable (fun x => worstRationedGains (eligible A x.1) (eligible B x.2) x.1 x.2) I.law := by
  classical
  let : ∀ i, IsProbabilityMeasure (I.μB i) := I.isProb_B
  let : ∀ j, IsProbabilityMeasure (I.μS j) := I.isProb_S
  let : IsProbabilityMeasure I.law := by unfold DAInstance.law; infer_instance
  let mask := fun (x : (Fin n → ℝ) × (Fin m → ℝ)) =>
    ((fun i => decide (x.1 i ∈ A)),(fun j => decide (x.2 j ∈ B)))
  have hmask : Measurable mask := by
    apply Measurable.prodMk
    · apply measurable_pi_iff.mpr
      intro i
      apply measurable_to_bool
      simpa [Set.preimage] using ((measurable_pi_apply i).comp measurable_fst) hA
    · apply measurable_pi_iff.mpr
      intro j
      apply measurable_to_bool
      simpa [Set.preimage] using ((measurable_pi_apply j).comp measurable_snd) hB
  let g := fun z : ((Fin n → ℝ) × (Fin m → ℝ)) × ((Fin n → Bool) × (Fin m → Bool)) =>
    worstRationedGains (Finset.univ.filter (fun i => z.2.1 i)) (Finset.univ.filter (fun j => z.2.2 j))
      z.1.1 z.1.2
  have hg : Measurable g := by
    apply measurable_from_prod_countable_left
    intro masks
    let bs := Finset.univ.filter (fun i => masks.1 i)
    let ss := Finset.univ.filter (fun j => masks.2 j)
    let opts := bs.powersetCard (min bs.card ss.card) ×ˢ ss.powersetCard (min bs.card ss.card)
    have hn : opts.Nonempty := (Finset.powersetCard_nonempty.mpr (min_le_left _ _)).product
      (Finset.powersetCard_nonempty.mpr (min_le_right _ _))
    let f := fun (T : Finset (Fin n) × Finset (Fin m)) (x : (Fin n → ℝ) × (Fin m → ℝ)) =>
      ∑ i ∈ T.1, x.1 i - ∑ j ∈ T.2, x.2 j
    have hfn (T) : Measurable (f T) := by
      apply Measurable.sub
      · exact Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).comp measurable_fst
      · exact Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).comp measurable_snd
    have heq : (fun x => g (x,masks)) = opts.inf' hn f := by
      funext x
      exact (Finset.inf'_apply hn f x).symm
    rw [heq]
    exact Finset.measurable_sup' (α := ℝᵒᵈ) hn fun T _ => hfn T
  have HM : Measurable (fun x : (Fin n → ℝ) × (Fin m → ℝ) => worstRationedGains (eligible A x.1) (eligible B x.2) x.1 x.2) := by
    simpa only [Function.comp_def, id_eq, g, mask, eligible, decide_eq_true_eq] using
      hg.comp (measurable_id.prodMk hmask)
  have buyer_support (i : Fin n) : ∀ᵐ x ∂I.law, x.1 i ∈ Icc (0 : ℝ) 1 :=
    (measurePreserving_fst (μ := Measure.pi I.μB) (ν := Measure.pi I.μS)).quasiMeasurePreserving.ae
      ((measurePreserving_eval I.μB i).quasiMeasurePreserving.ae
        ((mem_ae_iff_prob_eq_one measurableSet_Icc).mpr (I.support_B i)))
  have seller_support (j : Fin m) : ∀ᵐ x ∂I.law, x.2 j ∈ Icc (0 : ℝ) 1 :=
    (measurePreserving_snd (μ := Measure.pi I.μB) (ν := Measure.pi I.μS)).quasiMeasurePreserving.ae
      ((measurePreserving_eval I.μS j).quasiMeasurePreserving.ae
        ((mem_ae_iff_prob_eq_one measurableSet_Icc).mpr (I.support_S j)))
  apply Integrable.of_bound HM.aestronglyMeasurable ((n:ℝ)+m)
  filter_upwards [ae_all_iff.mpr buyer_support, ae_all_iff.mpr seller_support] with x hx hy
  unfold worstRationedGains
  let bs := eligible A x.1
  let ss := eligible B x.2
  have nonempty : ((bs.powersetCard (min bs.card ss.card)) ×ˢ ss.powersetCard (min bs.card ss.card)).Nonempty :=
    (Finset.powersetCard_nonempty.mpr (min_le_left _ _)).product (Finset.powersetCard_nonempty.mpr (min_le_right _ _))
  obtain ⟨pair,_,h⟩ := Finset.exists_mem_eq_inf' nonempty (fun T => ∑ i ∈ T.1, x.1 i - ∑ j ∈ T.2, x.2 j)
  change ‖Finset.inf' _ nonempty (fun T => ∑ i ∈ T.1, x.1 i - ∑ j ∈ T.2, x.2 j)‖ ≤ _
  rw [h,Real.norm_eq_abs,abs_le]
  have h1 : (∑ i ∈ pair.1, x.1 i) ≤ n := by
    calc _ ≤ ∑ _i ∈ pair.1, (1:ℝ) := Finset.sum_le_sum fun i _ => (hx i).2
         _ ≤ _ := by simpa using (show (pair.1.card:ℝ) ≤ n by exact_mod_cast (show pair.1.card ≤ n by simpa using Finset.card_le_univ pair.1))
  have h2 : (∑ j ∈ pair.2, x.2 j) ≤ m := by
    calc _ ≤ ∑ _j ∈ pair.2, (1:ℝ) := Finset.sum_le_sum fun j _ => (hy j).2
         _ ≤ _ := by simpa using (show (pair.2.card:ℝ) ≤ m by exact_mod_cast (show pair.2.card ≤ m by simpa using Finset.card_le_univ pair.2))
  have h3 := Finset.sum_nonneg (s := pair.1) (fun i _ => (hx i).1)
  have h4 := Finset.sum_nonneg (s := pair.2) (fun j _ => (hy j).1)
  constructor <;> linarith

theorem gains_integrable {n m : ℕ} (I : DAInstance n m) (q : ℝ) :
    Integrable (fun x => worstRationedGains (eligible (Ici q) x.1) (eligible (Iic q) x.2) x.1 x.2) I.law :=
  gains_integrable_sets I _ _ measurableSet_Ici measurableSet_Iic

theorem nonneg_gains {n m : ℕ} (v : Fin n → ℝ) (c : Fin m → ℝ) (q : ℝ) :
    0 ≤ worstRationedGains (eligible (Ici q) v) (eligible (Iic q) c) v c := by
  apply Finset.le_inf'
  intro T hT
  obtain ⟨hB,hS⟩ := Finset.mem_product.mp hT
  obtain ⟨inB,cB⟩ := Finset.mem_powersetCard.mp hB
  obtain ⟨inS,cS⟩ := Finset.mem_powersetCard.mp hS
  have sc : (∑ j ∈ T.2, c j) ≤ ∑ _j ∈ T.2, q := Finset.sum_le_sum fun j hj => (Finset.mem_filter.mp (inS hj)).2
  have vb : (∑ _i ∈ T.1, q) ≤ ∑ i ∈ T.1, v i := Finset.sum_le_sum fun i hi => (Finset.mem_filter.mp (inB hi)).2
  exact sub_nonneg.mpr (sc.trans ((by simp [cB,cS] : (∑ _j ∈ T.2, q) ≤ ∑ _i ∈ T.1, q).trans vb))

/-- The leave-one-out comparison behind (4.10) whenever expected demand
is at least one unit below expected supply. Each side is an independent
heterogeneous family; removing one eligible-side coordinate is allowed. -/
theorem extra_participant_wins {k l : ℕ}
    (μ : Fin k → Measure ℝ) (ν : Fin l → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ j, IsProbabilityMeasure (ν j)]
    (s t : Set ℝ) [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)]
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (gap : (∑ i, (μ i s).toReal) + 2 ≤ ∑ j, (ν j t).toReal) :
    (1/4 : ℝ) ≤ (((Measure.pi μ).prod (Measure.pi ν))
      {x | (eligible s x.1).card < (eligible t x.2).card}).toReal := by
  let B := {x : Fin k → ℝ | ((eligible s x).card : ℝ) < (∑ i, (μ i s).toReal) + 1}
  let S := {y : Fin l → ℝ | (∑ j, (ν j t).toReal) - 1 < ((eligible t y).card : ℝ)}
  have b := ENNReal.toReal_mono (measure_ne_top _ _) (count_median_bounds μ s hs).2
  have c := ENNReal.toReal_mono (measure_ne_top _ _) (count_median_bounds ν t ht).1
  change (1/2 : ENNReal).toReal ≤ ((Measure.pi μ) B).toReal at b
  change (1/2 : ENNReal).toReal ≤ ((Measure.pi ν) S).toReal at c
  norm_num at b c
  have subset : B ×ˢ S ⊆ {x | (eligible s x.1).card < (eligible t x.2).card} := by
    intro x hx
    obtain ⟨h1,h2⟩ := hx
    change ((eligible s x.1).card : ℝ) < (∑ i, (μ i s).toReal) + 1 at h1
    change (∑ j, (ν j t).toReal) - 1 < ((eligible t x.2).card : ℝ) at h2
    exact_mod_cast (show ((eligible s x.1).card : ℝ) < ((eligible t x.2).card : ℝ) by linarith)
  have h := measureReal_mono (μ := (Measure.pi μ).prod (Measure.pi ν)) subset
  apply le_trans _ h
  rw [measureReal_def, Measure.prod_prod, ENNReal.toReal_mul]
  nlinarith [mul_nonneg (sub_nonneg.mpr b) (sub_nonneg.mpr c)]

end StratifyMarkets.Participation
end

-- Solutions.StratifyMarketsBalancedLaw
section
open MeasureTheory Set
namespace StratifyMarkets.DoubleAuction

/-- Equation (4.1) defines the same expected count for all balanced prices,
even when some marginal CDFs are constant on a nonempty interval. -/
theorem balanced_count_unique {n m : ℕ} (I : DAInstance n m) {p q : ℝ}
    (hp : I.IsBalancedPrice p) (hq : I.IsBalancedPrice q) : I.expB p = I.expB q := by
  have hB : Antitone I.expB := by
    intro x y h
    apply Finset.sum_le_sum
    intro i _
    let := I.isProb_B i
    exact measureReal_mono (Ici_subset_Ici.mpr h)
  have hS : Monotone I.expS := by
    intro x y h
    apply Finset.sum_le_sum
    intro j _
    let := I.isProb_S j
    exact measureReal_mono (Iic_subset_Iic.mpr h)
  rcases le_total p q with h | h
  · exact le_antisymm (hp.2.le.trans ((hS h).trans hq.2.ge)) (hB h)
  · exact le_antisymm (hB h) (hq.2.le.trans ((hS h).trans hp.2.ge))

/-- A global price and the same price in the whole unit interval trade with
identical eligible sets almost surely under the product law. -/
theorem whole_submarket_eq {n m : ℕ} (I : DAInstance n m) (p : ℝ) :
    I.worstRationedIn 0 p 1 = I.worstRationed p := by
  let : ∀ i, IsProbabilityMeasure (I.μB i) := I.isProb_B
  let : ∀ j, IsProbabilityMeasure (I.μS j) := I.isProb_S
  have B (i : Fin n) : ∀ᵐ x ∂I.law, x.1 i ∈ Icc (0 : ℝ) 1 := by
    have h : Icc (0 : ℝ) 1 ∈ ae (I.μB i) :=
      (mem_ae_iff_prob_eq_one measurableSet_Icc).mpr (I.support_B i)
    exact (measurePreserving_fst (μ := Measure.pi I.μB) (ν := Measure.pi I.μS)).quasiMeasurePreserving.ae
      ((measurePreserving_eval I.μB i).quasiMeasurePreserving.ae h)
  have S (j : Fin m) : ∀ᵐ x ∂I.law, x.2 j ∈ Icc (0 : ℝ) 1 := by
    have h : Icc (0 : ℝ) 1 ∈ ae (I.μS j) :=
      (mem_ae_iff_prob_eq_one measurableSet_Icc).mpr (I.support_S j)
    exact (measurePreserving_snd (μ := Measure.pi I.μB) (ν := Measure.pi I.μS)).quasiMeasurePreserving.ae
      ((measurePreserving_eval I.μS j).quasiMeasurePreserving.ae h)
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr B, ae_all_iff.mpr S] with x hx hy
  congr 1
  · ext i
    simp [Finset.mem_filter, (hx i).2]
  · ext j
    simp [Finset.mem_filter, (hy j).1]

/-- Every summand of the efficient matching is positive because the list of
seller costs increases while the list of buyer values decreases. -/
theorem realizedFB_nonnegative {n m : ℕ} (v : Fin n → ℝ) (c : Fin m → ℝ) :
    0 ≤ realizedFB v c := by
  apply Finset.sum_nonneg
  intro i hi
  have hit : i < tau v c := Finset.mem_range.mp hi
  obtain ⟨j, hj, hij⟩ := Finset.lt_sup_iff.mp hit
  obtain ⟨jr, hjgain⟩ := Finset.mem_filter.mp hj
  have jmin := Finset.mem_range.mp jr
  change i < j+1 at hij
  have jv : j < (valuesDesc v).length := by simpa [valuesDesc] using (lt_of_lt_of_le jmin (min_le_left n m))
  have js : j < (costsAsc c).length := by simpa [costsAsc] using (lt_of_lt_of_le jmin (min_le_right n m))
  have ig : i ≤ j := Nat.le_of_lt_succ hij
  change (costsAsc c).getD j 0 < (valuesDesc v).getD j 0 at hjgain
  apply sub_nonneg.mpr
  rcases eq_or_lt_of_le ig with rfl | hl
  · exact hjgain.le
  have cv := List.pairwise_iff_getElem.mp (List.pairwise_mergeSort' (· ≥ ·) (List.ofFn v))
    i j (ig.trans_lt jv) jv hl
  have cc := List.pairwise_iff_getElem.mp (List.pairwise_mergeSort' (· ≤ ·) (List.ofFn c))
    i j (ig.trans_lt js) js hl
  simp only [List.getD_eq_getElem _ _ jv, List.getD_eq_getElem _ _ js] at hjgain
  rw [List.getD_eq_getElem _ _ (ig.trans_lt js), List.getD_eq_getElem _ _ (ig.trans_lt jv)]
  exact cc.trans (hjgain.le.trans cv)

end StratifyMarkets.DoubleAuction
end

-- Solutions.StratifyMarketsFirstBest
section
open MeasureTheory Set
namespace StratifyMarkets.DoubleAuction

private theorem sorted_coordinate_measurable {k : ℕ} (r : ℝ → ℝ → Bool)
    (hr : ∀ i j : Fin k, Measurable fun v : Fin k → ℝ => r (v i) (v j))
    (t : ℕ) :
    Measurable fun v : Fin k → ℝ => ((List.ofFn v).mergeSort r).getD t 0 := by
  let table := fun (v : Fin k → ℝ) (i j : Fin k) => r (v i) (v j)
  have htable : Measurable table :=
    measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => hr i j
  let indices := List.ofFn (id : Fin k → Fin k)
  let entry := fun (z : (Fin k → ℝ) × (Fin k → Fin k → Bool)) =>
    (((indices.mergeSort z.2).map z.1)[t]?).getD 0
  have hentry : Measurable entry := by
    apply measurable_from_prod_countable_left
    intro order
    simp only [entry, List.getElem?_map]
    cases (indices.mergeSort order)[t]? with
    | none => exact measurable_const
    | some i => exact measurable_pi_apply i
  have hmap (v : Fin k → ℝ) :
      (indices.mergeSort (table v)).map v = (List.ofFn v).mergeSort r := by
    simpa [indices, List.map_ofFn] using
      (List.map_mergeSort (f := v) (l := indices) (r := table v) (s := r)
        (fun _ _ _ _ => rfl))
  simpa only [Function.comp_def, id_eq, entry, hmap, List.getD_eq_getElem?_getD] using
    hentry.comp (measurable_id.prodMk htable)

theorem measurable_trade_cut {n m : ℕ} (r : ℕ) :
    MeasurableSet {x : (Fin n → ℝ) × (Fin m → ℝ) | r < tau x.1 x.2} := by
  have value (i : ℕ) : Measurable fun v : Fin n → ℝ => (valuesDesc v).getD i 0 :=
    sorted_coordinate_measurable (fun a b => decide (b ≤ a)) (fun a b => measurable_to_bool (by
      simpa [Set.preimage] using
        (measurableSet_le (f := fun v : Fin n → ℝ => v b) (g := fun v => v a)
          (measurable_pi_apply b) (measurable_pi_apply a)))) i
  have cost (i : ℕ) : Measurable fun c : Fin m → ℝ => (costsAsc c).getD i 0 :=
    sorted_coordinate_measurable (fun a b => decide (a ≤ b)) (fun a b => measurable_to_bool (by
      simpa [Set.preimage] using
        (measurableSet_le (f := fun c : Fin m → ℝ => c a) (g := fun c => c b)
          (measurable_pi_apply a) (measurable_pi_apply b)))) i
  let trades := fun i => {x : (Fin n → ℝ) × (Fin m → ℝ) |
    (costsAsc x.2).getD i 0 < (valuesDesc x.1).getD i 0}
  have h : {x : (Fin n → ℝ) × (Fin m → ℝ) | r < tau x.1 x.2} =
      ⋃ i : ℕ, ⋃ (_ : i < min n m ∧ r < i + 1), trades i := by
    ext x
    simp [tau, Finset.lt_sup_iff, trades]
    aesop
  rw [h]
  exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ =>
    measurableSet_lt ((cost i).comp measurable_snd) ((value i).comp measurable_fst)


theorem integrable_first_best {n m : ℕ} (I : DAInstance n m) :
    Integrable (fun x : (Fin n → ℝ) × (Fin m → ℝ) => realizedFB x.1 x.2) I.law := by
  let : ∀ i, IsProbabilityMeasure (I.μB i) := I.isProb_B
  let : ∀ j, IsProbabilityMeasure (I.μS j) := I.isProb_S
  let : IsProbabilityMeasure I.law := by unfold DAInstance.law; infer_instance
  have count (v : Fin n → ℝ) (c : Fin m → ℝ) : tau v c ≤ min n m := by
    apply Finset.sup_le
    intro i hi
    exact Finset.mem_range.mp (Finset.mem_filter.mp hi).1
  have hv (i : ℕ) : Measurable fun v : Fin n → ℝ => (valuesDesc v).getD i 0 :=
    sorted_coordinate_measurable (fun a b => decide (b ≤ a)) (fun a b => measurable_to_bool (by
      simpa [Set.preimage] using (measurableSet_le (f := fun v : Fin n → ℝ => v b)
        (g := fun v => v a) (measurable_pi_apply b) (measurable_pi_apply a)))) i
  have hc (i : ℕ) : Measurable fun c : Fin m → ℝ => (costsAsc c).getD i 0 :=
    sorted_coordinate_measurable (fun a b => decide (a ≤ b)) (fun a b => measurable_to_bool (by
      simpa [Set.preimage] using (measurableSet_le (f := fun c : Fin m → ℝ => c a)
        (g := fun c => c b) (measurable_pi_apply a) (measurable_pi_apply b)))) i
  have hmeas : Measurable (fun x : (Fin n → ℝ) × (Fin m → ℝ) => realizedFB x.1 x.2) := by
    have expand (v : Fin n → ℝ) (c : Fin m → ℝ) :
        realizedFB v c = ∑ i ∈ Finset.range (min n m), if i < tau v c then
          (valuesDesc v).getD i 0 - (costsAsc c).getD i 0 else 0 := by
      rw [← Finset.sum_filter]
      unfold realizedFB
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨fun h => ⟨h.trans_le (count v c), h⟩, fun h => h.2⟩
    simp_rw [expand]
    exact Finset.measurable_sum _ fun i _ => Measurable.ite (measurable_trade_cut i)
      (((hv i).comp measurable_fst).sub ((hc i).comp measurable_snd)) measurable_const
  have B (i : Fin n) : ∀ᵐ x ∂I.law, x.1 i ∈ Icc (0 : ℝ) 1 :=
    (measurePreserving_fst (μ := Measure.pi I.μB) (ν := Measure.pi I.μS)).quasiMeasurePreserving.ae
      ((measurePreserving_eval I.μB i).quasiMeasurePreserving.ae
        ((mem_ae_iff_prob_eq_one measurableSet_Icc).mpr (I.support_B i)))
  have S (j : Fin m) : ∀ᵐ x ∂I.law, x.2 j ∈ Icc (0 : ℝ) 1 :=
    (measurePreserving_snd (μ := Measure.pi I.μB) (ν := Measure.pi I.μS)).quasiMeasurePreserving.ae
      ((measurePreserving_eval I.μS j).quasiMeasurePreserving.ae
        ((mem_ae_iff_prob_eq_one measurableSet_Icc).mpr (I.support_S j)))
  apply Integrable.of_bound hmeas.aestronglyMeasurable (min n m : ℕ)
  filter_upwards [ae_all_iff.mpr B, ae_all_iff.mpr S] with x hx hy
  rw [Real.norm_eq_abs, abs_of_nonneg (realizedFB_nonnegative _ _)]
  have entry {k : ℕ} (w : Fin k → ℝ) (r : ℝ → ℝ → Bool) (h : ∀ j, w j ∈ Icc (0 : ℝ) 1)
      (i : ℕ) (hi : i < k) : ((List.ofFn w).mergeSort r).getD i 0 ∈ Icc (0 : ℝ) 1 := by
    have hil : i < ((List.ofFn w).mergeSort r).length := by simpa using hi
    rw [List.getD_eq_getElem _ _ hil]
    have mem := List.getElem_mem (l := (List.ofFn w).mergeSort r) hil
    have orig := List.mem_mergeSort.mp mem
    obtain ⟨j,hj⟩ := (List.mem_ofFn' _ _).mp orig
    rw [← hj]
    exact h j
  calc
    realizedFB x.1 x.2 ≤ ∑ _i ∈ Finset.range (tau x.1 x.2), (1:ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      have h := (Finset.mem_range.mp hi).trans_le (count x.1 x.2)
      have hb := (entry x.1 (fun a b => decide (b ≤ a)) hx i (h.trans_le (min_le_left _ _))).2
      have hs := (entry x.2 (fun a b => decide (a ≤ b)) hy i (h.trans_le (min_le_right _ _))).1
      change (valuesDesc x.1).getD i 0 ≤ 1 at hb
      change 0 ≤ (costsAsc x.2).getD i 0 at hs
      linarith
    _ ≤ _ := by simpa using (show (tau x.1 x.2 : ℝ) ≤ (min n m : ℕ) by exact_mod_cast count x.1 x.2)

theorem sorted_positive_sum {k : ℕ} (w : Fin k → ℝ) (r : ℝ → ℝ → Bool)
    (φ : ℝ → ℝ) (hφ : ∀ a, 0 ≤ φ a) {t : ℕ} (ht : t ≤ k) :
    (∑ i ∈ Finset.range t, φ (((List.ofFn w).mergeSort r).getD i 0)) ≤ ∑ i, φ (w i) := by
  let l := (List.ofFn w).mergeSort r
  have len : l.length = k := by simp [l]
  have hperm := (List.mergeSort_perm (List.ofFn w) r).map φ
  calc
    _ ≤ ∑ i ∈ Finset.range l.length, φ (l.getD i 0) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (ht.trans_eq len.symm)) (fun i _ _ => hφ _)
    _ = (l.map φ).sum := by
      rw [← Fin.sum_univ_eq_sum_range]
      rw [← List.sum_ofFn]
      congr 1
      rw [← List.ofFn_getElem_eq_map]
      apply congrArg List.ofFn
      funext i
      rw [List.getD_eq_getElem _ _ i.isLt]
    _ = ((List.ofFn w).map φ).sum := hperm.sum_eq
    _ = ∑ i, φ (w i) := by simp [List.map_ofFn, List.sum_ofFn]

theorem realized_surplus {n m : ℕ} (v : Fin n → ℝ) (c : Fin m → ℝ) (t : ℝ) :
    realizedFB v c ≤ ∑ i, max (v i - t) 0 + ∑ j, max (t - c j) 0 := by
  have H : tau v c ≤ min n m := by
    apply Finset.sup_le
    intro i hi
    exact Finset.mem_range.mp (Finset.mem_filter.mp hi).1
  calc
    _ ≤ ∑ i ∈ Finset.range (tau v c), (max ((valuesDesc v).getD i 0 - t) 0 + max (t - (costsAsc c).getD i 0) 0) := by
      apply Finset.sum_le_sum
      intro i _
      linarith only [le_max_left ((valuesDesc v).getD i 0 - t) 0, le_max_left (t - (costsAsc c).getD i 0) 0]
    _ ≤ _ := by
      rw [Finset.sum_add_distrib]
      exact add_le_add (sorted_positive_sum v (fun a b => decide (b ≤ a)) (fun x => max (x-t) 0)
        (fun _ => le_max_right _ _) (H.trans (min_le_left _ _)))
        (sorted_positive_sum c (fun a b => decide (a ≤ b)) (fun x => max (t-x) 0)
          (fun _ => le_max_right _ _) (H.trans (min_le_right _ _)))

end StratifyMarkets.DoubleAuction
end

-- Solutions.Sol_StratifyMarkets_DoubleAuction_lemma_4_4
section
open MeasureTheory Set StratifyMarkets.DoubleAuction StratifyMarkets.Participation

private theorem allocation {n m : ℕ} (v : Fin n → ℝ) (c : Fin m → ℝ) (q : ℝ) :
    (if (eligible (Ici q) v).card ≤ (eligible (Iic q) c).card then ∑ i, max (v i-q) 0 else 0) ≤
      worstRationedGains (eligible (Ici q) v) (eligible (Iic q) c) v c ∧
    (if (eligible (Iic q) c).card ≤ (eligible (Ici q) v).card then ∑ j, max (q-c j) 0 else 0) ≤
      worstRationedGains (eligible (Ici q) v) (eligible (Iic q) c) v c := by
  classical
  let B := eligible (Ici q) v
  let S := eligible (Iic q) c
  have vb : (∑ i, max (v i-q) 0) = ∑ i ∈ B, (v i-q) := by
    dsimp only [B,eligible]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : q ≤ v i
    · simp [h,max_eq_left (sub_nonneg.mpr h)]
    · simp [h,max_eq_right (sub_nonpos.mpr (le_of_not_ge h))]
  have sc : (∑ j, max (q-c j) 0) = ∑ j ∈ S, (q-c j) := by
    dsimp only [S,eligible]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : c j ≤ q
    · simp [h,max_eq_left (sub_nonneg.mpr h)]
    · simp [h,max_eq_right (sub_nonpos.mpr (le_of_not_ge h))]
  have bound (T : Finset (Fin n) × Finset (Fin m)) (ib : T.1 ⊆ B) (is : T.2 ⊆ S)
      (size : T.1.card = T.2.card) :
      (∑ i ∈ T.1, (v i-q)) ≤ (∑ i ∈ T.1, v i) - ∑ j ∈ T.2, c j ∧
      (∑ j ∈ T.2, (q-c j)) ≤ (∑ i ∈ T.1, v i) - ∑ j ∈ T.2, c j := by
    have vb := Finset.sum_nonneg (s := T.1) fun i hi => sub_nonneg.mpr
      (show q ≤ v i from (Finset.mem_filter.mp (ib hi)).2)
    have sc := Finset.sum_nonneg (s := T.2) fun j hj => sub_nonneg.mpr
      (show c j ≤ q from (Finset.mem_filter.mp (is hj)).2)
    simp only [Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul,size] at *
    constructor <;> linarith
  constructor
  · split_ifs with h
    · rw [vb]
      apply Finset.le_inf'
      intro T hT
      obtain ⟨hb,hs⟩ := Finset.mem_product.mp hT
      obtain ⟨ib,cb⟩ := Finset.mem_powersetCard.mp hb
      obtain ⟨is,cs⟩ := Finset.mem_powersetCard.mp hs
      have e : T.1 = B := Finset.eq_of_subset_of_card_le ib (by simpa only [min_eq_left h] using cb.ge)
      exact e ▸ (bound T ib is (cb.trans cs.symm)).1
    · exact nonneg_gains _ _ _
  · split_ifs with h
    · rw [sc]
      apply Finset.le_inf'
      intro T hT
      obtain ⟨hb,hs⟩ := Finset.mem_product.mp hT
      obtain ⟨ib,cb⟩ := Finset.mem_powersetCard.mp hb
      obtain ⟨is,cs⟩ := Finset.mem_powersetCard.mp hs
      have e : T.2 = S := Finset.eq_of_subset_of_card_le is (by simpa only [min_eq_right h] using cs.ge)
      exact e ▸ (bound T ib is (cb.trans cs.symm)).2
    · exact nonneg_gains _ _ _

private theorem weighted_side {n m : ℕ} (μ : Fin n → Measure ℝ) (ν : Fin m → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ j, IsProbabilityMeasure (ν j)]
    (s t : Set ℝ) [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)] (hs : MeasurableSet s) (ht : MeasurableSet t)
    (f : ℝ → ℝ) (hf : ∀ i, Integrable f (μ i)) (hm : Measurable f) (pos : ∀ y, 0 ≤ f y)
    (outside : ∀ y, y ∉ s → f y = 0)
    (gap : (∑ i, (μ i s).toReal)+2 ≤ ∑ j, (ν j t).toReal) :
    1/4 * (∑ i, ∫ z, f z ∂μ i) ≤
      ∫ x, (if (eligible s x.1).card ≤ (eligible t x.2).card then ∑ i, f (x.1 i) else 0)
        ∂((Measure.pi μ).prod (Measure.pi ν)) := by
  classical
  cases n with
  | zero => simp
  | succ n =>
    let P := (Measure.pi μ).prod (Measure.pi ν)
    let E := {x : (Fin (n+1) → ℝ) × (Fin m → ℝ) | (eligible s x.1).card ≤ (eligible t x.2).card}
    have he : MeasurableSet E := by
      have H := measurableSet_le ((count_measurable (k := n+1) s hs).comp measurable_fst) ((count_measurable (k := m) t ht).comp measurable_snd)
      simpa [E,Function.comp_def] using H
    let z := fun (i : Fin (n+1)) (x : (Fin (n+1) → ℝ) × (Fin m → ℝ)) => E.indicator (fun y => f (y.1 i)) x
    have hz (i) : Integrable (z i) P := by
      have H : MeasurePreserving (fun x : (Fin (n+1) → ℝ) × (Fin m → ℝ) => x.1 i) P (μ i) :=
        (measurePreserving_eval μ i).comp (measurePreserving_fst (μ := Measure.pi μ) (ν := Measure.pi ν))
      exact ((H.integrable_comp hm.aestronglyMeasurable).mpr (hf i)).indicator he
    have part (i : Fin (n+1)) : 1/4 * (∫ y, f y ∂μ i) ≤ ∫ x, z i x ∂P := by
      let rest := fun j => μ (i.succAbove j)
      let R := (Measure.pi rest).prod (Measure.pi ν)
      let A := {w : (Fin n → ℝ) × (Fin m → ℝ) | (eligible s w.1).card < (eligible t w.2).card}
      have hA : MeasurableSet A := by
        have H := measurableSet_lt ((count_measurable (k := n) s hs).comp measurable_fst) ((count_measurable (k := m) t ht).comp measurable_snd)
        simpa [A,Function.comp_def] using H
      have hg : (∑ j, (rest j s).toReal)+2 ≤ ∑ j, (ν j t).toReal := by
        rw [Fin.sum_univ_succAbove _ i] at gap
        dsimp [rest]; linarith [show 0 ≤ (μ i s).toReal from ENNReal.toReal_nonneg]
      have quarter : 1/4 ≤ (R A).toReal := extra_participant_wins rest ν s t hs ht hg
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i
      let lift := e.prodCongr (MeasurableEquiv.refl (Fin m → ℝ))
      let iso := lift.trans MeasurableEquiv.prodAssoc
      have hlift : MeasurePreserving lift P (((μ i).prod (Measure.pi rest)).prod (Measure.pi ν)) := by
        refine ⟨lift.measurable, ?_⟩
        have heq := (measurePreserving_piFinSuccAbove μ i).map_eq
        change (Measure.map (Prod.map e id) ((Measure.pi μ).prod (Measure.pi ν))) = _
        rw [← Measure.map_prod_map _ _ e.measurable measurable_id, Measure.map_id, heq]
      have hi : MeasurePreserving iso P ((μ i).prod R) := (measurePreserving_prodAssoc _ _ _).comp hlift
      let Φ := fun y : ℝ × ((Fin n → ℝ) × (Fin m → ℝ)) => f y.1 * A.indicator (fun _ => (1:ℝ)) y.2
      have hid : (fun x => Φ (iso x)) = z i := by
        funext x
        change f (x.1 i) * A.indicator (fun _ => (1:ℝ)) ((fun j => x.1 (i.succAbove j)),x.2) = E.indicator _ x
        by_cases b : x.1 i ∈ s
        · have split : (eligible s x.1).card = 1 + (eligible s (fun j => x.1 (i.succAbove j))).card := by
            unfold eligible
            rw [Finset.card_filter, Fin.sum_univ_succAbove _ i, Finset.card_filter]
            simp only [b, if_true]
          by_cases ht' : (eligible s (fun j => x.1 (i.succAbove j))).card < (eligible t x.2).card
          · have ha : ((fun j => x.1 (i.succAbove j)),x.2) ∈ A := ht'
            have he' : x ∈ E := by
              change (eligible s x.1).card ≤ (eligible t x.2).card
              omega
            rw [Set.indicator_of_mem ha, Set.indicator_of_mem he',mul_one]
          · have ha : ((fun j => x.1 (i.succAbove j)),x.2) ∉ A := ht'
            have he' : x ∉ E := by
              change ¬(eligible s x.1).card ≤ (eligible t x.2).card
              omega
            rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem he',mul_zero]
        · simp [Set.indicator,outside _ b]
      have val : (∫ x, z i x ∂P) = (∫ y, f y ∂μ i) * (R A).toReal := by
        rw [← hid, hi.integral_comp' Φ]
        dsimp [Φ]
        rw [integral_prod_mul, integral_indicator hA, setIntegral_one_eq_measureReal, measureReal_def]
      rw [val,mul_comm (1/4 : ℝ)]
      exact mul_le_mul_of_nonneg_left quarter (integral_nonneg pos)
    have total := Finset.sum_le_sum (s := Finset.univ) fun i _ => part i
    rw [← Finset.mul_sum, ← integral_finsetSum _ (fun i _ => hz i)] at total
    apply total.trans_eq
    apply integral_congr_ae
    filter_upwards with x
    by_cases h : x ∈ E
    · change (eligible s x.1).card ≤ (eligible t x.2).card at h
      simp [z,E,Set.indicator,h]
    · change ¬(eligible s x.1).card ≤ (eligible t x.2).card at h
      simp [z,E,Set.indicator,h]

theorem solution {n m : ℕ} (I : DAInstance n m) (pt pbar plow : ℝ)
    (_hpt : I.IsBalancedPrice pt) (_hlam : 4 ≤ I.expB pt)
    (hpbar : I.IsExcessSupplyPrice pbar) (hplow : I.IsExcessDemandPrice plow) :
    1 / 4 * I.buyerSurplus pbar ≤ I.worstRationed pbar ∧
    1 / 4 * I.sellerSurplus plow ≤ I.worstRationed plow := by
  let : ∀ i, IsProbabilityMeasure (I.μB i) := I.isProb_B
  let : ∀ j, IsProbabilityMeasure (I.μS j) := I.isProb_S
  have hint {μ : Measure ℝ} [IsProbabilityMeasure μ] (supp : μ (Icc 0 1)=1) (f : ℝ → ℝ) (cf : Continuous f) :
      Integrable f μ := by
    obtain ⟨C,hC⟩ := (isCompact_Icc (a := (0:ℝ)) (b := (1:ℝ))).exists_bound_of_continuousOn cf.continuousOn
    apply Integrable.of_bound cf.measurable.aestronglyMeasurable C
    filter_upwards [(mem_ae_iff_prob_eq_one measurableSet_Icc).mpr supp] with x hx
    exact hC x hx
  have ib (i) : Integrable (fun x : ℝ => max (x-pbar) 0) (I.μB i) := hint (I.support_B i) _ (by fun_prop)
  have is (j) : Integrable (fun x : ℝ => max (plow-x) 0) (I.μS j) := hint (I.support_S j) _ (by fun_prop)
  have int_alloc {a b : ℕ} (μ : Fin a → Measure ℝ) (ν : Fin b → Measure ℝ)
      [∀ i, IsProbabilityMeasure (μ i)] [∀ j, IsProbabilityMeasure (ν j)]
      (s t : Set ℝ) [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)] (hs : MeasurableSet s) (ht : MeasurableSet t)
      (f : ℝ → ℝ) (hm : Measurable f) (hi : ∀ i, Integrable f (μ i)) :
      Integrable (fun x => if (eligible s x.1).card ≤ (eligible t x.2).card then ∑ i, f (x.1 i) else 0)
        ((Measure.pi μ).prod (Measure.pi ν)) := by
    have mset := measurableSet_le ((count_measurable (k := a) s hs).comp measurable_fst) ((count_measurable (k := b) t ht).comp measurable_snd)
    have he : MeasurableSet {x : (Fin a → ℝ) × (Fin b → ℝ) | (eligible s x.1).card ≤ (eligible t x.2).card} := by
      simpa [Function.comp_def] using mset
    have H := integrable_finsetSum (s := Finset.univ) fun i _ =>
      (((measurePreserving_eval μ i).comp (measurePreserving_fst (μ := Measure.pi μ) (ν := Measure.pi ν))).integrable_comp
        hm.aestronglyMeasurable).mpr (hi i)
    apply (H.indicator he).congr
    filter_upwards with x
    simp [Set.indicator]
  constructor
  · have W := weighted_side I.μB I.μS (Ici pbar) (Iic pbar) measurableSet_Ici measurableSet_Iic
      (fun x => max (x-pbar) 0) ib (by fun_prop) (fun _ => le_max_right _ _)
      (fun x hx => max_eq_right (sub_nonpos.mpr (le_of_not_ge hx))) (by change I.expB pbar + 2 ≤ I.expS pbar; linarith only [hpbar.2])
    exact W.trans (integral_mono (int_alloc I.μB I.μS _ _ measurableSet_Ici measurableSet_Iic _ (by fun_prop) ib)
      (gains_integrable I pbar) (fun x => (allocation x.1 x.2 pbar).1))
  · have W := weighted_side I.μS I.μB (Iic plow) (Ici plow) measurableSet_Iic measurableSet_Ici
      (fun x => max (plow-x) 0) is (by fun_prop) (fun _ => le_max_right _ _)
      (fun x hx => max_eq_right (sub_nonpos.mpr (le_of_not_ge hx))) (by change I.expS plow + 2 ≤ I.expB plow; linarith only [hplow.2])
    let f := fun x : (Fin m → ℝ) × (Fin n → ℝ) =>
      if (eligible (Iic plow) x.1).card ≤ (eligible (Ici plow) x.2).card then ∑ j, max (plow-x.1 j) 0 else 0
    have sw : MeasurePreserving (MeasurableEquiv.prodComm : _ ≃ᵐ _) I.law ((Measure.pi I.μS).prod (Measure.pi I.μB)) :=
      Measure.measurePreserving_swap
    have hi := int_alloc I.μS I.μB (Iic plow) (Ici plow) measurableSet_Iic measurableSet_Ici
      (fun x => max (plow-x) 0) (by fun_prop) is
    have hsw : Integrable (fun x => f (Prod.swap x)) I.law :=
      (sw.integrable_comp hi.aestronglyMeasurable).mpr hi
    change 1/4 * I.sellerSurplus plow ≤ ∫ x, f x ∂((Measure.pi I.μS).prod (Measure.pi I.μB)) at W
    rw [← sw.integral_comp' f] at W
    exact W.trans (integral_mono hsw (gains_integrable I plow) (fun x => (allocation x.1 x.2 plow).2))
end
