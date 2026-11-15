-- Prove2me | solution 1 for StratifyMarkets.DoubleAuction.lemma_4_10
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T06:50:19.960205+00:00
-- url     : https://prove2.me/submissions/1d681d8c-5d3c-405c-9089-8ad7442675e0

import Definitions.Def_StratifyMarkets_DoubleAuction_Prices
import Definitions.Def_StratifyMarkets_DoubleAuction_WorstRationed
import Mathlib
import Theorems.Thm_StratifyMarkets_DoubleAuction_lemma_4_8
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

-- Solutions.StratifyMarketsSmallParticipation
section
open MeasureTheory Set ProbabilityTheory StratifyMarkets.DoubleAuction StratifyMarkets.Participation

namespace StratifyMarkets.SmallParticipation

/-- Equation (4.14) holds even for ties at the fixed price and for empty markets. -/
theorem trade_count_le_max {n m : ℕ} (v : Fin n → ℝ) (c : Fin m → ℝ) (p : ℝ) :
    tau v c ≤ max (eligible (Ici p) v).card (eligible (Iic p) c).card := by
  classical
  apply Finset.sup_le
  intro j hj
  obtain ⟨hr,hgain⟩ := Finset.mem_filter.mp hj
  have H := Finset.mem_range.mp hr
  have jv : j < (valuesDesc v).length := by simpa [valuesDesc] using H.trans_le (min_le_left _ _)
  have jc : j < (costsAsc c).length := by simpa [costsAsc] using H.trans_le (min_le_right _ _)
  have bound {k : ℕ} (w : Fin k → ℝ) (r : ℝ → ℝ → Bool) (s : Set ℝ) [DecidablePred (· ∈ s)]
      (jk : j < k) (h : ∀ i ≤ j, ((List.ofFn w).mergeSort r).getD i 0 ∈ s) : j+1 ≤ (eligible s w).card := by
    let f := s.indicator (fun _ => (1:ℝ))
    have upper := sorted_positive_sum w r f (fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x) (Nat.succ_le_of_lt jk)
    have lo : (∑ i ∈ Finset.range (j+1), f (((List.ofFn w).mergeSort r).getD i 0)) = j+1 := by
      calc _ = ∑ i ∈ Finset.range (j+1), (1:ℝ) := Finset.sum_congr rfl (fun i hi => Set.indicator_of_mem (h i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))) _)
           _ = _ := by simp
    rw [lo] at upper
    have sum : ∑ i, f (w i) = ((eligible s w).card : ℝ) := by
      unfold f eligible Set.indicator
      convert Finset.sum_boole (R := ℝ) (fun i => w i ∈ s) Finset.univ using 1
      apply Finset.sum_congr rfl
      intro i _
      by_cases H : w i ∈ s <;> simp [H]
    rw [sum] at upper
    exact_mod_cast upper
  by_cases h : p ≤ (valuesDesc v).getD j 0
  · apply le_trans _ (le_max_left _ _)
    apply bound v (fun a b => decide (b ≤ a)) (Ici p) (H.trans_le (min_le_left _ _))
    intro i hi
    change p ≤ (valuesDesc v).getD i 0
    rcases eq_or_lt_of_le hi with rfl|hlt
    · exact h
    · have M := List.pairwise_iff_getElem.mp (List.pairwise_mergeSort' (· ≥ ·) (List.ofFn v)) i j (hi.trans_lt jv) jv hlt
      rw [List.getD_eq_getElem _ _ jv] at h
      rw [List.getD_eq_getElem _ _ (hi.trans_lt jv)]
      exact h.trans M
  · apply le_trans _ (le_max_right _ _)
    apply bound c (fun a b => decide (a ≤ b)) (Iic p) (H.trans_le (min_le_right _ _))
    intro i hi
    change (costsAsc c).getD i 0 ≤ p
    have head : (costsAsc c).getD j 0 ≤ p := (show (costsAsc c).getD j 0 < (valuesDesc v).getD j 0 from hgain).le.trans (le_of_not_ge h)
    rcases eq_or_lt_of_le hi with rfl|hlt
    · exact head
    · have M := List.pairwise_iff_getElem.mp (List.pairwise_mergeSort' (· ≤ ·) (List.ofFn c)) i j (hi.trans_lt jc) jc hlt
      rw [List.getD_eq_getElem _ _ jc] at head
      rw [List.getD_eq_getElem _ _ (hi.trans_lt jc)]
      exact M.trans head

private theorem bernoulli_coordinates {k : ℕ} {X : Type} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (μ : Fin k → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {h : X → (Fin k → ℝ)} (hp : MeasurePreserving h P (Measure.pi μ))
    (s : Set ℝ) [DecidablePred (· ∈ s)] (hs : MeasurableSet s) :
    let f := fun (i : Fin k) (x : X) => s.indicator (fun _ => (1:ℝ)) (h x i)
    (∀ i, Measurable (f i)) ∧ (∀ i, ∀ᵐ x ∂P, f i x = 0 ∨ f i x = 1) ∧ iIndepFun f P ∧
      (∫ x, ∑ i, f i x ∂P) = ∑ i, (μ i).real s := by
  classical
  let g := s.indicator (fun _ => (1:ℝ))
  let G := fun (i : Fin k) (x : Fin k → ℝ) => g (x i)
  have gm : Measurable g := measurable_const.indicator hs
  have Gm (i) : Measurable (G i) := gm.comp (measurable_pi_apply i)
  have ij (i) : MeasurePreserving (fun x => h x i) P (μ i) := (measurePreserving_eval μ i).comp hp
  refine ⟨fun i => (Gm i).comp hp.measurable, fun i => Filter.Eventually.of_forall (fun x => ?_),?_,?_⟩
  · by_cases e : h x i ∈ s <;> simp [Set.indicator,e]
  · have ind := iIndepFun_pi (μ := μ) (X := fun _ => g) (fun _ => gm.aemeasurable)
    have maps := ind.map_fun_eq_pi_map (fun i => (Gm i).aemeasurable)
    apply (iIndepFun_iff_map_fun_eq_pi_map (fun i => ((Gm i).comp hp.measurable).aemeasurable)).mpr
    have L := Measure.map_map (μ := P) (measurable_pi_iff.mpr (fun i => Gm i)) hp.measurable
    have R (i) := Measure.map_map (Gm i) hp.measurable (μ := P)
    change P.map ((fun y i => G i y) ∘ h) = Measure.pi (fun i => P.map (G i ∘ h))
    rw [← L,hp.map_eq]
    simp_rw [← R,hp.map_eq]
    exact maps
  · have ints (i) : Integrable (fun x => g (h x i)) P := ((ij i).integrable_comp gm.aestronglyMeasurable).mpr ((integrable_const _).indicator hs)
    rw [integral_finsetSum _ (fun i _ => ints i)]
    apply Finset.sum_congr rfl
    intro i _
    calc _ = ∫ y, g y ∂μ i := by
           rw [← (ij i).map_eq,integral_map (ij i).measurable.aemeasurable gm.aestronglyMeasurable]
         _ = _ := by simp [g,integral_indicator hs]

theorem small_tail {n m : ℕ} (μ : Fin n → Measure ℝ) (ν : Fin m → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ j, IsProbabilityMeasure (ν j)]
    (s t : Set ℝ) [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)] (hs : MeasurableSet s) (ht : MeasurableSet t)
    (gap : (∑ i, (μ i).real s) ≤ ∑ j, (ν j).real t) (cap : (∑ j, (ν j).real t) < 4) :
    let P := (Measure.pi μ).prod (Measure.pi ν)
    (1/7:ℝ)*P.real {x | 5 < max (1+(eligible s x.1).card) (eligible t x.2).card} ≤
      P.real {x | 1+(eligible s x.1).card ≤ (eligible t x.2).card} := by
  let P := (Measure.pi μ).prod (Measure.pi ν)
  let B := fun (i : Fin n) (x : (Fin n → ℝ) × (Fin m → ℝ)) => s.indicator (fun _ => (1:ℝ)) (x.1 i)
  let S := fun (j : Fin m) (x : (Fin n → ℝ) × (Fin m → ℝ)) => t.indicator (fun _ => (1:ℝ)) (x.2 j)
  obtain ⟨bm,bb,bi,bE⟩ := bernoulli_coordinates P μ measurePreserving_fst s hs
  obtain ⟨sm,sb,si,sE⟩ := bernoulli_coordinates P ν measurePreserving_snd t ht
  have indep : IndepFun (fun x => ∑ i, B i x) (fun x => ∑ j, S j x) P :=
    indepFun_prod (Finset.measurable_sum _ (fun i _ => (measurable_const.indicator hs).comp (measurable_pi_apply i)))
      (Finset.measurable_sum _ (fun j _ => (measurable_const.indicator ht).comp (measurable_pi_apply j)))
  have H := lemma_4_8 P n m B S bm sm bb sb bi si indep (bE.trans_le (gap.trans_eq sE.symm)) (sE.trans_lt cap)
  have bc (x) : ∑ i, B i x = ((eligible s x.1).card : ℝ) := by simp only [B,Set.indicator,eligible,Finset.sum_boole]
  have sc (x) : ∑ j, S j x = ((eligible t x.2).card : ℝ) := by simp only [S,Set.indicator,eligible,Finset.sum_boole]
  simp_rw [bc,sc] at H
  have Z := ENNReal.toReal_mono (measure_ne_top _ _) H
  simp only [ENNReal.toReal_mul] at Z
  norm_num at Z
  convert Z using 2 <;> congr 2 <;> ext x <;> push_cast <;> norm_cast <;> simp only [lt_max_iff]

/-- Removing one coordinate transports the full surplus integral to the
opposite-side count event. No conditioning on a positive-probability event
is necessary for this identity. -/
private theorem remove_coordinate {n m : ℕ} (μ : Fin (n+1) → Measure ℝ) (ν : Fin m → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ j, IsProbabilityMeasure (ν j)]
    (s t : Set ℝ) [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)]
    (i : Fin (n+1)) (f : ℝ → ℝ) (outside : ∀ y, y ∉ s → f y = 0)
    (Q : ℕ → ℕ → Prop)
    (Ameas : MeasurableSet {w : (Fin n → ℝ) × (Fin m → ℝ) | Q (1+(eligible s w.1).card) (eligible t w.2).card}) :
    let E := {x : (Fin (n+1) → ℝ) × (Fin m → ℝ) | Q (eligible s x.1).card (eligible t x.2).card}
    let A := {w : (Fin n → ℝ) × (Fin m → ℝ) | Q (1+(eligible s w.1).card) (eligible t w.2).card}
    (∫ x, E.indicator (fun y => f (y.1 i)) x ∂(Measure.pi μ).prod (Measure.pi ν)) =
      (∫ y, f y ∂μ i) * ((Measure.pi (fun j => μ (i.succAbove j))).prod (Measure.pi ν)).real A := by
  classical
  let E := {x : (Fin (n+1) → ℝ) × (Fin m → ℝ) | Q (eligible s x.1).card (eligible t x.2).card}
  let A := {w : (Fin n → ℝ) × (Fin m → ℝ) | Q (1+(eligible s w.1).card) (eligible t w.2).card}
  let rest := fun j => μ (i.succAbove j)
  let P := (Measure.pi μ).prod (Measure.pi ν)
  let R := (Measure.pi rest).prod (Measure.pi ν)
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
  have eq : (fun x => Φ (iso x)) = E.indicator (fun y => f (y.1 i)) := by
    funext x
    change f (x.1 i) * A.indicator (fun _ => (1:ℝ)) ((fun j => x.1 (i.succAbove j)),x.2) = E.indicator _ x
    by_cases h : x.1 i ∈ s
    · have split : (eligible s x.1).card = 1 + (eligible s (fun j => x.1 (i.succAbove j))).card := by
        unfold eligible
        rw [Finset.card_filter, Fin.sum_univ_succAbove _ i, Finset.card_filter]
        simp only [h,if_true]
      have iff : x ∈ E ↔ ((fun j => x.1 (i.succAbove j)),x.2) ∈ A := by
        change Q _ _ ↔ Q _ _
        rw [split]
      by_cases e : x ∈ E
      · rw [Set.indicator_of_mem e,Set.indicator_of_mem (iff.mp e),mul_one]
      · rw [Set.indicator_of_notMem e,Set.indicator_of_notMem (fun H => e (iff.mpr H)),mul_zero]
    · simp [Set.indicator,outside _ h]
  change (∫ x, E.indicator (fun y => f (y.1 i)) x ∂P) = _
  rw [← eq,hi.integral_comp' Φ]
  dsimp only [Φ]
  rw [integral_prod_mul,integral_indicator Ameas,setIntegral_one_eq_measureReal]

private theorem count_set {n m : ℕ} (s t : Set ℝ) [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)]
    (hs : MeasurableSet s) (ht : MeasurableSet t) (Q : ℕ → ℕ → Prop) :
    MeasurableSet {x : (Fin n → ℝ) × (Fin m → ℝ) | Q (eligible s x.1).card (eligible t x.2).card} := by
  have cnt {k : ℕ} {A : Set ℝ} [DecidablePred (· ∈ A)] (hA : MeasurableSet A) :
      Measurable (fun x : Fin k → ℝ => (eligible A x).card) := by
    have m := count_measurable (k := k) A hA
    apply measurable_to_countable'
    intro j
    have map : (fun x : Fin k → ℝ => (eligible A x).card) ⁻¹' {j} = (fun x => ((eligible A x).card : ℝ)) ⁻¹' {(j : ℝ)} := by
      ext x
      change (eligible A x).card = j ↔ ((eligible A x).card : ℝ) = j
      exact_mod_cast Iff.rfl
    rw [map]
    exact m (measurableSet_singleton _)
  have h : Measurable (fun x : (Fin n → ℝ) × (Fin m → ℝ) => ((eligible s x.1).card,(eligible t x.2).card)) :=
    ((cnt hs).comp measurable_fst).prodMk ((cnt ht).comp measurable_snd)
  exact h (show MeasurableSet {z : ℕ × ℕ | Q z.1 z.2} from MeasurableSet.of_discrete)

noncomputable def weighted {n m : ℕ} (s t : Set ℝ) [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)]
    (f : ℝ → ℝ) (Q : ℕ → ℕ → Prop) (x : (Fin n → ℝ) × (Fin m → ℝ)) : ℝ :=
  {z : (Fin n → ℝ) × (Fin m → ℝ) | Q (eligible s z.1).card (eligible t z.2).card}.indicator
    (fun y => ∑ i, f (y.1 i)) x

theorem compare_weights {n m : ℕ} (μ : Fin n → Measure ℝ) (ν : Fin m → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ j, IsProbabilityMeasure (ν j)]
    (s t : Set ℝ) [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)] (hs : MeasurableSet s) (ht : MeasurableSet t)
    (f : ℝ → ℝ) (hf : Measurable f) (hi : ∀ i, Integrable f (μ i))
    (hn : ∀ y, 0 ≤ f y) (outside : ∀ y, y ∉ s → f y = 0)
    (mean : (∑ i, (μ i).real s) = ∑ j, (ν j).real t) (cap : (∑ j, (ν j).real t) < 4) :
    let P := (Measure.pi μ).prod (Measure.pi ν)
    let E := weighted s t f (fun a b => 5 < max a b)
    let W := weighted s t f (fun a b => a ≤ b)
    Integrable E P ∧ Integrable W P ∧ 1/7*(∫ x, E x ∂P) ≤ ∫ x, W x ∂P := by
  classical
  let P := (Measure.pi μ).prod (Measure.pi ν)
  have parts (Q : ℕ → ℕ → Prop) :
      Integrable (weighted s t f Q) P ∧
      (∫ x, weighted s t f Q x ∂P) = ∑ i, ∫ x, {z : (Fin n → ℝ) × (Fin m → ℝ) | Q (eligible s z.1).card (eligible t z.2).card}.indicator (fun y => f (y.1 i)) x ∂P := by
    let E := {z : (Fin n → ℝ) × (Fin m → ℝ) | Q (eligible s z.1).card (eligible t z.2).card}
    have hm : MeasurableSet E := count_set s t hs ht Q
    have integr (i) : Integrable (fun x : (Fin n → ℝ) × (Fin m → ℝ) => f (x.1 i)) P :=
      (((measurePreserving_eval μ i).comp (measurePreserving_fst (μ := Measure.pi μ) (ν := Measure.pi ν))).integrable_comp hf.aestronglyMeasurable).mpr (hi i)
    refine ⟨(integrable_finsetSum _ (fun i _ => integr i)).indicator hm,?_⟩
    have repr (x) : weighted s t f Q x = ∑ i, E.indicator (fun y => f (y.1 i)) x := by
      by_cases H : x ∈ E <;> change E.indicator _ x = _ <;> simp [Set.indicator,H]
    simp_rw [repr]
    exact integral_finsetSum _ (fun i _ => (integr i).indicator hm)
  let Q := fun a b : ℕ => 5 < max a b
  let W := fun a b : ℕ => a ≤ b
  refine ⟨(parts Q).1,(parts W).1,?_⟩
  rw [(parts Q).2,(parts W).2,Finset.mul_sum]
  cases n with
  | zero => simp
  | succ n =>
    apply Finset.sum_le_sum
    intro i _
    have hA (F : ℕ → ℕ → Prop) := count_set (n := n) (m := m) s t hs ht (fun a b => F (1+a) b)
    rw [remove_coordinate μ ν s t i f outside Q (hA Q),remove_coordinate μ ν s t i f outside W (hA W)]
    have reduced : (∑ j, (μ (i.succAbove j)).real s) ≤ ∑ j, (ν j).real t := by
      rw [← mean, Fin.sum_univ_succAbove _ i]
      linarith [measureReal_nonneg (μ := μ i) (s := s)]
    have H := small_tail (fun j => μ (i.succAbove j)) ν s t hs ht reduced cap
    rw [mul_left_comm]
    exact mul_le_mul_of_nonneg_left H (integral_nonneg hn)

end StratifyMarkets.SmallParticipation
end

-- Solutions.Sol_StratifyMarkets_DoubleAuction_lemma_4_10
section
open MeasureTheory Set StratifyMarkets.DoubleAuction StratifyMarkets.Participation StratifyMarkets.SmallParticipation

theorem solution {n m : ℕ} (I : DAInstance n m) (pt : ℝ) (hpt : I.IsBalancedPrice pt) (hlam : I.expB pt < 4) :
    1/7 * I.FBtauGt5 ≤ I.worstRationed pt := by
  classical
  let : ∀ i, IsProbabilityMeasure (I.μB i) := I.isProb_B
  let : ∀ j, IsProbabilityMeasure (I.μS j) := I.isProb_S
  let B := Ici pt
  let S := Iic pt
  let f := fun x : ℝ => max (x-pt) 0
  let g := fun x : ℝ => max (pt-x) 0
  have hint {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : μ (Icc 0 1)=1) (u : ℝ → ℝ) (hu : Continuous u) : Integrable u μ := by
    obtain ⟨C,hC⟩ := (isCompact_Icc (a := (0:ℝ)) (b := (1:ℝ))).exists_bound_of_continuousOn hu.continuousOn
    apply Integrable.of_bound hu.measurable.aestronglyMeasurable C
    filter_upwards [(mem_ae_iff_prob_eq_one measurableSet_Icc).mpr hμ] with x hx
    exact hC x hx
  have cf : Continuous f := by dsimp [f]; fun_prop
  have cg : Continuous g := by dsimp [g]; fun_prop
  have missB (x) (h : x ∉ B) : f x = 0 := max_eq_right (sub_nonpos.mpr (le_of_not_ge h))
  have missS (x) (h : x ∉ S) : g x = 0 := max_eq_right (sub_nonpos.mpr (le_of_not_ge h))
  let Q := fun a b : ℕ => 5 < max a b
  let W := fun a b : ℕ => a ≤ b
  let eb := weighted B S f Q (n := n) (m := m)
  let es := weighted S B g Q (n := m) (m := n)
  let wb := weighted B S f W (n := n) (m := m)
  let ws := weighted S B g W (n := m) (m := n)
  obtain ⟨ib,ibw,bc⟩ := compare_weights I.μB I.μS B S measurableSet_Ici measurableSet_Iic f cf.measurable
    (fun i => hint (I.support_B i) f cf) (fun _ => le_max_right _ _) missB hpt.2 (by change I.expS pt < 4; rwa [← hpt.2])
  obtain ⟨is,isw,sc⟩ := compare_weights I.μS I.μB S B measurableSet_Iic measurableSet_Ici g cg.measurable
    (fun j => hint (I.support_S j) g cg) (fun _ => le_max_right _ _) missS hpt.2.symm hlam
  change Integrable eb I.law at ib
  change Integrable wb I.law at ibw
  have sw : MeasurePreserving (MeasurableEquiv.prodComm : _ ≃ᵐ _) I.law ((Measure.pi I.μS).prod (Measure.pi I.μB)) :=
    Measure.measurePreserving_swap
  have ies : Integrable (fun x => es x.swap) I.law := (sw.integrable_comp is.aestronglyMeasurable).mpr is
  have iws : Integrable (fun x => ws x.swap) I.law := (sw.integrable_comp isw.aestronglyMeasurable).mpr isw
  change 1/7 * (∫ y, es y ∂_) ≤ ∫ y, ws y ∂_ at sc
  rw [← sw.integral_comp' es,← sw.integral_comp' ws] at sc
  have price : I.FBtauGt5 ≤ (∫ x, eb x ∂I.law) + ∫ x, es x.swap ∂I.law := by
    let E := {x : (Fin n → ℝ) × (Fin m → ℝ) | 5 < tau x.1 x.2}
    have iz := (integrable_first_best I).indicator (measurable_trade_cut 5)
    rw [← integral_add ib ies]
    have zeq : I.FBtauGt5 = ∫ x, E.indicator (fun z => realizedFB z.1 z.2) x ∂I.law := by
      unfold DAInstance.FBtauGt5
      apply integral_congr_ae
      filter_upwards with z
      by_cases H : 5 < tau z.1 z.2 <;> simp [E,Set.indicator,H]
    rw [zeq]
    apply integral_mono iz (ib.add ies)
    intro x
    let countB := (eligible B x.1).card
    let countS := (eligible S x.2).card
    have val (h : 5 < max countB countS) : eb x + es x.swap = ∑ i, f (x.1 i) + ∑ j, g (x.2 j) := by
      have h1 : x ∈ {z | Q (eligible B z.1).card (eligible S z.2).card} := h
      have h2 : x.swap ∈ {z | Q (eligible S z.1).card (eligible B z.2).card} := by
        change 5 < max countS countB
        rwa [max_comm]
      exact congrArg₂ (·+·) (Set.indicator_of_mem h1 _) (Set.indicator_of_mem h2 _)
    by_cases h : x ∈ E
    · rw [Set.indicator_of_mem h]
      change realizedFB x.1 x.2 ≤ eb x + es x.swap
      rw [val ((show 5 < tau x.1 x.2 from h).trans_le (trade_count_le_max _ _ pt))]
      exact realized_surplus _ _ _
    · rw [Set.indicator_of_notMem h]
      exact add_nonneg (Set.indicator_nonneg (fun y _ => Finset.sum_nonneg fun _ _ => le_max_right _ _) x)
        (Set.indicator_nonneg (fun y _ => Finset.sum_nonneg fun _ _ => le_max_right _ _) x.swap)
  have alloc : (∫ x, wb x ∂I.law) + (∫ x, ws x.swap ∂I.law) ≤ I.worstRationed pt := by
    rw [← integral_add ibw iws]
    apply integral_mono (ibw.add iws) (gains_integrable I pt)
    intro x
    apply Finset.le_inf'
    intro T hT
    obtain ⟨h1,h2⟩ := Finset.mem_product.mp hT
    obtain ⟨ib',cb⟩ := Finset.mem_powersetCard.mp h1
    obtain ⟨is',cs⟩ := Finset.mem_powersetCard.mp h2
    have side {k l : ℕ} (s t : Set ℝ) [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)]
        (u : ℝ → ℝ) (u0 : ∀ z, z ∉ s → u z = 0) (un : ∀ z, 0 ≤ u z) (x : Fin k → ℝ) (y : Fin l → ℝ)
        (T : Finset (Fin k)) (hT : T ⊆ eligible s x) (size : T.card = min (eligible s x).card (eligible t y).card) :
        weighted s t u W (x,y) ≤ ∑ i ∈ T, u (x i) := by
      by_cases h : W (eligible s x).card (eligible t y).card
      · have eq : T = eligible s x := Finset.eq_of_subset_of_card_le hT (by rw [size,min_eq_left h])
        have yes : (x,y) ∈ {z | W (eligible s z.1).card (eligible t z.2).card} := h
        rw [weighted,Set.indicator_of_mem yes,eq,eligible,Finset.sum_filter]
        exact (Finset.sum_congr rfl fun i _ => by by_cases b : x i ∈ s <;> simp [b] <;> exact u0 _ b).le
      · have no : (x,y) ∉ {z | W (eligible s z.1).card (eligible t z.2).card} := h
        rw [weighted,Set.indicator_of_notMem no]
        exact Finset.sum_nonneg (fun _ _ => un _)
    have Hb := side B S f missB (fun _ => le_max_right _ _) x.1 x.2 T.1 ib' cb
    have Hs := side S B g missS (fun _ => le_max_right _ _) x.2 x.1 T.2 is' (by simpa only [min_comm] using cs)
    have e1 : (∑ i ∈ T.1, f (x.1 i)) = ∑ i ∈ T.1, (x.1 i-pt) := Finset.sum_congr rfl fun i hi => max_eq_left (sub_nonneg.mpr (Finset.mem_filter.mp (ib' hi)).2)
    have e2 : (∑ j ∈ T.2, g (x.2 j)) = ∑ j ∈ T.2, (pt-x.2 j) := Finset.sum_congr rfl fun j hj => max_eq_left (sub_nonneg.mpr (Finset.mem_filter.mp (is' hj)).2)
    rw [e1,Finset.sum_sub_distrib] at Hb
    rw [e2,Finset.sum_sub_distrib] at Hs
    simp only [Finset.sum_const,nsmul_eq_mul,cb,cs] at Hb Hs
    change wb x + ws x.swap ≤ _
    change wb x ≤ _ at Hb
    change ws x.swap ≤ _ at Hs
    linarith only [Hb,Hs]
  change 1/7*(∫ x, eb x ∂I.law) ≤ ∫ x, wb x ∂I.law at bc
  change 1/7*(∫ x, es x.swap ∂I.law) ≤ ∫ x, ws x.swap ∂I.law at sc
  linarith only [price,alloc,bc,sc]
end
