-- Prove2me | solution 1 for StratifyMarkets.DoubleAuction.lemma_4_12
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T06:50:21.010248+00:00
-- url     : https://prove2.me/submissions/6b6034a2-569d-463d-a372-2e756e642833

import Definitions.Def_StratifyMarkets_DoubleAuction_Prices
import Definitions.Def_StratifyMarkets_DoubleAuction_Submarket
import Definitions.Def_StratifyMarkets_DoubleAuction_WorstRationed
import Mathlib
import Theorems.Thm_StratifyMarkets_DoubleAuction_theorem_3_1
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

-- Solutions.StratifyMarketsSuperAgents
section
open MeasureTheory Set
namespace StratifyMarkets.DoubleAuction

theorem vmax_meas {n : ℕ} [NeZero n] : Measurable (vmax (n := n)) := by
  have h := Finset.measurable_sup' Finset.univ_nonempty
    (fun i _ => measurable_pi_apply (X := fun _ : Fin n => ℝ) i)
  have heq : vmax (n := n) = Finset.univ.sup' Finset.univ_nonempty
      (fun i (v : Fin n → ℝ) => v i) := by
    funext v
    exact (Finset.sup'_apply Finset.univ_nonempty (fun i (w : Fin n → ℝ) => w i) v).symm
  rw [heq]
  exact h

theorem cmin_meas {m : ℕ} [NeZero m] : Measurable (cmin (m := m)) := by
  have h := Finset.measurable_sup' (α := ℝᵒᵈ) Finset.univ_nonempty
    (fun i _ => measurable_pi_apply (X := fun _ : Fin m => ℝᵒᵈ) i)
  have heq : cmin (m := m) = Finset.univ.inf' Finset.univ_nonempty
      (fun i (c : Fin m → ℝ) => c i) := by
    funext c
    exact (Finset.inf'_apply Finset.univ_nonempty (fun i (w : Fin m → ℝ) => w i) c).symm
  rw [heq]
  exact h

private theorem extremum_law {k : ℕ} (μ : Fin k → Measure ℝ) [∀ j, IsProbabilityMeasure (μ j)]
    (hn : ∀ j, NullSingletonClass (μ j)) (hs : ∀ j, μ j (Icc 0 1) = 1)
    (f : (Fin k → ℝ) → ℝ) (hf : Measurable f) (attains : ∀ x, ∃ j, f x = x j) :
    IsProbabilityMeasure ((Measure.pi μ).map f) ∧ NullSingletonClass ((Measure.pi μ).map f) ∧
      (Measure.pi μ).map f (Icc 0 1) = 1 := by
  let : IsProbabilityMeasure ((Measure.pi μ).map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  refine ⟨inferInstance, ⟨fun r => ?_⟩, ?_⟩
  · rw [Measure.map_apply hf (measurableSet_singleton _)]
    have coord (i : Fin k) : ∀ᵐ x ∂Measure.pi μ, x i ≠ r :=
      (measurePreserving_eval μ i).quasiMeasurePreserving.ae (by
        let := hn i
        exact (μ i).ae_ne r)
    have null : ∀ᵐ x ∂Measure.pi μ, f x ≠ r := by
      filter_upwards [ae_all_iff.mpr coord] with x hx
      obtain ⟨i,hi⟩ := attains x
      exact hi ▸ hx i
    exact compl_mem_ae_iff.mp null
  · rw [Measure.map_apply hf measurableSet_Icc]
    apply (mem_ae_iff_prob_eq_one (hf measurableSet_Icc)).mp
    have coord (i : Fin k) : ∀ᵐ x ∂Measure.pi μ, x i ∈ Icc (0 : ℝ) 1 :=
      (measurePreserving_eval μ i).quasiMeasurePreserving.ae
        ((mem_ae_iff_prob_eq_one measurableSet_Icc).mpr (hs i))
    filter_upwards [ae_all_iff.mpr coord] with x hx
    obtain ⟨i,hi⟩ := attains x
    change f x ∈ Icc 0 1
    rw [hi]
    exact hx i

/-- The extrema in the double-auction profile define an admissible atomless
bilateral instance; the buyer and seller are sampled independently. -/
noncomputable def superAgents {n m : ℕ} [NeZero n] [NeZero m] (I : DAInstance n m) : BTInstance := by
  let : ∀ i, IsProbabilityMeasure (I.μB i) := I.isProb_B
  let : ∀ i, IsProbabilityMeasure (I.μS i) := I.isProb_S
  have hB := extremum_law I.μB I.noAtoms_B I.support_B vmax vmax_meas (fun x => by
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty x
    exact ⟨i,hi⟩)
  have hS := extremum_law I.μS I.noAtoms_S I.support_S cmin cmin_meas (fun x => by
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty x
    exact ⟨i,hi⟩)
  exact ⟨_, _, hB.1, hS.1, hB.2.1, hS.2.1, hB.2.2, hS.2.2⟩

private theorem super_integral {n m : ℕ} [NeZero n] [NeZero m] (I : DAInstance n m)
    (f : ℝ × ℝ → ℝ) (hf : Measurable f) :
    ∫ x, f x ∂(superAgents I).law = ∫ x, f (cmin x.2, vmax x.1) ∂I.law := by
  let : ∀ i, IsProbabilityMeasure (I.μB i) := I.isProb_B
  let : ∀ j, IsProbabilityMeasure (I.μS j) := I.isProb_S
  change (∫ x, f x ∂(((Measure.pi I.μS).map cmin).prod ((Measure.pi I.μB).map vmax))) = _
  rw [Measure.map_prod_map _ _ cmin_meas vmax_meas, integral_map (cmin_meas.prodMap vmax_meas).aemeasurable hf.aestronglyMeasurable]
  have swap : MeasurePreserving (MeasurableEquiv.prodComm : _ ≃ᵐ _)
      ((Measure.pi I.μB).prod (Measure.pi I.μS)) ((Measure.pi I.μS).prod (Measure.pi I.μB)) :=
    Measure.measurePreserving_swap
  exact (swap.integral_comp' (fun z => f ((Prod.map cmin vmax) z))).symm

theorem superAgents_first_best {n m : ℕ} [NeZero n] [NeZero m] (I : DAInstance n m) :
    (superAgents I).FB = ∫ x, max (vmax x.1 - cmin x.2) 0 ∂I.law :=
  super_integral I (fun x => max (x.2-x.1) 0) (by fun_prop)

theorem superAgents_strat {n m : ℕ} [NeZero n] [NeZero m] (I : DAInstance n m) (σ : Stratification) :
    (superAgents I).strat σ = ∑ k : Fin σ.N, I.superFP (σ.m k.castSucc) (σ.p k) (σ.m k.succ) := by
  apply Finset.sum_congr rfl
  intro k _
  apply super_integral
  apply Measurable.ite
  · exact (measurableSet_le measurable_const measurable_fst).inter
      ((measurableSet_le measurable_fst measurable_const).inter
        ((measurableSet_le measurable_const measurable_snd).inter
          (measurableSet_le measurable_snd measurable_const)))
  · exact measurable_snd.sub measurable_fst
  · exact measurable_const

/-- Equation (4.35) transports the bilateral theorem to the exact super-agent
integrals of the double auction. -/
theorem superAgents_bilateral_guarantee {n m : ℕ} [NeZero n] [NeZero m] (I : DAInstance n m) :
    ∃ σ : Stratification, 1/(12*Real.exp 1) * (∫ x, max (vmax x.1-cmin x.2) 0 ∂I.law) ≤
      ∑ k : Fin σ.N, I.superFP (σ.m k.castSucc) (σ.p k) (σ.m k.succ) := by
  obtain ⟨σ,hσ⟩ := theorem_3_1 (superAgents I)
  exact ⟨σ, by simpa only [superAgents_first_best, superAgents_strat] using hσ⟩

end StratifyMarkets.DoubleAuction
end

-- Solutions.StratifyMarketsScarcity
section
open MeasureTheory Set StratifyMarkets.Participation

namespace StratifyMarkets.Scarcity

/-- The no-other-participant factor is at least one minus the total marginal participation. -/
theorem product_failure {ι : Type*} (u : ι → ℝ) (hu : ∀ i, 0 ≤ u i) (hu1 : ∀ i, u i ≤ 1) (s : Finset ι) :
    1 - ∑ i ∈ s, u i ≤ ∏ i ∈ s, (1-u i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s h ih =>
    rw [Finset.prod_insert h, Finset.sum_insert h]
    have e := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr (hu1 i))
    nlinarith [mul_nonneg (hu i) (Finset.sum_nonneg (s := s) fun j _ => hu j)]

noncomputable def others {n : ℕ} (s : Set ℝ) (i : Fin n) : Set (Fin n → ℝ) :=
  univ.pi (Function.update (fun _ : Fin n => sᶜ) i univ)

theorem mem_others {n : ℕ} {s : Set ℝ} {i : Fin n} {x : Fin n → ℝ} :
    x ∈ others s i ↔ ∀ j, j ≠ i → x j ∉ s := by
  classical
  simp [others, Set.mem_pi,Function.update_apply]

theorem measurable_others {n : ℕ} {s : Set ℝ} (hs : MeasurableSet s) (i : Fin n) :
    MeasurableSet (others s i) := by
  classical
  apply MeasurableSet.univ_pi
  intro j
  by_cases eq : j = i <;> simp [eq,hs.compl]

theorem isolated_factor {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (s : Set ℝ) (hs : MeasurableSet s) (i : Fin n) (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ x, (others s i).indicator (fun y => f (y i)) x ∂Measure.pi μ) =
      (∏ j ∈ Finset.univ.erase i, (1 - (μ j).real s)) * ∫ y, f y ∂μ i := by
  classical
  let A := Function.update (fun _ : Fin n => sᶜ) i univ
  let ν := fun j => (μ j).restrict (A j)
  rw [integral_indicator (measurable_others hs i)]
  unfold others
  rw [Measure.restrict_pi_pi]
  change (∫ x, f (Function.eval i x) ∂Measure.pi ν) = _
  rw [← integral_map (measurable_pi_apply i).aemeasurable hf.aestronglyMeasurable, Measure.pi_map_eval, integral_smul_measure]
  have ei : ν i = μ i := by simp [ν,A]
  rw [ei]
  simp only [ENNReal.toReal_prod, smul_eq_mul]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  have ne := (Finset.mem_erase.mp hj).1
  simp [ν,A,Function.update_of_ne ne, ← measureReal_def, measureReal_compl hs]

/-- Equation (A.7) for an arbitrary nonnegative coordinate weight. The index
itself is unconstrained in the box, which also handles zero eligibility mass. -/
theorem isolated_integral {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (s : Set ℝ) (hs : MeasurableSet s) (cap : (∑ j, (μ j).real s) ≤ 1/4)
    (i : Fin n) (f : ℝ → ℝ) (hf : Measurable f) (hn : ∀ x, 0 ≤ f x) :
    3/4 * (∫ y, f y ∂μ i) ≤ ∫ x, (others s i).indicator (fun y => f (y i)) x ∂Measure.pi μ := by
  classical
  rw [isolated_factor μ s hs i f hf]
  apply mul_le_mul_of_nonneg_right _ (integral_nonneg hn)
  have total := Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset i (Finset.univ : Finset (Fin n)))
    (fun j _ _ => measureReal_nonneg (μ := μ j) (s := s))
  have low := product_failure (fun j => (μ j).real s) (fun _ => measureReal_nonneg) (fun _ => measureReal_le_one)
    (Finset.univ.erase i)
  linarith


/-- Weighted surplus when a participant is the unique eligible coordinate. -/
noncomputable def uniqueWeight {n : ℕ} (s : Set ℝ) (f : ℝ → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, (others s i).indicator (fun y => f (y i)) x

theorem unique_integral {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (s : Set ℝ) (hs : MeasurableSet s) (cap : (∑ j, (μ j).real s) ≤ 1/4)
    (f : ℝ → ℝ) (hf : Measurable f) (hi : ∀ i, Integrable f (μ i)) (hn : ∀ x, 0 ≤ f x) :
    Integrable (uniqueWeight s f) (Measure.pi μ) ∧
      3/4 * (∑ i, ∫ y, f y ∂μ i) ≤ ∫ x, uniqueWeight s f x ∂Measure.pi μ := by
  have h (i) : Integrable ((others s i).indicator (fun y => f (y i))) (Measure.pi μ) :=
    (((measurePreserving_eval μ i).integrable_comp hf.aestronglyMeasurable).mpr (hi i)).indicator (measurable_others hs i)
  refine ⟨integrable_finsetSum _ (fun i _ => h i), ?_⟩
  unfold uniqueWeight
  rw [integral_finsetSum _ (fun i _ => h i), Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => isolated_integral μ s hs cap i f hf hn

theorem unique_le_alloc {n : ℕ} {s : Set ℝ} [DecidablePred (· ∈ s)] (x : Fin n → ℝ)
    (f : ℝ → ℝ) (outside : ∀ y, y ∉ s → f y = 0) (hn : ∀ y, 0 ≤ f y)
    (T : Finset (Fin n)) (sub : T ⊆ eligible s x) (pos : (eligible s x).Nonempty → T.Nonempty) :
    uniqueWeight s f x ≤ ∑ i ∈ T, f (x i) := by
  classical
  have eq : (∑ i ∈ T, f (x i)) = ∑ i, if i ∈ T then f (x i) else 0 := by
    rw [← Finset.sum_filter]
    simp
  rw [eq,uniqueWeight]
  apply Finset.sum_le_sum
  intro i _
  by_cases e : x i ∈ s
  · by_cases iso : x ∈ others s i
    · have mem : i ∈ eligible s x := Finset.mem_filter.mpr ⟨Finset.mem_univ _,e⟩
      obtain ⟨j,hj⟩ := pos ⟨i,mem⟩
      have eq : j = i := by
        by_contra hji
        exact mem_others.mp iso j hji (Finset.mem_filter.mp (sub hj)).2
      have hi : i ∈ T := eq ▸ hj
      simp [iso,hi]
    · by_cases hi : i ∈ T <;> simp [iso,hi,hn]
  · simp [Set.indicator,outside _ e]

theorem bounded_band {μ : Measure ℝ} [IsProbabilityMeasure μ] {lo hi : ℝ} (hh : lo ≤ hi) :
    Integrable ((Icc lo hi).indicator (fun y => y-lo)) μ ∧ Integrable ((Icc lo hi).indicator (fun y => hi-y)) μ := by
  constructor
  · apply Integrable.of_bound ((measurable_id.sub measurable_const).indicator measurableSet_Icc).aestronglyMeasurable (hi-lo)
    filter_upwards with y
    by_cases h : y ∈ Icc lo hi
    · rw [Set.indicator_of_mem h]
      change ‖y-lo‖ ≤ _
      rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr h.1)]
      exact sub_le_sub_right h.2 _
    · simp [h,sub_nonneg.mpr hh]
  · apply Integrable.of_bound ((measurable_const.sub measurable_id).indicator measurableSet_Icc).aestronglyMeasurable (hi-lo)
    filter_upwards with y
    by_cases h : y ∈ Icc lo hi
    · rw [Set.indicator_of_mem h]
      change ‖hi-y‖ ≤ _
      rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr h.2)]
      exact sub_le_sub_left h.1 _
    · simp [h,sub_nonneg.mpr hh]

noncomputable def oneEvent {n : ℕ} (s : Set ℝ) [DecidablePred (· ∈ s)] : Set (Fin n → ℝ) :=
  {x | (eligible s x).card = 1}

theorem one_meas {n : ℕ} {s : Set ℝ} [DecidablePred (· ∈ s)] (hs : MeasurableSet s) :
    MeasurableSet (oneEvent (n := n) s) := by
  have card (x : Fin n → ℝ) : ((eligible s x).card : ℝ) = ∑ i, s.indicator (fun _ => (1:ℝ)) (x i) := by
    simp only [Set.indicator,eligible,Finset.sum_boole]
  have hm : Measurable (fun x : Fin n → ℝ => ((eligible s x).card : ℝ)) := by
    simp_rw [card]
    exact Finset.measurable_sum _ fun i _ => (measurable_const.indicator hs).comp (measurable_pi_apply i)
  have eq : oneEvent (n := n) s = (fun x : Fin n → ℝ => ((eligible s x).card : ℝ)) ⁻¹' {1} := by
    ext x
    change (eligible s x).card = 1 ↔ ((eligible s x).card : ℝ) = 1
    norm_cast
  rw [eq]
  exact hm (measurableSet_singleton _)

/-- If there is one eligible coordinate the isolated weight is its weight;
on all other profiles the isolated weight vanishes. -/
theorem unique_eq {n : ℕ} (s : Set ℝ) [DecidablePred (· ∈ s)] (f : ℝ → ℝ)
    (out : ∀ y, y ∉ s → f y = 0) (x : Fin n → ℝ) :
    uniqueWeight s f x = (oneEvent s).indicator (fun y => ∑ i ∈ eligible s y, f (y i)) x := by
  classical
  by_cases h : x ∈ oneEvent s
  · rw [Set.indicator_of_mem h]
    obtain ⟨j,ej⟩ := Finset.card_eq_one.mp h
    have iso : x ∈ others s j := by
      apply mem_others.mpr
      intro k ne hk
      have H : k ∈ eligible s x := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk⟩
      simpa [ej,ne] using H
    rw [ej,Finset.sum_singleton,uniqueWeight,Finset.sum_eq_single j,Set.indicator_of_mem iso]
    · intro k _ ne
      have hn : x k ∉ s := mem_others.mp iso k ne
      simp [Set.indicator,out _ hn]
    · simp
  · rw [Set.indicator_of_notMem h,uniqueWeight]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : x i ∈ s
    · apply Set.indicator_of_notMem
      intro iso
      apply h
      apply Finset.card_eq_one.mpr
      refine ⟨i,?_⟩
      ext j
      by_cases eq : j = i
      · simp [eligible,eq,hi]
      · simp [eligible,eq,mem_others.mp iso j eq]
    · simp [Set.indicator,out _ hi]

theorem one_probability {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (s : Set ℝ) [DecidablePred (· ∈ s)] (hs : MeasurableSet s) (mass : (∑ i, (μ i).real s) = 1/4) :
    3/16 ≤ (Measure.pi μ).real (oneEvent s) ∧ (Measure.pi μ).real (oneEvent s) ≤ 1/4 := by
  let f := s.indicator (fun _ => (1:ℝ))
  have f0 (y) (hy : y ∉ s) : f y = 0 := Set.indicator_of_notMem hy _
  have iden (x : Fin n → ℝ) : uniqueWeight s f x = (oneEvent s).indicator (fun _ => (1:ℝ)) x := by
    rw [unique_eq s f f0]
    by_cases h : x ∈ oneEvent s
    · obtain ⟨j,ej⟩ := Finset.card_eq_one.mp h
      have hj : x j ∈ s := (Finset.mem_filter.mp (ej ▸ Finset.mem_singleton_self j : j ∈ eligible s x)).2
      simp [h,ej,f,hj]
    · simp [h]
  have hu := (unique_integral μ s hs mass.le f (measurable_const.indicator hs)
    (fun _ => (integrable_const _).indicator hs) (fun y => Set.indicator_nonneg (fun _ _ => zero_le_one) y)).2
  simp_rw [iden] at hu
  simp only [f,integral_indicator hs, integral_indicator (one_meas hs),setIntegral_one_eq_measureReal,mass] at hu
  refine ⟨by linarith,?_⟩
  have sub : oneEvent (n := n) s ⊆ ⋃ i : Fin n, Function.eval i ⁻¹' s := by
    intro x h
    have hm : (eligible s x).Nonempty := Finset.card_pos.mp (show 0 < (eligible s x).card by rw [show (eligible s x).card = 1 from h]; decide)
    obtain ⟨j,hj⟩ := hm
    exact Set.mem_iUnion.mpr ⟨j,(Finset.mem_filter.mp hj).2⟩
  have u := (measureReal_mono (μ := Measure.pi μ) sub).trans (measureReal_iUnion_fintype_le _)
  apply u.trans_eq
  rw [← mass]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg ENNReal.toReal ((measurePreserving_eval μ i).measure_preimage hs.nullMeasurableSet)

/-- Adding a middle band of mass at most one quarter preserves at least
two thirds of each isolated-coordinate surplus (equations 4.28–4.32). -/
theorem middle_comparison {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (s t : Set ℝ) (hs : MeasurableSet s) (ht : MeasurableSet t) (sub : s ⊆ t)
    (cap : (∑ j, (μ j).real s) ≤ 1/4) (mid : (∑ j, (μ j).real (t \ s)) ≤ 1/4)
    (i : Fin n) (f : ℝ → ℝ) (hf : Measurable f) (hn : ∀ y, 0 ≤ f y) :
    2/3 * (∫ x, (others s i).indicator (fun y => f (y i)) x ∂Measure.pi μ) ≤
      ∫ x, (others t i).indicator (fun y => f (y i)) x ∂Measure.pi μ := by
  classical
  let u := fun j => (μ j).real (t \ s) / (1 - (μ j).real s)
  have den (j) : (3/4:ℝ) ≤ 1-(μ j).real s := by
    have H := Finset.single_le_sum (f := fun k => (μ k).real s) (fun _ _ => measureReal_nonneg) (Finset.mem_univ j)
    linarith
  have un (j) : 0 ≤ u j := div_nonneg measureReal_nonneg (by linarith only [den j])
  have ub (j) : u j ≤ 4/3 * (μ j).real (t \ s) := by
    apply (div_le_iff₀ (by linarith only [den j] : 0 < 1-(μ j).real s)).mpr
    nlinarith [mul_le_mul_of_nonneg_left (den j) (measureReal_nonneg (μ := μ j) (s := t \ s))]
  have total := Finset.sum_le_sum (s := Finset.univ) fun j _ => ub j
  rw [← Finset.mul_sum] at total
  have total' : (∑ j, u j) ≤ 1/3 := by linarith only [total,mid]
  have u1 (j) : u j ≤ 1 := by
    have H := Finset.single_le_sum (f := u) (fun k _ => un k) (Finset.mem_univ j)
    linarith
  have rest := Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset i (Finset.univ : Finset (Fin n))) (fun j _ _ => un j)
  have good := product_failure u un u1 (Finset.univ.erase i)
  have der (j) : 1-(μ j).real t = (1-(μ j).real s)*(1-u j) := by
    have hpos : 0 < 1-(μ j).real s := by linarith only [den j]
    dsimp only [u]
    rw [measureReal_sdiff sub hs]
    field_simp
    ring
  rw [isolated_factor μ s hs i f hf,isolated_factor μ t ht i f hf]
  simp_rw [der]
  rw [Finset.prod_mul_distrib, ← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (integral_nonneg hn)
  rw [mul_comm (2/3:ℝ)]
  exact mul_le_mul_of_nonneg_left (by linarith only [good,rest,total']) (Finset.prod_nonneg fun j _ => sub_nonneg.mpr measureReal_le_one)

theorem unique_comparison {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (s t : Set ℝ) (hs : MeasurableSet s) (ht : MeasurableSet t) (sub : s ⊆ t)
    (cap : (∑ j, (μ j).real s) ≤ 1/4) (mid : (∑ j, (μ j).real (t \ s)) ≤ 1/4)
    (f : ℝ → ℝ) (hf : Measurable f) (hi : ∀ i, Integrable f (μ i)) (hn : ∀ y, 0 ≤ f y) :
    Integrable (uniqueWeight t f) (Measure.pi μ) ∧
      2/3 * (∫ x, uniqueWeight s f x ∂Measure.pi μ) ≤ ∫ x, uniqueWeight t f x ∂Measure.pi μ := by
  have int {A : Set ℝ} (hA : MeasurableSet A) (i) : Integrable ((others A i).indicator (fun y => f (y i))) (Measure.pi μ) :=
    (((measurePreserving_eval μ i).integrable_comp hf.aestronglyMeasurable).mpr (hi i)).indicator (measurable_others hA i)
  refine ⟨integrable_finsetSum _ (fun i _ => int ht i), ?_⟩
  unfold uniqueWeight
  rw [integral_finsetSum _ (fun i _ => int hs i),integral_finsetSum _ (fun i _ => int ht i),Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => middle_comparison μ s t hs ht sub cap mid i f hf hn

open StratifyMarkets.DoubleAuction

/-- The numerator in the definition of one trade splits at any intermediate price. -/
theorem one_trade_numerator {n m : ℕ} (I : DAInstance n m) (a b tB tS q : ℝ)
    (hB : tB ≤ b) (hS : a ≤ tS) (hq1 : tS ≤ q) (hq2 : q ≤ tB) :
    let B := Icc tB b
    let S := Icc a tS
    let f := B.indicator (fun y => y-q)
    let g := S.indicator (fun y => q-y)
    let μ := Measure.pi I.μB
    let ν := Measure.pi I.μS
    I.oneTrade a b tB tS * (μ.real (oneEvent B) * ν.real (oneEvent S)) =
      (∫ x, uniqueWeight B f x ∂μ)*ν.real (oneEvent S) + μ.real (oneEvent B)*(∫ y, uniqueWeight S g y ∂ν) := by
  classical
  let : ∀ i, IsProbabilityMeasure (I.μB i) := I.isProb_B
  let : ∀ j, IsProbabilityMeasure (I.μS j) := I.isProb_S
  let B := Icc tB b
  let S := Icc a tS
  let μ := Measure.pi I.μB
  let ν := Measure.pi I.μS
  let EB := oneEvent (n := n) B
  let ES := oneEvent (n := m) S
  let f := B.indicator (fun y => y-q)
  let g := S.indicator (fun y => q-y)
  let U : (Fin n → ℝ) → ℝ := uniqueWeight B f
  let V : (Fin m → ℝ) → ℝ := uniqueWeight S g
  let LB := EB.indicator (fun _ => (1:ℝ))
  let LS := ES.indicator (fun _ => (1:ℝ))
  have ub (i) : Integrable f (I.μB i) := by
    have x : Integrable ((Icc q b).indicator (fun y => y-q)) (I.μB i) := (bounded_band (hq2.trans hB)).1
    have H := x.indicator (s := B) measurableSet_Icc
    have inB : B ⊆ Icc q b := Icc_subset_Icc_left hq2
    simpa only [indicator_indicator,inter_eq_self_of_subset_left inB] using H
  have us (j) : Integrable g (I.μS j) := by
    have x : Integrable ((Icc a q).indicator (fun y => q-y)) (I.μS j) := (bounded_band (hS.trans hq1)).2
    have H := x.indicator (s := S) measurableSet_Icc
    have inS : S ⊆ Icc a q := Icc_subset_Icc_right hq1
    simpa only [indicator_indicator,inter_eq_self_of_subset_left inS] using H
  have iU : Integrable U μ := integrable_finsetSum _ fun i _ =>
    (((measurePreserving_eval I.μB i).integrable_comp ((measurable_id.sub measurable_const).indicator measurableSet_Icc).aestronglyMeasurable).mpr (ub i)).indicator (measurable_others measurableSet_Icc i)
  have iV : Integrable V ν := integrable_finsetSum _ fun j _ =>
    (((measurePreserving_eval I.μS j).integrable_comp ((measurable_const.sub measurable_id).indicator measurableSet_Icc).aestronglyMeasurable).mpr (us j)).indicator (measurable_others measurableSet_Icc j)
  have mB : MeasurableSet EB := one_meas measurableSet_Icc
  have mS : MeasurableSet ES := one_meas measurableSet_Icc
  have lb : Integrable LB μ := (integrable_const _).indicator mB
  have ls : Integrable LS ν := (integrable_const _).indicator mS
  have eB : (∫ x, LB x ∂μ) = μ.real EB := by simp [LB,integral_indicator mB]
  have eS : (∫ y, LS y ∂ν) = ν.real ES := by simp [LS,integral_indicator mS]
  let pay := fun z : (Fin n → ℝ) × (Fin m → ℝ) => if (inRange tB b z.1).card = 1 ∧ (inRange a tS z.2).card = 1
    then ∑ i ∈ inRange tB b z.1, ∑ j ∈ inRange a tS z.2, (z.1 i - z.2 j) else 0
  have decomp (z : (Fin n → ℝ) × (Fin m → ℝ)) : pay z = U z.1 * LS z.2 + LB z.1 * V z.2 := by
    change (if (eligible B z.1).card = 1 ∧ (eligible S z.2).card = 1 then ∑ i ∈ eligible B z.1, ∑ j ∈ eligible S z.2, (z.1 i - z.2 j) else 0) = _
    dsimp only [U,V]
    rw [unique_eq B f (fun _ h => Set.indicator_of_notMem h _),unique_eq S g (fun _ h => Set.indicator_of_notMem h _)]
    by_cases bH : z.1 ∈ EB <;> by_cases sH : z.2 ∈ ES
    · obtain ⟨i,hi⟩ := Finset.card_eq_one.mp bH
      obtain ⟨j,hj⟩ := Finset.card_eq_one.mp sH
      have bi : z.1 i ∈ B := (Finset.mem_filter.mp (hi ▸ Finset.mem_singleton_self i : i ∈ eligible B z.1)).2
      have sj : z.2 j ∈ S := (Finset.mem_filter.mp (hj ▸ Finset.mem_singleton_self j : j ∈ eligible S z.2)).2
      change z.1 ∈ oneEvent B at bH
      change z.2 ∈ oneEvent S at sH
      simp [hi,hj,LB,LS,EB,ES,bH,sH,f,g,bi,sj]
    all_goals
      have no : ¬((eligible B z.1).card = 1 ∧ (eligible S z.2).card = 1) := by
        intro H
        first | exact bH H.1 | exact sH H.2
      rw [if_neg no]
      dsimp only [LB,LS]
      simp [EB,ES] at bH sH ⊢ <;> simp [Set.indicator,bH,sH]
  have den : (I.law {x | (inRange tB b x.1).card = 1 ∧ (inRange a tS x.2).card = 1}).toReal = μ.real EB * ν.real ES := by
    change ((μ.prod ν) (EB ×ˢ ES)).toReal = _
    rw [Measure.prod_prod,ENNReal.toReal_mul]; rfl
  have N : (∫ z, pay z ∂I.law) = (∫ x, U x ∂μ)*ν.real ES + μ.real EB*(∫ y, V y ∂ν) := by
    simp_rw [decomp]
    change (∫ z, _ ∂μ.prod ν) = _
    rw [integral_add (iU.mul_prod ls) (lb.mul_prod iV),integral_prod_mul,integral_prod_mul,eB,eS]
  change I.oneTrade a b tB tS * (μ.real EB*ν.real ES) = _
  rw [← N]; unfold DAInstance.oneTrade
  rw [den]
  change (∫ z, pay z ∂I.law) / _ * _ = ∫ z, pay z ∂I.law
  by_cases h : μ.real EB * ν.real ES = 0
  · have hnull : I.law (EB ×ˢ ES) = 0 := by
      have : (I.law (EB ×ˢ ES)).toReal = 0 := den.trans h
      exact (ENNReal.toReal_eq_zero_iff _).mp this |>.resolve_right (by unfold DAInstance.law; exact measure_ne_top _ _)
    have zae : ∀ᵐ z ∂I.law, z ∉ EB ×ˢ ES := compl_mem_ae_iff.mpr hnull
    have nil : ∫ z, pay z ∂I.law = 0 := integral_eq_zero_of_ae (zae.mono (fun z hz => by
      have no : ¬((inRange tB b z.1).card = 1 ∧ (inRange a tS z.2).card = 1) := hz
      simp [pay,no]))
    rw [nil]; simp
  · exact div_mul_cancel₀ _ h

end StratifyMarkets.Scarcity
end

-- Solutions.Sol_StratifyMarkets_DoubleAuction_lemma_4_12
section
open MeasureTheory Set StratifyMarkets.DoubleAuction StratifyMarkets.Participation StratifyMarkets.Scarcity

private noncomputable def anyEligible {n : ℕ} (s : Set ℝ) : Set (Fin n → ℝ) :=
  ⋃ i, Function.eval i ⁻¹' s

private theorem any_meas {n : ℕ} {s : Set ℝ} (hs : MeasurableSet s) : MeasurableSet (anyEligible (n := n) s) :=
  MeasurableSet.iUnion fun i => measurable_pi_apply i hs

private theorem any_iff {n : ℕ} {s : Set ℝ} [DecidablePred (· ∈ s)] {x : Fin n → ℝ} :
    x ∈ anyEligible s ↔ (eligible s x).Nonempty := by
  simp [anyEligible,eligible,Finset.Nonempty]

private noncomputable def lamp {n : ℕ} (s : Set ℝ) (x : Fin n → ℝ) : ℝ :=
  (anyEligible s).indicator (fun _ => 1) x

private theorem lamp_integrable {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {s : Set ℝ} (hs : MeasurableSet s) : Integrable (lamp s) (Measure.pi μ) :=
  (integrable_const _).indicator (any_meas hs)

theorem solution {n m : ℕ} [NeZero n] [NeZero m] (I : DAInstance n m) (a b p : ℝ)
    (_ha : 0 ≤ a) (_hab : a < b) (_hb : b ≤ 1) (hap : a ≤ p) (hpb : p ≤ b)
    (hB : I.expBuyersIn p b ≤ 1/4) (hS : I.expSellersIn a p ≤ 1/4) :
    3/4 * I.superFP a p b ≤ I.worstRationedIn a p b := by
  classical
  let : ∀ i, IsProbabilityMeasure (I.μB i) := I.isProb_B
  let : ∀ j, IsProbabilityMeasure (I.μS j) := I.isProb_S
  let : IsProbabilityMeasure I.law := by unfold DAInstance.law; infer_instance
  let B := Icc p b
  let S := Icc a p
  let f := B.indicator (fun y => y-p)
  let g := S.indicator (fun y => p-y)
  have fb : Measurable f := (measurable_id.sub measurable_const).indicator measurableSet_Icc
  have gs : Measurable g := (measurable_const.sub measurable_id).indicator measurableSet_Icc
  have fn (x) : 0 ≤ f x := Set.indicator_nonneg (fun _ h => sub_nonneg.mpr h.1) x
  have gn (x) : 0 ≤ g x := Set.indicator_nonneg (fun _ h => sub_nonneg.mpr h.2) x
  have fi (i) : Integrable f (I.μB i) := (bounded_band hpb).1
  have gi (j) : Integrable g (I.μS j) := (bounded_band hap).2
  let F := fun x : Fin n → ℝ => ∑ i, f (x i)
  let G := fun y : Fin m → ℝ => ∑ j, g (y j)
  have fi' (i) : Integrable (fun x : Fin n → ℝ => f (x i)) (Measure.pi I.μB) := ((measurePreserving_eval I.μB i).integrable_comp fb.aestronglyMeasurable).mpr (fi i)
  have gi' (j) : Integrable (fun y : Fin m → ℝ => g (y j)) (Measure.pi I.μS) := ((measurePreserving_eval I.μS j).integrable_comp gs.aestronglyMeasurable).mpr (gi j)
  have iF : Integrable F (Measure.pi I.μB) := integrable_finsetSum _ (fun i _ => fi' i)
  have iG : Integrable G (Measure.pi I.μS) := integrable_finsetSum _ (fun j _ => gi' j)
  let proxy := fun (U : (Fin n → ℝ) → ℝ) (V : (Fin m → ℝ) → ℝ) (z : (Fin n → ℝ) × (Fin m → ℝ)) =>
    U z.1 * lamp S z.2 + lamp B z.1 * V z.2
  have ls := lamp_integrable I.μS (s := S) measurableSet_Icc
  have lb := lamp_integrable I.μB (s := B) measurableSet_Icc
  have bound {U V} (iU : Integrable U (Measure.pi I.μB)) (iV : Integrable V (Measure.pi I.μS)) :
      Integrable (proxy U V) I.law := (iU.mul_prod ls).add (lb.mul_prod iV)
  have eval {U V} (iU : Integrable U (Measure.pi I.μB)) (iV : Integrable V (Measure.pi I.μS)) :
      (∫ z, proxy U V z ∂I.law) = (∫ x, U x ∂Measure.pi I.μB) * (∫ y, lamp S y ∂Measure.pi I.μS) +
        (∫ x, lamp B x ∂Measure.pi I.μB) * (∫ y, V y ∂Measure.pi I.μS) := by
    unfold proxy DAInstance.law
    rw [integral_add (iU.mul_prod ls) (lb.mul_prod iV), integral_prod_mul, integral_prod_mul]
  let super := fun (z : (Fin n → ℝ) × (Fin m → ℝ)) =>
    if a ≤ cmin z.2 ∧ cmin z.2 ≤ p ∧ p ≤ vmax z.1 ∧ vmax z.1 ≤ b then vmax z.1 - cmin z.2 else 0
  have hsuper : Integrable super I.law := by
    have ms : MeasurableSet {z : (Fin n → ℝ) × (Fin m → ℝ) | a ≤ cmin z.2 ∧ cmin z.2 ≤ p ∧ p ≤ vmax z.1 ∧ vmax z.1 ≤ b} :=
      (measurableSet_le measurable_const (cmin_meas.comp measurable_snd)).inter
        ((measurableSet_le (cmin_meas.comp measurable_snd) measurable_const).inter
          ((measurableSet_le measurable_const (vmax_meas.comp measurable_fst)).inter (measurableSet_le (vmax_meas.comp measurable_fst) measurable_const)))
    apply Integrable.of_bound (Measurable.ite ms ((vmax_meas.comp measurable_fst).sub (cmin_meas.comp measurable_snd)) measurable_const).aestronglyMeasurable (b-a)
    filter_upwards with z
    change ‖super z‖ ≤ _
    unfold super
    split_ifs with h
    · rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (h.2.1.trans h.2.2.1))]
      linarith only [h.1,h.2.2.2]
    · simp [sub_nonneg.mpr (hap.trans hpb)]
  have upper : I.superFP a p b ≤ ∫ z, proxy F G z ∂I.law := by
    apply integral_mono hsuper (bound iF iG)
    intro z
    obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty z.1
    obtain ⟨j,_,hj⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty z.2
    change vmax z.1 = z.1 i at hi
    change cmin z.2 = z.2 j at hj
    dsimp only [super,proxy]
    split_ifs with h
    · have ei : z.1 i ∈ B := hi ▸ h.2.2
      have ej : z.2 j ∈ S := hj ▸ ⟨h.1,h.2.1⟩
      have bt : z.1 ∈ anyEligible B := Set.mem_iUnion.mpr ⟨i,ei⟩
      have st : z.2 ∈ anyEligible S := Set.mem_iUnion.mpr ⟨j,ej⟩
      have I' := Finset.single_le_sum (f := fun i => f (z.1 i)) (fun i _ => fn _) (Finset.mem_univ i)
      have J' := Finset.single_le_sum (f := fun j => g (z.2 j)) (fun j _ => gn _) (Finset.mem_univ j)
      change f (z.1 i) ≤ F z.1 at I'
      change g (z.2 j) ≤ G z.2 at J'
      rw [show f (z.1 i) = z.1 i-p from Set.indicator_of_mem ei _] at I'
      rw [show g (z.2 j) = p-z.2 j from Set.indicator_of_mem ej _] at J'
      simp only [lamp,Set.indicator_of_mem bt,Set.indicator_of_mem st,mul_one,one_mul,hi,hj]
      linarith
    · exact add_nonneg (mul_nonneg (Finset.sum_nonneg fun i _ => fn _) (Set.indicator_nonneg (fun _ _ => zero_le_one) _))
        (mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (Finset.sum_nonneg fun j _ => gn _))
  have ub := unique_integral I.μB B measurableSet_Icc hB f fb fi fn
  have us := unique_integral I.μS S measurableSet_Icc hS g gs gi gn
  have equalB : (∫ x, F x ∂Measure.pi I.μB) = ∑ i, ∫ y, f y ∂I.μB i := by
    unfold F; rw [integral_finsetSum _ (fun i _ => fi' i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [← (measurePreserving_eval I.μB i).map_eq,integral_map (measurable_pi_apply i).aemeasurable fb.aestronglyMeasurable]
  have equalS : (∫ x, G x ∂Measure.pi I.μS) = ∑ j, ∫ y, g y ∂I.μS j := by
    unfold G; rw [integral_finsetSum _ (fun j _ => gi' j)]
    apply Finset.sum_congr rfl
    intro j _
    rw [← (measurePreserving_eval I.μS j).map_eq,integral_map (measurable_pi_apply j).aemeasurable gs.aestronglyMeasurable]
  have scale : 3/4 * (∫ z, proxy F G z ∂I.law) ≤ ∫ z, proxy (uniqueWeight B f) (uniqueWeight S g) z ∂I.law := by
    rw [eval iF iG,eval ub.1 us.1,equalB,equalS]
    have hlS : 0 ≤ ∫ y, lamp S y ∂Measure.pi I.μS := integral_nonneg fun y => Set.indicator_nonneg (fun _ _ => zero_le_one) y
    have hlB : 0 ≤ ∫ x, lamp B x ∂Measure.pi I.μB := integral_nonneg fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x
    have b := mul_le_mul_of_nonneg_right ub.2 hlS
    have s := mul_le_mul_of_nonneg_left us.2 hlB
    linarith only [b,s]
  refine ((mul_le_mul_of_nonneg_left upper (by norm_num : (0:ℝ) ≤ 3/4)).trans scale).trans ?_
  apply integral_mono (bound ub.1 us.1) (gains_integrable_sets I B S measurableSet_Icc measurableSet_Icc)
  intro z
  apply Finset.le_inf'
  intro T hT
  obtain ⟨h1,h2⟩ := Finset.mem_product.mp hT
  obtain ⟨ib,cb⟩ := Finset.mem_powersetCard.mp h1
  obtain ⟨is,cs⟩ := Finset.mem_powersetCard.mp h2
  have Bnd {k l : ℕ} {s : Set ℝ} [DecidablePred (· ∈ s)] (x : Fin k → ℝ) (y : Fin l → ℝ)
      (t : Set ℝ) [DecidablePred (· ∈ t)] (w : ℝ → ℝ) (w0 : ∀ u, u ∉ s → w u = 0) (wn : ∀ u, 0 ≤ w u)
      (A : Finset (Fin k)) (iA : A ⊆ eligible s x) (size : A.card = min (eligible s x).card (eligible t y).card) :
      uniqueWeight s w x * lamp t y ≤ ∑ i ∈ A, w (x i) := by
    by_cases o : y ∈ anyEligible t
    · rw [lamp,Set.indicator_of_mem o,mul_one]
      apply unique_le_alloc x w w0 wn A iA
      intro h
      exact Finset.card_pos.mp (size ▸ lt_min h.card_pos (any_iff.mp o).card_pos)
    · simp [lamp,o,Finset.sum_nonneg (s := A) (fun j _ => wn (x j))]
  have buy := Bnd z.1 z.2 S f (fun y h => Set.indicator_of_notMem h _) fn T.1 ib cb
  have sell := Bnd z.2 z.1 B g (fun y h => Set.indicator_of_notMem h _) gn T.2 is (by simpa only [min_comm] using cs)
  have e1 : (∑ i ∈ T.1, f (z.1 i)) = ∑ i ∈ T.1, (z.1 i-p) := Finset.sum_congr rfl fun i h => Set.indicator_of_mem (Finset.mem_filter.mp (ib h)).2 _
  have e2 : (∑ j ∈ T.2, g (z.2 j)) = ∑ j ∈ T.2, (p-z.2 j) := Finset.sum_congr rfl fun j h => Set.indicator_of_mem (Finset.mem_filter.mp (is h)).2 _
  rw [e1,Finset.sum_sub_distrib] at buy
  rw [e2,Finset.sum_sub_distrib] at sell
  simp only [Finset.sum_const,nsmul_eq_mul,cb,cs] at buy sell
  unfold proxy
  linarith only [buy,sell]
end
