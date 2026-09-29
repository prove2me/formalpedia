-- Prove2me | solution 1 for TreatmentLocality.integrable_rwd_of_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-22T03:16:00.148271+00:00
-- url     : https://prove2.me/submissions/d66e3abb-86ef-4773-8c89-2f09daf80815

import Definitions.Def_TreatmentLocalityPlugIn
import Mathlib.Probability.Kernel.Invariance
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Definitions.Def_MarkovIterKernel
import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal



namespace TreatmentLocality

section Bind

variable {α : Type*} [MeasurableSpace α]

/-- The Bochner integral against a measure pushed through a Markov kernel. -/
lemma integral_bind_eq (μ : Measure α) [IsFiniteMeasure μ] (κ : Kernel α α) [IsMarkovKernel κ]
    {f : α → ℝ} (hf : Integrable f (μ.bind κ)) :
    ∫ y, f y ∂(μ.bind κ) = ∫ x, (∫ y, f y ∂(κ x)) ∂μ := by
  have h1 : μ.bind κ = (κ ∘ₖ (Kernel.const Unit μ)) () := rfl
  rw [h1] at hf ⊢
  rw [Kernel.integral_comp hf, Kernel.const_apply]

end Bind

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

/-- The experiment kernel, evaluated. -/
lemma expKernel_apply (M : Model S) (z : Step S) :
    expKernel M z = (Measure.dirac (Step.next z)).prod (stepLaw M (Step.next z)) := by
  rw [expKernel, Kernel.prod_apply, Kernel.deterministic_apply, Kernel.comap_apply]
  rfl

/-- Integrating one experiment step. -/
lemma integral_expKernel (M : Model S) (z : Step S) {f : Step S → ℝ} (hf : Measurable f) :
    ∫ w, f w ∂(expKernel M z) = ∫ p, f (Step.next z, p) ∂(stepLaw M (Step.next z)) := by
  rw [expKernel_apply, Measure.dirac_prod,
    integral_map (measurable_prodMk_left).aemeasurable hf.aestronglyMeasurable]

/-- Under an invariant law, the current step can be resampled from the step law at its
*next* state. -/
lemma integral_stationary (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν) {f : Step S → ℝ} (hf : Measurable f)
    (hint : Integrable f ν) :
    ∫ z, f z ∂ν = ∫ z, (∫ p, f (Step.next z, p) ∂(stepLaw M (Step.next z))) ∂ν := by
  conv_lhs => rw [← hinv]
  rw [integral_bind_eq ν (expKernel M) (by rwa [hinv])]
  exact integral_congr_ae (Filter.Eventually.of_forall fun z => integral_expKernel M z hf)

/-- Under an invariant law, the current state and the next state have the same
distribution. -/
lemma integral_state_eq_integral_next (M : Model S) (ν : Measure (Step S))
    [IsProbabilityMeasure ν] (hinv : Kernel.Invariant (expKernel M) ν) (g : S → ℝ) :
    ∫ z, g (Step.state z) ∂ν = ∫ z, g (Step.next z) ∂ν := by
  have hgm : Measurable g := measurable_of_countable g
  have hfm : Measurable (fun z : Step S => g (Step.state z)) :=
    hgm.comp (measurable_fst)
  obtain ⟨C, hC⟩ : ∃ C, ∀ s, |g s| ≤ C :=
    ⟨∑ t, |g t|, fun s => Finset.single_le_sum (fun t _ => abs_nonneg (g t)) (Finset.mem_univ s)⟩
  have hint : Integrable (fun z : Step S => g (Step.state z)) ν := by
    refine (integrable_const C).mono' hfm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    simpa [Real.norm_eq_abs] using hC (Step.state z)
  have h := integral_stationary M ν hinv hfm hint
  have h2 : ∀ z : Step S,
      ∫ p : Bool × S × ℝ, g (Step.state (Step.next z, p)) ∂(stepLaw M (Step.next z))
        = g (Step.next z) := by
    intro z
    simp [Step.state]
  rw [h]
  exact integral_congr_ae (Filter.Eventually.of_forall h2)

end TreatmentLocality

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

/-- The stationary decomposition of an integral against an invariant law. -/
lemma integral_eq_integral_stepLaw (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν) {f : Step S → ℝ} (hf : Measurable f)
    (hint : Integrable f ν) :
    ∫ z, f z ∂ν = ∫ z, (∫ p, f (Step.state z, p) ∂(stepLaw M (Step.state z))) ∂ν := by
  rw [integral_stationary M ν hinv hf hint]
  exact (integral_state_eq_integral_next M ν hinv
    (fun s => ∫ p, f (s, p) ∂(stepLaw M s))).symm

/-- Integrating a function of the first coordinate against a product with a probability
measure. -/
lemma integral_prod_fst (μ : Measure S) (ρ : Measure ℝ) [SFinite μ] [IsProbabilityMeasure ρ]
    (g : S → ℝ) :
    ∫ q : S × ℝ, g q.1 ∂(μ.prod ρ) = ∫ x, g x ∂μ := by
  have h1 : (μ.prod ρ).map Prod.fst = μ := by
    rw [Measure.map_fst_prod]; simp
  calc ∫ q : S × ℝ, g q.1 ∂(μ.prod ρ)
      = ∫ x, g x ∂((μ.prod ρ).map Prod.fst) :=
        (integral_map measurable_fst.aemeasurable
          (measurable_of_countable g).aestronglyMeasurable).symm
    _ = ∫ x, g x ∂μ := by rw [h1]

/-- Integrating a function of the last coordinate against a product with a probability
measure. -/
lemma integral_prod_snd (μ : Measure S) (ρ : Measure ℝ) [IsProbabilityMeasure μ] [SFinite ρ]
    {g : ℝ → ℝ} (hg : Measurable g) :
    ∫ q : S × ℝ, g q.2 ∂(μ.prod ρ) = ∫ r, g r ∂ρ := by
  have h1 : (μ.prod ρ).map Prod.snd = ρ := by
    rw [Measure.map_snd_prod]; simp
  calc ∫ q : S × ℝ, g q.2 ∂(μ.prod ρ)
      = ∫ r, g r ∂((μ.prod ρ).map Prod.snd) :=
        (integral_map measurable_snd.aemeasurable hg.aestronglyMeasurable).symm
    _ = ∫ r, g r ∂ρ := by rw [h1]

/-- Integrating against the one-step experiment law: a fair coin between the two arms. -/
lemma integral_stepLaw (M : Model S) (s : S) {F : Bool × S × ℝ → ℝ} (hF : Measurable F)
    (hint : ∀ γ : Bool, Integrable (fun q : S × ℝ => F (γ, q))
      (((M.trans s (M.act γ s)).toMeasure).prod (M.reward s (M.act γ s)))) :
    ∫ p, F p ∂(stepLaw M s)
      = (2 : ℝ)⁻¹ *
        ((∫ q : S × ℝ, F (true, q)
            ∂(((M.trans s (M.act true s)).toMeasure).prod (M.reward s (M.act true s))))
          + (∫ q : S × ℝ, F (false, q)
            ∂(((M.trans s (M.act false s)).toMeasure).prod (M.reward s (M.act false s))))) := by
  have hmap : ∀ γ : Bool,
      ∫ p, F p ∂((Measure.dirac γ).prod
          (((M.trans s (M.act γ s)).toMeasure).prod (M.reward s (M.act γ s))))
        = ∫ q : S × ℝ, F (γ, q)
          ∂(((M.trans s (M.act γ s)).toMeasure).prod (M.reward s (M.act γ s))) := by
    intro γ
    rw [Measure.dirac_prod,
      integral_map measurable_prodMk_left.aemeasurable hF.aestronglyMeasurable]
  have hintd : ∀ γ : Bool, Integrable F ((Measure.dirac γ).prod
      (((M.trans s (M.act γ s)).toMeasure).prod (M.reward s (M.act γ s)))) := by
    intro γ
    rw [Measure.dirac_prod]
    exact (integrable_map_measure hF.aestronglyMeasurable
      measurable_prodMk_left.aemeasurable).2 (hint γ)
  rw [stepLaw, integral_smul_measure, integral_add_measure (hintd true) (hintd false),
    hmap true, hmap false]
  norm_num

end TreatmentLocality

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

/-- The inverse-probability weight of the information-sharing scheme, evaluated on the
step law, reproduces the arm-`a` transition probability. -/
lemma integral_stepLaw_indicator (M : Model S) (s j : S) (a : Bool) :
    ∫ p : Bool × S × ℝ,
        ((if s = M.crucial then 2 * (if p.1 = a then (1 : ℝ) else 0) else 1)
          * (if p.2.1 = j then (1 : ℝ) else 0)) ∂(stepLaw M s)
      = (M.trans s (M.act a s) j).toReal := by
  classical
  set F : Bool × S × ℝ → ℝ := fun p =>
    (if s = M.crucial then 2 * (if p.1 = a then (1 : ℝ) else 0) else 1)
      * (if p.2.1 = j then (1 : ℝ) else 0) with hF
  have hind1 : MeasurableSet {p : Bool × S × ℝ | p.1 = a} :=
    measurable_fst (measurableSet_singleton a)
  have hind2 : MeasurableSet {p : Bool × S × ℝ | p.2.1 = j} :=
    (measurable_fst.comp measurable_snd) (measurableSet_singleton j)
  have hFmeas : Measurable F := by
    rw [hF]
    refine Measurable.mul ?_ (Measurable.ite hind2 measurable_const measurable_const)
    by_cases hs : s = M.crucial
    · simp only [if_pos hs]
      exact (Measurable.ite hind1 measurable_const measurable_const).const_mul 2
    · simp only [if_neg hs]
      exact measurable_const
  have hbd : ∀ p, |F p| ≤ 2 := by
    intro p
    rw [hF]
    simp only [abs_mul]
    have h1 : |if s = M.crucial then 2 * (if p.1 = a then (1 : ℝ) else 0) else 1| ≤ 2 := by
      split_ifs <;> norm_num
    have h2 : |if p.2.1 = j then (1 : ℝ) else 0| ≤ 1 := by split_ifs <;> norm_num
    calc |if s = M.crucial then 2 * (if p.1 = a then (1 : ℝ) else 0) else 1|
          * |if p.2.1 = j then (1 : ℝ) else 0| ≤ 2 * 1 :=
          mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
      _ = 2 := by norm_num
  have hint : ∀ γ : Bool, Integrable (fun q : S × ℝ => F (γ, q))
      (((M.trans s (M.act γ s)).toMeasure).prod (M.reward s (M.act γ s))) := by
    intro γ
    refine (integrable_const (2 : ℝ)).mono'
      ((hFmeas.comp measurable_prodMk_left).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun q => ?_)
    simpa [Real.norm_eq_abs] using hbd (γ, q)
  rw [integral_stepLaw M s hFmeas hint]
  -- each arm contributes its own transition probability
  have hcoord : ∀ γ : Bool,
      ∫ q : S × ℝ, F (γ, q)
          ∂(((M.trans s (M.act γ s)).toMeasure).prod (M.reward s (M.act γ s)))
        = (if s = M.crucial then 2 * (if γ = a then (1 : ℝ) else 0) else 1)
          * (M.trans s (M.act γ s) j).toReal := by
    intro γ
    have : (fun q : S × ℝ => F (γ, q))
        = fun q : S × ℝ =>
          ((if s = M.crucial then 2 * (if γ = a then (1 : ℝ) else 0) else 1)
            * (if q.1 = j then (1 : ℝ) else 0)) := rfl
    rw [this, integral_prod_fst _ _
      (fun x : S => (if s = M.crucial then 2 * (if γ = a then (1 : ℝ) else 0) else 1)
        * (if x = j then (1 : ℝ) else 0)), PMF.integral_eq_sum]
    simp only [smul_eq_mul]
    rw [Finset.sum_eq_single j (fun b _ hb => by simp [hb])
      (fun h => absurd (Finset.mem_univ j) h)]
    simp
    ring
  rw [hcoord true, hcoord false]
  by_cases hs : s = M.crucial
  · subst hs
    cases a <;> simp [Model.act] <;> ring
  · simp [Model.act, hs]
    ring

end TreatmentLocality

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

lemma pmf_sum_toReal (p : PMF S) : ∑ j, (p j).toReal = 1 := by
  have h := PMF.integral_eq_sum p (fun _ : S => (1 : ℝ))
  simpa using h.symm

/-- The information-sharing weight, integrated against the step law, reproduces the
arm-`a` mean reward. -/
lemma integral_stepLaw_rwd (M : Model S) (s : S) (a : Bool)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y)) :
    ∫ p : Bool × S × ℝ,
        ((if s = M.crucial then 2 * (if p.1 = a then (1 : ℝ) else 0) else 1) * p.2.2)
        ∂(stepLaw M s)
      = M.polReward a s := by
  classical
  set F : Bool × S × ℝ → ℝ := fun p =>
    (if s = M.crucial then 2 * (if p.1 = a then (1 : ℝ) else 0) else 1) * p.2.2 with hF
  have hind1 : MeasurableSet {p : Bool × S × ℝ | p.1 = a} :=
    measurable_fst (measurableSet_singleton a)
  have hFmeas : Measurable F := by
    rw [hF]
    refine Measurable.mul ?_ (measurable_snd.comp measurable_snd)
    by_cases hs : s = M.crucial
    · simp only [if_pos hs]
      exact (Measurable.ite hind1 measurable_const measurable_const).const_mul 2
    · simp only [if_neg hs]
      exact measurable_const
  have hsnd : ∀ γ : Bool, Integrable (fun q : S × ℝ => q.2)
      (((M.trans s (M.act γ s)).toMeasure).prod (M.reward s (M.act γ s))) := by
    intro γ
    have h1 : (((M.trans s (M.act γ s)).toMeasure).prod (M.reward s (M.act γ s))).map Prod.snd
        = M.reward s (M.act γ s) := by
      rw [Measure.map_snd_prod]; simp
    refine (integrable_map_measure (g := fun r : ℝ => r) (f := Prod.snd)
      (μ := ((M.trans s (M.act γ s)).toMeasure).prod (M.reward s (M.act γ s)))
      ?_ measurable_snd.aemeasurable).1 ?_
    · rw [h1]; exact measurable_id.aestronglyMeasurable
    · rw [h1]; exact hR s (M.act γ s)
  have hint : ∀ γ : Bool, Integrable (fun q : S × ℝ => F (γ, q))
      (((M.trans s (M.act γ s)).toMeasure).prod (M.reward s (M.act γ s))) := by
    intro γ
    exact (hsnd γ).const_mul
      (if s = M.crucial then 2 * (if γ = a then (1 : ℝ) else 0) else 1)
  rw [integral_stepLaw M s hFmeas hint]
  have hcoord : ∀ γ : Bool,
      ∫ q : S × ℝ, F (γ, q)
          ∂(((M.trans s (M.act γ s)).toMeasure).prod (M.reward s (M.act γ s)))
        = (if s = M.crucial then 2 * (if γ = a then (1 : ℝ) else 0) else 1)
          * (∫ r, r ∂(M.reward s (M.act γ s))) := by
    intro γ
    have hEq : (fun q : S × ℝ => F (γ, q))
        = fun q : S × ℝ =>
          (if s = M.crucial then 2 * (if γ = a then (1 : ℝ) else 0) else 1) * q.2 := rfl
    rw [hEq, integral_const_mul,
      integral_prod_snd _ _ (g := fun r : ℝ => r) measurable_id]
  rw [hcoord true, hcoord false, Model.polReward]
  by_cases hs : s = M.crucial
  · subst hs
    cases a <;> simp [Model.act] <;> ring
  · simp [Model.act, hs]
    ring

/-- The population transition statistic of the information-sharing scheme. -/
lemma meanObs_IS_trans (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν) (a : Bool) (i j : S) :
    (meanObs M .IS ν a).1 i j
      = (∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν) * M.polTrans a i j := by
  classical
  have hind : MeasurableSet {z : Step S | Step.state z = i} :=
    measurable_fst (measurableSet_singleton i)
  have hind2 : MeasurableSet {z : Step S | Step.next z = j} :=
    ((measurable_fst.comp measurable_snd).comp measurable_snd) (measurableSet_singleton j)
  have hindarm : MeasurableSet {z : Step S | Step.arm z = a} :=
    (measurable_fst.comp measurable_snd) (measurableSet_singleton a)
  set f : Step S → ℝ := fun z => (estObs M .IS z a).1 i j with hf
  have hfEq : ∀ z : Step S, f z
      = (if Step.state z = i then (1 : ℝ) else 0)
        * ((if Step.state z = M.crucial then 2 * (if Step.arm z = a then (1 : ℝ) else 0) else 1)
          * (if Step.next z = j then (1 : ℝ) else 0)) := by
    intro z
    rw [hf]
    simp only [estObs, schemeWeight]
    by_cases h1 : Step.state z = i <;> by_cases h2 : Step.next z = j <;>
      simp [h1, h2]
  have hfmeas : Measurable f := by
    rw [funext hfEq]
    refine Measurable.mul (Measurable.ite hind measurable_const measurable_const) ?_
    refine Measurable.mul ?_ (Measurable.ite hind2 measurable_const measurable_const)
    exact Measurable.ite (measurable_fst (measurableSet_singleton M.crucial))
      ((Measurable.ite hindarm measurable_const measurable_const).const_mul 2) measurable_const
  have hbd : ∀ z, |f z| ≤ 2 := by
    intro z
    rw [hfEq z, abs_mul, abs_mul]
    have b1 : |(if Step.state z = i then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> norm_num
    have c1 : |(if Step.state z = M.crucial then 2 * (if Step.arm z = a then (1 : ℝ) else 0)
        else 1)| ≤ 2 := by split_ifs <;> norm_num
    have c2 : |(if Step.next z = j then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> norm_num
    have hinner := mul_le_mul c1 c2 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    have houter := mul_le_mul b1 hinner (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      (by norm_num : (0 : ℝ) ≤ 1)
    linarith
  have hfint : Integrable f ν :=
    (integrable_const (2 : ℝ)).mono' hfmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hbd z)
  show ∫ z, f z ∂ν = _
  rw [integral_eq_integral_stepLaw M ν hinv hfmeas hfint]
  have hstep : ∀ z : Step S,
      ∫ p, f (Step.state z, p) ∂(stepLaw M (Step.state z))
        = (if Step.state z = i then (1 : ℝ) else 0) * M.polTrans a i j := by
    intro z
    have h1 : ∀ p : Bool × S × ℝ, f (Step.state z, p)
        = (if Step.state z = i then (1 : ℝ) else 0)
          * ((if Step.state z = M.crucial then 2 * (if p.1 = a then (1 : ℝ) else 0) else 1)
            * (if p.2.1 = j then (1 : ℝ) else 0)) := fun p => hfEq (Step.state z, p)
    rw [integral_congr_ae (Filter.Eventually.of_forall h1), integral_const_mul,
      integral_stepLaw_indicator M (Step.state z) j a]
    by_cases h : Step.state z = i
    · rw [h]; rfl
    · simp [h]
  rw [integral_congr_ae (Filter.Eventually.of_forall hstep), integral_mul_const]

end TreatmentLocality

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

/-- The population reward statistic of the information-sharing scheme. -/
lemma meanObs_IS_rwd (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y))
    (hrint : Integrable (fun z : Step S => Step.rwd z) ν) (a : Bool) (i : S) :
    (meanObs M .IS ν a).2 i
      = (∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν) * M.polReward a i := by
  classical
  have hind : MeasurableSet {z : Step S | Step.state z = i} :=
    measurable_fst (measurableSet_singleton i)
  have hindarm : MeasurableSet {z : Step S | Step.arm z = a} :=
    (measurable_fst.comp measurable_snd) (measurableSet_singleton a)
  set f : Step S → ℝ := fun z => (estObs M .IS z a).2 i with hf
  have hfEq : ∀ z : Step S, f z
      = (if Step.state z = i then (1 : ℝ) else 0)
        * ((if Step.state z = M.crucial then 2 * (if Step.arm z = a then (1 : ℝ) else 0) else 1)
          * Step.rwd z) := by
    intro z
    rw [hf]
    simp only [estObs, schemeWeight]
    by_cases h1 : Step.state z = i <;> simp [h1]
  have hrwdmeas : Measurable (fun z : Step S => Step.rwd z) :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  have hfmeas : Measurable f := by
    rw [funext hfEq]
    refine Measurable.mul (Measurable.ite hind measurable_const measurable_const) ?_
    refine Measurable.mul ?_ hrwdmeas
    exact Measurable.ite (measurable_fst (measurableSet_singleton M.crucial))
      ((Measurable.ite hindarm measurable_const measurable_const).const_mul 2) measurable_const
  have hbd : ∀ z, |f z| ≤ 2 * |Step.rwd z| := by
    intro z
    rw [hfEq z, abs_mul, abs_mul]
    have b1 : |(if Step.state z = i then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> norm_num
    have c1 : |(if Step.state z = M.crucial then 2 * (if Step.arm z = a then (1 : ℝ) else 0)
        else 1)| ≤ 2 := by split_ifs <;> norm_num
    have hinner : |(if Step.state z = M.crucial then 2 * (if Step.arm z = a then (1 : ℝ) else 0)
        else 1)| * |Step.rwd z| ≤ 2 * |Step.rwd z| :=
      mul_le_mul_of_nonneg_right c1 (abs_nonneg _)
    have houter := mul_le_mul b1 hinner (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      (by norm_num : (0 : ℝ) ≤ 1)
    linarith
  have hfint : Integrable f ν := by
    refine (hrint.abs.const_mul 2).mono' hfmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    simpa [Real.norm_eq_abs] using hbd z
  show ∫ z, f z ∂ν = _
  rw [integral_eq_integral_stepLaw M ν hinv hfmeas hfint]
  have hstep : ∀ z : Step S,
      ∫ p, f (Step.state z, p) ∂(stepLaw M (Step.state z))
        = (if Step.state z = i then (1 : ℝ) else 0) * M.polReward a i := by
    intro z
    have h1 : ∀ p : Bool × S × ℝ, f (Step.state z, p)
        = (if Step.state z = i then (1 : ℝ) else 0)
          * ((if Step.state z = M.crucial then 2 * (if p.1 = a then (1 : ℝ) else 0) else 1)
            * p.2.2) := fun p => hfEq (Step.state z, p)
    rw [integral_congr_ae (Filter.Eventually.of_forall h1), integral_const_mul,
      integral_stepLaw_rwd M (Step.state z) a hR]
    by_cases h : Step.state z = i
    · rw [h]
    · simp [h]
  rw [integral_congr_ae (Filter.Eventually.of_forall hstep), integral_mul_const]

/-- The total population count at a state is its stationary visit probability. -/
lemma meanObs_IS_visit (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν) (a : Bool) (i : S) :
    ∑ k, (meanObs M .IS ν a).1 i k
      = ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν := by
  simp_rw [meanObs_IS_trans M ν hinv a i]
  rw [← Finset.mul_sum]
  have h : ∑ k, M.polTrans a i k = 1 := pmf_sum_toReal (M.trans i (M.act a i))
  rw [h, mul_one]

/-- **Fisher consistency of the plug-in transition estimate.** -/
theorem mbTrans_meanObs_IS (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0) (a : Bool) :
    mbTrans (meanObs M .IS ν) a = M.polTrans a := by
  ext i j
  rw [mbTrans, Matrix.of_apply, meanObs_IS_trans M ν hinv a i j,
    meanObs_IS_visit M ν hinv a i]
  exact mul_div_cancel_left₀ _ (hμ i)

/-- **Fisher consistency of the plug-in reward estimate.** -/
theorem mbReward_meanObs_IS (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y))
    (hrint : Integrable (fun z : Step S => Step.rwd z) ν)
    (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0) (a : Bool) :
    mbReward (meanObs M .IS ν) a = M.polReward a := by
  funext i
  rw [mbReward, meanObs_IS_rwd M ν hinv hR hrint a i, meanObs_IS_visit M ν hinv a i]
  exact mul_div_cancel_left₀ _ (hμ i)

/-- **Fisher consistency of the model-based estimator**: at the population statistics of
the information-sharing scheme the plug-in value function is the true value function. -/
theorem mbValue_meanObs_IS (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y))
    (hrint : Integrable (fun z : Step S => Step.rwd z) ν)
    (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0) (a : Bool) :
    mbValue M (meanObs M .IS ν) a = M.value a := by
  rw [mbValue, mbTrans_meanObs_IS M ν hinv hμ a,
    mbReward_meanObs_IS M ν hinv hR hrint hμ a, Model.value]

end TreatmentLocality





namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

lemma measurable_rwd : Measurable (fun z : Step S => Step.rwd z) :=
  measurable_snd.comp (measurable_snd.comp measurable_snd)

/-- The reward coordinate under the one-step experiment law is dominated, uniformly in
the state, by the total moment over the finitely many state-action pairs. -/
lemma lintegral_stepLaw_rwd_le (M : Model S) {F : ℝ → ℝ≥0∞} (hF : Measurable F) (s : S) :
    ∫⁻ p : Bool × S × ℝ, F p.2.2 ∂(stepLaw M s)
      ≤ ∑ t : S, ∑ a : Bool, ∫⁻ r, F r ∂(M.reward t a) := by
  have hFm : Measurable (fun p : Bool × S × ℝ => F p.2.2) :=
    hF.comp (measurable_snd.comp measurable_snd)
  have harm : ∀ γ : Bool,
      ∫⁻ p : Bool × S × ℝ, F p.2.2 ∂((Measure.dirac γ).prod
          (((M.trans s (M.act γ s)).toMeasure).prod (M.reward s (M.act γ s))))
        = ∫⁻ r, F r ∂(M.reward s (M.act γ s)) := by
    intro γ
    rw [Measure.dirac_prod, lintegral_map hFm measurable_prodMk_left]
    have h1 : Measure.map Prod.snd
        (((M.trans s (M.act γ s)).toMeasure).prod (M.reward s (M.act γ s)))
        = M.reward s (M.act γ s) := by
      rw [Measure.map_snd_prod]; simp
    calc ∫⁻ q : S × ℝ, F (γ, q).2.2
            ∂(((M.trans s (M.act γ s)).toMeasure).prod (M.reward s (M.act γ s)))
        = ∫⁻ q : S × ℝ, F q.2
            ∂(((M.trans s (M.act γ s)).toMeasure).prod (M.reward s (M.act γ s))) := rfl
      _ = ∫⁻ r, F r ∂(Measure.map Prod.snd
            (((M.trans s (M.act γ s)).toMeasure).prod (M.reward s (M.act γ s)))) :=
            (lintegral_map hF measurable_snd).symm
      _ = ∫⁻ r, F r ∂(M.reward s (M.act γ s)) := by rw [h1]
  have hle : ∀ γ : Bool, ∫⁻ r, F r ∂(M.reward s (M.act γ s))
      ≤ ∑ t : S, ∑ a : Bool, ∫⁻ r, F r ∂(M.reward t a) := by
    intro γ
    calc ∫⁻ r, F r ∂(M.reward s (M.act γ s))
        ≤ ∑ a : Bool, ∫⁻ r, F r ∂(M.reward s a) :=
          Finset.single_le_sum (f := fun a : Bool => ∫⁻ r, F r ∂(M.reward s a))
            (fun a _ => bot_le) (Finset.mem_univ (M.act γ s))
      _ ≤ ∑ t : S, ∑ a : Bool, ∫⁻ r, F r ∂(M.reward t a) :=
          Finset.single_le_sum (f := fun t : S => ∑ a : Bool, ∫⁻ r, F r ∂(M.reward t a))
            (fun t _ => bot_le) (Finset.mem_univ s)
  rw [stepLaw, lintegral_smul_measure, lintegral_add_measure, harm true, harm false]
  set B := ∑ t : S, ∑ a : Bool, ∫⁻ r, F r ∂(M.reward t a) with hB
  calc (2 : ℝ≥0∞)⁻¹ * ((∫⁻ r, F r ∂(M.reward s (M.act true s)))
          + ∫⁻ r, F r ∂(M.reward s (M.act false s)))
      ≤ (2 : ℝ≥0∞)⁻¹ * (B + B) := by
        gcongr <;> [exact hle true; exact hle false]
    _ = B := by
        rw [← two_mul, ← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

end TreatmentLocality

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

/-- The same bound along the experiment kernel. -/
lemma lintegral_expKernel_rwd_le (M : Model S) {F : ℝ → ℝ≥0∞} (hF : Measurable F)
    (z : Step S) :
    ∫⁻ w : Step S, F (Step.rwd w) ∂(expKernel M z)
      ≤ ∑ t : S, ∑ a : Bool, ∫⁻ r, F r ∂(M.reward t a) := by
  have hFm : Measurable (fun w : Step S => F (Step.rwd w)) := hF.comp measurable_rwd
  rw [expKernel_apply, Measure.dirac_prod, lintegral_map hFm measurable_prodMk_left]
  exact lintegral_stepLaw_rwd_le M hF (Step.next z)

/-- The reward moment under an invariant law is bounded by the total moment over the
finitely many state-action pairs. -/
lemma lintegral_rwd_le_of_invariant (M : Model S) (ν : Measure (Step S))
    [IsProbabilityMeasure ν] (hinv : Kernel.Invariant (expKernel M) ν)
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ z, F (Step.rwd z) ∂ν ≤ ∑ t : S, ∑ a : Bool, ∫⁻ r, F r ∂(M.reward t a) := by
  have hFm : Measurable (fun w : Step S => F (Step.rwd w)) := hF.comp measurable_rwd
  conv_lhs => rw [← hinv]
  have h1 : ν.bind (expKernel M) = ((expKernel M) ∘ₖ (Kernel.const Unit ν)) () := rfl
  rw [h1, Kernel.lintegral_comp _ _ _ hFm, Kernel.const_apply]
  calc ∫⁻ z, (∫⁻ w, F (Step.rwd w) ∂(expKernel M z)) ∂ν
      ≤ ∫⁻ _z : Step S, (∑ t : S, ∑ a : Bool, ∫⁻ r, F r ∂(M.reward t a)) ∂ν :=
        lintegral_mono fun z => lintegral_expKernel_rwd_le M hF z
    _ = ∑ t : S, ∑ a : Bool, ∫⁻ r, F r ∂(M.reward t a) := by
        rw [lintegral_const, measure_univ, mul_one]

/-- The same bound along any positive number of steps of the chain. -/
lemma lintegral_iterKernel_rwd_le (M : Model S) {F : ℝ → ℝ≥0∞} (hF : Measurable F)
    (k : ℕ) (x : Step S) :
    ∫⁻ w : Step S, F (Step.rwd w) ∂(MarkovChainCLT.iterKernel (expKernel M) (k + 1) x)
      ≤ ∑ t : S, ∑ a : Bool, ∫⁻ r, F r ∂(M.reward t a) := by
  have hFm : Measurable (fun w : Step S => F (Step.rwd w)) := hF.comp measurable_rwd
  rw [MarkovChainCLT.iterKernel_succ, Kernel.lintegral_comp _ _ _ hFm]
  calc ∫⁻ y, (∫⁻ w, F (Step.rwd w) ∂(expKernel M y))
          ∂(MarkovChainCLT.iterKernel (expKernel M) k x)
      ≤ ∫⁻ _y : Step S, (∑ t : S, ∑ a : Bool, ∫⁻ r, F r ∂(M.reward t a))
          ∂(MarkovChainCLT.iterKernel (expKernel M) k x) :=
        lintegral_mono fun y => lintegral_expKernel_rwd_le M hF y
    _ = ∑ t : S, ∑ a : Bool, ∫⁻ r, F r ∂(M.reward t a) := by
        rw [lintegral_const, measure_univ, mul_one]

end TreatmentLocality

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

/-- Gaussian rewards have a first moment. -/
lemma integrable_reward_of_gaussian (M : Model S) (m : S → Bool → ℝ) (v : S → Bool → ℝ≥0)
    (hgauss : M.GaussianRewards m v) (t : S) (a : Bool) :
    Integrable (fun r : ℝ => r) (M.reward t a) := by
  rw [hgauss t a]
  exact (memLp_id_gaussianReal (μ := m t a) (v := v t a) 1).integrable le_rfl

/-- Gaussian rewards have a second moment. -/
lemma memLp_reward_of_gaussian (M : Model S) (m : S → Bool → ℝ) (v : S → Bool → ℝ≥0)
    (hgauss : M.GaussianRewards m v) (t : S) (a : Bool) :
    MemLp (fun r : ℝ => r) 2 (M.reward t a) := by
  rw [hgauss t a]
  exact memLp_id_gaussianReal (μ := m t a) (v := v t a) 2

/-- Under an invariant law the reward coordinate is integrable. -/
theorem integrable_rwd_of_invariant_aux (M : Model S) (ν : Measure (Step S))
    [IsProbabilityMeasure ν] (hinv : Kernel.Invariant (expKernel M) ν)
    (hR : ∀ t a, Integrable (fun r : ℝ => r) (M.reward t a)) :
    Integrable (fun z : Step S => Step.rwd z) ν := by
  refine ⟨measurable_rwd.aestronglyMeasurable, lt_of_le_of_lt
    (lintegral_rwd_le_of_invariant M ν hinv (F := fun r : ℝ => ‖r‖ₑ) measurable_id.enorm) ?_⟩
  exact ENNReal.sum_lt_top.2 fun t _ => ENNReal.sum_lt_top.2 fun a _ => (hR t a).2

/-- Under an invariant law the reward coordinate is square-integrable. -/
theorem memLp_rwd_of_invariant (M : Model S) (ν : Measure (Step S))
    [IsProbabilityMeasure ν] (hinv : Kernel.Invariant (expKernel M) ν)
    (hR2 : ∀ t a, MemLp (fun r : ℝ => r) 2 (M.reward t a)) :
    MemLp (fun z : Step S => Step.rwd z) 2 ν := by
  rw [memLp_two_iff_integrable_sq measurable_rwd.aestronglyMeasurable]
  refine ⟨(measurable_rwd.pow_const 2).aestronglyMeasurable, lt_of_le_of_lt
    (lintegral_rwd_le_of_invariant M ν hinv (F := fun r : ℝ => ‖r ^ 2‖ₑ)
      (measurable_id.pow_const 2).enorm) ?_⟩
  refine ENNReal.sum_lt_top.2 fun t _ => ENNReal.sum_lt_top.2 fun a _ => ?_
  exact ((memLp_two_iff_integrable_sq
    (measurable_id : Measurable fun r : ℝ => r).aestronglyMeasurable).1 (hR2 t a)).2

/-- The reward coordinate is integrable along every step of the chain. -/
theorem integrable_rwd_iterKernel (M : Model S)
    (hR : ∀ t a, Integrable (fun r : ℝ => r) (M.reward t a)) (k : ℕ) (x : Step S) :
    Integrable (fun z : Step S => Step.rwd z)
      (MarkovChainCLT.iterKernel (expKernel M) k x) := by
  cases k with
  | zero =>
      rw [MarkovChainCLT.iterKernel_zero, Kernel.id_apply]
      refine ⟨measurable_rwd.aestronglyMeasurable, ?_⟩
      have : ∫⁻ z : Step S, ‖Step.rwd z‖ₑ ∂(Measure.dirac x) = ‖Step.rwd x‖ₑ :=
        lintegral_dirac' _ measurable_rwd.enorm
      show ∫⁻ z : Step S, ‖Step.rwd z‖ₑ ∂(Measure.dirac x) < ⊤
      rw [this]
      exact enorm_lt_top
  | succ j =>
      refine ⟨measurable_rwd.aestronglyMeasurable, lt_of_le_of_lt
        (lintegral_iterKernel_rwd_le M (F := fun r : ℝ => ‖r‖ₑ) measurable_id.enorm j x) ?_⟩
      exact ENNReal.sum_lt_top.2 fun t _ => ENNReal.sum_lt_top.2 fun a _ => (hR t a).2

end TreatmentLocality

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

lemma measurableSet_state_eq (i : S) : MeasurableSet {z : Step S | Step.state z = i} :=
  measurable_fst (measurableSet_singleton i)

lemma measurableSet_next_eq (i : S) : MeasurableSet {z : Step S | Step.next z = i} :=
  (measurable_fst.comp (measurable_snd.comp measurable_snd)) (measurableSet_singleton i)

lemma expKernel_state_eq (M : Model S) (i : S) (z : Step S) :
    (expKernel M z) {w : Step S | Step.state w = i}
      = if Step.next z = i then (1 : ℝ≥0∞) else 0 := by
  have hset : {w : Step S | Step.state w = i}
      = ({i} : Set S) ×ˢ (Set.univ : Set (Bool × S × ℝ)) := by
    ext w; simp [Step.state, Set.mem_prod]
  rw [expKernel_apply, hset, Measure.prod_prod, measure_univ, mul_one,
    MeasureTheory.Measure.dirac_apply' _ (measurableSet_singleton i)]
  by_cases h : Step.next z = i <;> simp [Set.indicator, h]

lemma expKernel_next_eq (M : Model S) (i : S) (z : Step S) :
    (expKernel M z) {w : Step S | Step.next w = i}
      = (stepLaw M (Step.next z)) {p : Bool × S × ℝ | p.2.1 = i} := by
  have hset : {w : Step S | Step.next w = i}
      = (Set.univ : Set S) ×ˢ {p : Bool × S × ℝ | p.2.1 = i} := by
    ext w; simp [Step.next, Set.mem_prod]
  rw [expKernel_apply, hset, Measure.prod_prod, measure_univ, one_mul]

lemma stepLaw_next_eq_ge (M : Model S) (i s : S) :
    (2 : ℝ≥0∞)⁻¹ * M.trans s (M.act true s) i
      ≤ (stepLaw M s) {p : Bool × S × ℝ | p.2.1 = i} := by
  have hset : {p : Bool × S × ℝ | p.2.1 = i}
      = (Set.univ : Set Bool) ×ˢ (({i} : Set S) ×ˢ (Set.univ : Set ℝ)) := by
    ext p; simp [Set.mem_prod]
  have harm : ∀ γ : Bool, ((Measure.dirac γ).prod
      (((M.trans s (M.act γ s)).toMeasure).prod (M.reward s (M.act γ s))))
      {p : Bool × S × ℝ | p.2.1 = i} = M.trans s (M.act γ s) i := by
    intro γ
    rw [hset, Measure.prod_prod, Measure.prod_prod, measure_univ, measure_univ, one_mul,
      mul_one, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton i)]
  rw [stepLaw, Measure.smul_apply, Measure.add_apply, smul_eq_mul, harm true, harm false]
  exact mul_le_mul' le_rfl (le_self_add)

/-- With strictly positive transitions every state has positive stationary visit
probability. -/
theorem visit_ne_zero_of_trans_pos (M : Model S) (ν : Measure (Step S))
    [IsProbabilityMeasure ν] (hinv : Kernel.Invariant (expKernel M) ν)
    (hpos : ∀ s a j, 0 < M.trans s (M.act a s) j) (i : S) :
    ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0 := by
  classical
  have hbind : ∀ A : Set (Step S), MeasurableSet A →
      ν A = ∫⁻ z, (expKernel M z) A ∂ν := by
    intro A hA
    conv_lhs => rw [← hinv]
    exact Measure.bind_apply hA (Kernel.aemeasurable _)
  have hne : (Finset.univ : Finset S).Nonempty := ⟨i, Finset.mem_univ i⟩
  set ε : ℝ≥0∞ :=
    (2 : ℝ≥0∞)⁻¹ * Finset.univ.inf' hne (fun s => M.trans s (M.act true s) i) with hεdef
  have hε0 : 0 < ε := by
    refine ENNReal.mul_pos (by norm_num) (ne_of_gt ?_)
    exact (Finset.lt_inf'_iff hne).2 fun s _ => hpos s true i
  -- the next state hits `i` with probability at least ε
  have hnext : ε ≤ ν {z : Step S | Step.next z = i} := by
    rw [hbind _ (measurableSet_next_eq i)]
    calc ε = ∫⁻ _z : Step S, ε ∂ν := by rw [lintegral_const, measure_univ, mul_one]
      _ ≤ ∫⁻ z, (expKernel M z) {w : Step S | Step.next w = i} ∂ν := by
          refine lintegral_mono fun z => ?_
          rw [expKernel_next_eq]
          refine le_trans ?_ (stepLaw_next_eq_ge M i (Step.next z))
          exact mul_le_mul' le_rfl ((Finset.inf'_le _ (Finset.mem_univ (Step.next z))))
  -- the current state has the same law as the next state
  have hstate : ν {z : Step S | Step.state z = i} = ν {z : Step S | Step.next z = i} := by
    rw [hbind _ (measurableSet_state_eq i)]
    have : ∀ z : Step S, (expKernel M z) {w : Step S | Step.state w = i}
        = Set.indicator {z : Step S | Step.next z = i} (fun _ => (1 : ℝ≥0∞)) z := by
      intro z
      rw [expKernel_state_eq]
      by_cases h : Step.next z = i <;> simp [Set.indicator, h]
    rw [lintegral_congr this, lintegral_indicator (measurableSet_next_eq i)]
    simp
  have hpos' : ν {z : Step S | Step.state z = i} ≠ 0 := by
    rw [hstate]
    exact ne_of_gt (lt_of_lt_of_le hε0 hnext)
  have hfun : (fun z : Step S => if Step.state z = i then (1 : ℝ) else 0)
      = Set.indicator {z : Step S | Step.state z = i} (fun _ => (1 : ℝ)) := by
    funext z
    by_cases h : Step.state z = i <;> simp [Set.indicator, h]
  rw [hfun, integral_indicator_const (1 : ℝ) (measurableSet_state_eq i)]
  simp only [smul_eq_mul, mul_one, Measure.real]
  exact ENNReal.toReal_ne_zero.2 ⟨hpos', measure_ne_top _ _⟩

end TreatmentLocality


open TreatmentLocality in
theorem solution {S : Type*} [DecidableEq S] [Fintype S]
    [MeasurableSpace S] [MeasurableSingletonClass S] (M : Model S)
    (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    (hR : ∀ t a, Integrable (fun r : ℝ => r) (M.reward t a)) :
    Integrable (fun z : Step S => Step.rwd z) ν :=
  TreatmentLocality.integrable_rwd_of_invariant_aux M ν hinv hR
