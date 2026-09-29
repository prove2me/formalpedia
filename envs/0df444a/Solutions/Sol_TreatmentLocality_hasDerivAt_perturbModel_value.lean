-- Prove2me | solution 1 for TreatmentLocality.hasDerivAt_perturbModel_value
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-22T14:57:12.15386+00:00
-- url     : https://prove2.me/submissions/ef3dfc0e-6078-4931-86eb-c93380777a34

import Definitions.Def_TreatmentLocality
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Definitions.Def_TreatmentLocalityPlugIn
import Mathlib.Probability.Kernel.Invariance
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_TreatmentLocalityPerturbation
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Ring.Units

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

section




attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S]

lemma polTrans_nonneg (M : Model S) (a : Bool) (i j : S) : 0 ≤ M.polTrans a i j :=
  ENNReal.toReal_nonneg

lemma polTrans_row_sum (M : Model S) (a : Bool) (i : S) : ∑ j, M.polTrans a i j = 1 := by
  have h1 : ∀ j : S, (M.trans i (M.act a i)) j ≠ ⊤ := fun j => PMF.apply_ne_top _ _
  have h2 : ∑ j, (M.trans i (M.act a i)) j = 1 := by
    have := (M.trans i (M.act a i)).tsum_coe
    rwa [tsum_fintype] at this
  simp only [Model.polTrans, Matrix.of_apply]
  rw [← ENNReal.toReal_sum (fun j _ => h1 j), h2, ENNReal.toReal_one]

/-- The discounted transition matrix is a strict contraction in the `L∞` operator norm. -/
lemma norm_smul_polTrans_lt_one (M : Model S) (a : Bool) :
    ‖M.γdisc • M.polTrans a‖ < 1 := by
  have hrow : ∀ i : S, ((∑ j, ‖(M.γdisc • M.polTrans a) i j‖₊ : ℝ≥0) : ℝ) ≤ M.γdisc := by
    intro i
    rw [NNReal.coe_sum]
    have hcalc : ∀ j ∈ (Finset.univ : Finset S),
        ((‖(M.γdisc • M.polTrans a) i j‖₊ : ℝ≥0) : ℝ) = M.γdisc * M.polTrans a i j := by
      intro j _
      simp only [coe_nnnorm, Matrix.smul_apply, smul_eq_mul, Real.norm_eq_abs]
      exact abs_of_nonneg (mul_nonneg M.γdisc_nonneg (polTrans_nonneg M a i j))
    rw [Finset.sum_congr rfl hcalc, ← Finset.mul_sum, polTrans_row_sum M a i, mul_one]
  have hg : (Finset.univ : Finset S).sup
      (fun i => ∑ j, ‖(M.γdisc • M.polTrans a) i j‖₊)
      ≤ (⟨M.γdisc, M.γdisc_nonneg⟩ : ℝ≥0) :=
    Finset.sup_le fun i _ => NNReal.coe_le_coe.mp (hrow i)
  have hle : ‖M.γdisc • M.polTrans a‖ ≤ M.γdisc := by
    rw [Matrix.linfty_opNorm_def]
    calc (((Finset.univ : Finset S).sup
            fun i => ∑ j, ‖(M.γdisc • M.polTrans a) i j‖₊ : ℝ≥0) : ℝ)
        ≤ ((⟨M.γdisc, M.γdisc_nonneg⟩ : ℝ≥0) : ℝ) := NNReal.coe_le_coe.mpr hg
      _ = M.γdisc := rfl
  exact lt_of_le_of_lt hle M.γdisc_lt_one

/-- **The Bellman system is invertible.** -/
theorem isUnit_one_sub_smul_polTrans (M : Model S) (a : Bool) :
    IsUnit ((1 : Matrix S S ℝ) - M.γdisc • M.polTrans a) :=
  isUnit_one_sub_of_norm_lt_one (norm_smul_polTrans_lt_one M a)

/-- **The Bellman equation** `V^a = r^a + γ P^a V^a`. -/
theorem value_bellman (M : Model S) (a : Bool) :
    M.value a = M.polReward a + M.γdisc • (M.polTrans a).mulVec (M.value a) := by
  have hdet : IsUnit ((1 : Matrix S S ℝ) - M.γdisc • M.polTrans a).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_one_sub_smul_polTrans M a)
  have hmul : ((1 : Matrix S S ℝ) - M.γdisc • M.polTrans a) *
      ((1 : Matrix S S ℝ) - M.γdisc • M.polTrans a)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hdet
  have h : ((1 : Matrix S S ℝ) - M.γdisc • M.polTrans a).mulVec (M.value a)
      = M.polReward a := by
    rw [Model.value, Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]
  have h2 : M.value a - M.γdisc • (M.polTrans a).mulVec (M.value a) = M.polReward a := by
    rw [← h, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  exact sub_eq_iff_eq_add.mp h2

/-- The Bellman equation, in coordinates. -/
theorem value_bellman_apply (M : Model S) (a : Bool) (s : S) :
    M.value a s = M.polReward a s + M.γdisc * ∑ j, M.polTrans a s j * M.value a j := by
  have h := congrFun (value_bellman M a) s
  simpa [Matrix.mulVec, dotProduct] using h

end TreatmentLocality

end



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

end TreatmentLocality

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

lemma perturbCoef_nonneg (M : Model S) (β : S → Bool → S → ℝ) (t : ℝ)
    (ht : ∀ s a j, 0 ≤ 1 + t * β s a j) (s : S) (a : Bool) (j : S) :
    0 ≤ perturbCoef M β t s a j := by
  rw [perturbCoef]
  split_ifs
  · exact mul_nonneg ENNReal.toReal_nonneg (ht s a j)
  · exact ENNReal.toReal_nonneg

lemma perturbCoef_sum (M : Model S) (β : S → Bool → S → ℝ) (t : ℝ)
    (hcent : ∀ (s : S) (γ : Bool),
      ∑ j, (M.trans s (M.act γ s) j).toReal * β s (M.act γ s) j = 0)
    (s : S) (a : Bool) : ∑ j, perturbCoef M β t s a j = 1 := by
  simp only [perturbCoef]
  by_cases hact : M.act a s = a
  · simp only [if_pos hact]
    have hterm : ∀ j : S, (M.trans s a j).toReal * (1 + t * β s a j)
        = (M.trans s a j).toReal + t * ((M.trans s a j).toReal * β s a j) := fun j => by ring
    rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib, ← Finset.mul_sum]
    have h0 : ∑ j, (M.trans s a j).toReal * β s a j = 0 := by
      have := hcent s a
      rwa [hact] at this
    rw [h0, pmf_sum_toReal (M.trans s a), mul_zero, add_zero]
  · simp only [if_neg hact]
    exact pmf_sum_toReal (M.trans s a)

lemma perturbTrans_eq (M : Model S) (β : S → Bool → S → ℝ) (t : ℝ)
    (hcent : ∀ (s : S) (γ : Bool),
      ∑ j, (M.trans s (M.act γ s) j).toReal * β s (M.act γ s) j = 0)
    (ht : ∀ s a j, 0 ≤ 1 + t * β s a j) (s : S) (a : Bool) (j : S) :
    perturbTrans M β t s a j = ENNReal.ofReal (perturbCoef M β t s a j) := by
  have hsum : (∑ j, ENNReal.ofReal (perturbCoef M β t s a j)) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => perturbCoef_nonneg M β t ht s a j),
      perturbCoef_sum M β t hcent s a, ENNReal.ofReal_one]
  rw [perturbTrans, dif_pos hsum, PMF.ofFintype_apply]

/-- The perturbed transitions are strictly positive whenever the original ones are. -/
theorem perturbTrans_pos (M : Model S) (β : S → Bool → S → ℝ) (t : ℝ)
    (hcent : ∀ (s : S) (γ : Bool),
      ∑ j, (M.trans s (M.act γ s) j).toReal * β s (M.act γ s) j = 0)
    (ht : ∀ s a j, 0 < 1 + t * β s a j)
    (hpos : ∀ s a j, 0 < M.trans s (M.act a s) j) (s : S) (a : Bool) (j : S) :
    0 < perturbTrans M β t s (M.act a s) j := by
  have ht' : ∀ s a j, 0 ≤ 1 + t * β s a j := fun s a j => (ht s a j).le
  rw [perturbTrans_eq M β t hcent ht']
  rw [ENNReal.ofReal_pos, perturbCoef]
  have hP : 0 < (M.trans s (M.act a s) j).toReal := by
    refine ENNReal.toReal_pos (ne_of_gt (hpos s a j)) ?_
    exact PMF.apply_ne_top _ _
  split_ifs
  · exact mul_pos hP (ht s (M.act a s) j)
  · exact hP

/-- For small perturbations the transition weights stay positive. -/
theorem exists_perturb_radius (β : S → Bool → S → ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε → ∀ s a j, 0 < 1 + t * β s a j := by
  classical
  obtain ⟨B, hB0, hB⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ s a j, |β s a j| ≤ B :=
    ⟨∑ x : S, ∑ b : Bool, ∑ y : S, |β x b y|,
      Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun b _ =>
        Finset.sum_nonneg fun y _ => abs_nonneg _,
      fun s a j => by
        refine le_trans ?_ (Finset.single_le_sum
          (f := fun x : S => ∑ b : Bool, ∑ y : S, |β x b y|)
          (fun x _ => Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun y _ => abs_nonneg _)
          (Finset.mem_univ s))
        refine le_trans ?_ (Finset.single_le_sum
          (f := fun b : Bool => ∑ y : S, |β s b y|)
          (fun b _ => Finset.sum_nonneg fun y _ => abs_nonneg _) (Finset.mem_univ a))
        exact Finset.single_le_sum (f := fun y : S => |β s a y|)
          (fun y _ => abs_nonneg _) (Finset.mem_univ j)⟩
  refine ⟨(B + 1)⁻¹, by positivity, fun t htlt s a j => ?_⟩
  have hbd : |t * β s a j| < 1 := by
    rw [abs_mul]
    calc |t| * |β s a j| ≤ |t| * B := mul_le_mul_of_nonneg_left (hB s a j) (abs_nonneg _)
      _ ≤ |t| * (B + 1) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      _ < (B + 1)⁻¹ * (B + 1) := mul_lt_mul_of_pos_right htlt (by positivity)
      _ = 1 := inv_mul_cancel₀ (by positivity)
  have := abs_lt.1 hbd
  linarith [this.1]

end TreatmentLocality

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

/-- **The perturbation stays inside the SST family.** For all small enough `t` the
perturbed model has the same crucial state, discount factor and reward variances, keeps
strictly positive transitions, and its transition weights are the explicit perturbed
weights. -/
theorem perturbModel_isSST (M : Model S) (m : S → Bool → ℝ) (v : S → Bool → ℝ≥0)
    (α : S → Bool → ℝ) (β : S → Bool → S → ℝ)
    (hcent : ∀ (s : S) (γ : Bool),
      ∑ j, (M.trans s (M.act γ s) j).toReal * β s (M.act γ s) j = 0)
    (hpos : ∀ s a j, 0 < M.trans s (M.act a s) j) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε →
      (perturbModel M m v α β t).crucial = M.crucial ∧
      (perturbModel M m v α β t).γdisc = M.γdisc ∧
      (perturbModel M m v α β t).GaussianRewards
        (fun s a => m s a + t * α s a * (v s a : ℝ)) v ∧
      (∀ s a j, 0 < (perturbModel M m v α β t).trans s
        ((perturbModel M m v α β t).act a s) j) ∧
      (∀ s a j, ((perturbModel M m v α β t).trans s a j).toReal
        = perturbCoef M β t s a j) := by
  obtain ⟨ε, hε0, hε⟩ := exists_perturb_radius (S := S) β
  refine ⟨ε, hε0, fun t ht => ⟨rfl, rfl, perturbModel_gaussianRewards M m v α β t,
    fun s a j => perturbTrans_pos M β t hcent (hε t ht) hpos s a j, fun s a j => ?_⟩⟩
  rw [show (perturbModel M m v α β t).trans = perturbTrans M β t from rfl,
    perturbTrans_eq M β t hcent (fun s a j => (hε t ht s a j).le),
    ENNReal.toReal_ofReal (perturbCoef_nonneg M β t (fun s a j => (hε t ht s a j).le) s a j)]

end TreatmentLocality

section




attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

lemma act_idem (M : Model S) (a : Bool) (s : S) : M.act (M.act a s) s = M.act a s := by
  cases a <;> simp [Model.act]

/-- The derivative of the transition matrix along the perturbation. -/
noncomputable def dTrans (M : Model S) (β : S → Bool → S → ℝ) (a : Bool) : Matrix S S ℝ :=
  Matrix.of fun i j => M.polTrans a i j * β i (M.act a i) j

/-- The derivative of the mean-reward vector along the perturbation. -/
noncomputable def dReward (M : Model S) (v : S → Bool → ℝ≥0) (α : S → Bool → ℝ) (a : Bool) :
    S → ℝ := fun i => α i (M.act a i) * (v i (M.act a i) : ℝ)

lemma perturbModel_polTrans (M : Model S) (m : S → Bool → ℝ) (v : S → Bool → ℝ≥0)
    (α : S → Bool → ℝ) (β : S → Bool → S → ℝ)
    (hcent : ∀ (s : S) (γ : Bool),
      ∑ j, (M.trans s (M.act γ s) j).toReal * β s (M.act γ s) j = 0)
    {t : ℝ} (ht : ∀ s a j, 0 ≤ 1 + t * β s a j) (a : Bool) :
    (perturbModel M m v α β t).polTrans a = M.polTrans a + t • dTrans M β a := by
  ext i j
  have hact : M.act (M.act a i) i = M.act a i := act_idem M a i
  rw [Model.polTrans, Matrix.of_apply,
    show (perturbModel M m v α β t).act a i = M.act a i from rfl,
    show (perturbModel M m v α β t).trans = perturbTrans M β t from rfl,
    perturbTrans_eq M β t hcent ht,
    ENNReal.toReal_ofReal (perturbCoef_nonneg M β t ht i (M.act a i) j), perturbCoef,
    if_pos hact]
  simp only [Matrix.add_apply, Matrix.smul_apply, dTrans, Matrix.of_apply, smul_eq_mul,
    Model.polTrans]
  ring

lemma perturbModel_polReward (M : Model S) (m : S → Bool → ℝ) (v : S → Bool → ℝ≥0)
    (α : S → Bool → ℝ) (β : S → Bool → S → ℝ) (t : ℝ) (a : Bool) (i : S) :
    (perturbModel M m v α β t).polReward a i
      = m i (M.act a i) + t * (dReward M v α a i) := by
  rw [Model.polReward, show (perturbModel M m v α β t).act a i = M.act a i from rfl,
    show (perturbModel M m v α β t).reward = fun s b =>
      gaussianReal (m s b + t * α s b * (v s b : ℝ)) (v s b) from rfl]
  rw [integral_id_gaussianReal]
  rw [dReward]
  ring

lemma polReward_zero (M : Model S) (m : S → Bool → ℝ) (v : S → Bool → ℝ≥0)
    (hgauss : M.GaussianRewards m v) (a : Bool) (i : S) :
    M.polReward a i = m i (M.act a i) := by
  rw [Model.polReward, hgauss i (M.act a i), integral_id_gaussianReal]

end TreatmentLocality

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

/-- The entry map of a matrix, as a continuous linear map. -/
noncomputable def entryCLM (i j : S) : Matrix S S ℝ →L[ℝ] ℝ :=
  (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap

@[simp] lemma entryCLM_apply (i j : S) (A : Matrix S S ℝ) : entryCLM i j A = A i j := rfl

/-- **The derivative of the policy value along the perturbation.** -/
theorem hasDerivAt_perturbModel_value_aux (M : Model S) (m : S → Bool → ℝ) (v : S → Bool → ℝ≥0)
    (hgauss : M.GaussianRewards m v) (α : S → Bool → ℝ) (β : S → Bool → S → ℝ)
    (hcent : ∀ (s : S) (γ : Bool),
      ∑ j, (M.trans s (M.act γ s) j).toReal * β s (M.act γ s) j = 0)
    (a : Bool) (s : S) :
    HasDerivAt (fun t : ℝ => (perturbModel M m v α β t).value a s)
      ((((1 : Matrix S S ℝ) - M.γdisc • M.polTrans a)⁻¹).mulVec
        (fun i => dReward M v α a i
          + M.γdisc * ((dTrans M β a).mulVec (M.value a) i)) s) 0 := by
  classical
  set A0 : Matrix S S ℝ := (1 : Matrix S S ℝ) - M.γdisc • M.polTrans a with hA0def
  set B : Matrix S S ℝ := -(M.γdisc • dTrans M β a) with hBdef
  set Ai : Matrix S S ℝ := A0⁻¹ with hAidef
  set A : ℝ → Matrix S S ℝ := fun t => A0 + t • B with hAdef
  set r : ℝ → S → ℝ := fun t i => m i (M.act a i) + t * dReward M v α a i with hrdef
  have hu : IsUnit A0 := isUnit_one_sub_smul_polTrans M a
  have hri : Ring.inverse A0 = Ai := (Matrix.nonsing_inv_eq_ringInverse A0).symm
  have hr0 : r 0 = M.polReward a := by
    funext i; rw [hrdef]; simp [polReward_zero M m v hgauss a i]
  have hV : Ai.mulVec (r 0) = M.value a := by rw [hr0, hAidef, hA0def, Model.value]
  -- the curve of matrices
  have hdA : HasDerivAt A B 0 := by
    rw [hAdef]
    have h1 : HasDerivAt (fun t : ℝ => t • B) ((1 : ℝ) • B) 0 :=
      (hasDerivAt_id (0 : ℝ)).smul_const B
    rw [one_smul] at h1
    exact h1.const_add A0
  have hA00 : A 0 = A0 := by simp [hAdef]
  -- the derivative of the inverse
  have hdinv : HasDerivAt (fun t : ℝ => Ring.inverse (A t)) (-(Ai * B * Ai)) 0 := by
    have hval : (↑hu.unit : Matrix S S ℝ) = A0 := hu.unit_spec
    have hinvval : (↑hu.unit⁻¹ : Matrix S S ℝ) = Ai := by
      rw [← Ring.inverse_unit hu.unit, hval, hri]
    have hfd := hasFDerivAt_ringInverse (𝕜 := ℝ) (R := Matrix S S ℝ) hu.unit
    rw [hinvval] at hfd
    have hpt : A 0 = (↑hu.unit : Matrix S S ℝ) := by rw [hA00, hval]
    have hfd2 : HasFDerivAt (Ring.inverse : Matrix S S ℝ → Matrix S S ℝ)
        (-(ContinuousLinearMap.mulLeftRight ℝ (Matrix S S ℝ) Ai Ai)) (A 0) := by
      rw [hpt]; exact hfd
    have hcomp := hfd2.comp_hasDerivAt (0 : ℝ) hdA
    have hval2 : (-ContinuousLinearMap.mulLeftRight ℝ (Matrix S S ℝ) Ai Ai) B
        = -(Ai * B * Ai) := by
      simp [ContinuousLinearMap.mulLeftRight_apply]
    rw [hval2] at hcomp
    exact hcomp
  -- entrywise derivatives
  have hentry : ∀ i : S, HasDerivAt (fun t : ℝ => (Ring.inverse (A t)) s i)
      ((-(Ai * B * Ai)) s i) 0 := fun i =>
    (entryCLM s i).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hdinv
  have hdr : ∀ i : S, HasDerivAt (fun t : ℝ => r t i) (dReward M v α a i) 0 := by
    intro i
    have h1 : HasDerivAt (fun t : ℝ => t * dReward M v α a i)
        (1 * dReward M v α a i) 0 := (hasDerivAt_id (0 : ℝ)).mul_const _
    simpa [hrdef] using h1.const_add (m i (M.act a i))
  have hsum0 := HasDerivAt.sum (u := (Finset.univ : Finset S))
    (fun (i : S) (_ : i ∈ Finset.univ) => (hentry i).mul (hdr i))
  have heq : (∑ i ∈ (Finset.univ : Finset S),
      (fun t : ℝ => (Ring.inverse (A t)) s i) * fun t : ℝ => r t i)
      = fun t : ℝ => ∑ i, (Ring.inverse (A t)) s i * r t i := by
    funext t; simp
  rw [heq] at hsum0
  have hsum : HasDerivAt (fun t : ℝ => ∑ i, (Ring.inverse (A t)) s i * r t i)
      (∑ i, ((-(Ai * B * Ai)) s i * r 0 i + (Ring.inverse (A 0)) s i * dReward M v α a i))
      0 := hsum0
  -- identify the derivative
  have hkey : (∑ i, ((-(Ai * B * Ai)) s i * r 0 i + (Ring.inverse (A 0)) s i
        * dReward M v α a i))
      = (Ai.mulVec (fun i => dReward M v α a i
          + M.γdisc * ((dTrans M β a).mulVec (M.value a) i)) s) := by
    rw [hA00, hri]
    have e1 : ∑ i, ((-(Ai * B * Ai)) s i * r 0 i)
        = (-(Ai * B * Ai)).mulVec (r 0) s := rfl
    have e2 : (-(Ai * B * Ai)).mulVec (r 0)
        = fun x => -(Ai.mulVec (B.mulVec (Ai.mulVec (r 0))) x) := by
      funext x
      rw [Matrix.neg_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      simp
    have e3 : B.mulVec (M.value a) = -(M.γdisc • (dTrans M β a).mulVec (M.value a)) := by
      rw [hBdef, Matrix.neg_mulVec, Matrix.smul_mulVec]
    rw [Finset.sum_add_distrib, e1, e2, hV, e3]
    simp only [Matrix.mulVec, dotProduct, Pi.neg_apply, Matrix.smul_mulVec,
      Pi.smul_apply, smul_eq_mul]
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hkey] at hsum
  -- transfer along the eventual equality
  obtain ⟨ε, hε0, hε⟩ := exists_perturb_radius (S := S) β
  have hball : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), |t| < ε := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε0] with t ht
    simpa [Real.dist_eq] using ht
  refine hsum.congr_of_eventuallyEq ?_
  · filter_upwards [hball] with t ht
    have hpos : ∀ s a j, 0 ≤ 1 + t * β s a j := fun s a j => (hε t ht s a j).le
    rw [Model.value, show (perturbModel M m v α β t).γdisc = M.γdisc from rfl,
      perturbModel_polTrans M m v α β hcent hpos a]
    have hrw : (perturbModel M m v α β t).polReward a = r t := by
      funext i
      rw [perturbModel_polReward, hrdef]
    rw [hrw]
    have hAeq : (1 : Matrix S S ℝ) - M.γdisc • (M.polTrans a + t • dTrans M β a) = A t := by
      rw [hAdef, hBdef, hA0def]
      rw [smul_add, smul_smul]
      simp [sub_add_eq_sub_sub, mul_comm]
      ring_nf
      module
    rw [hAeq, Matrix.nonsing_inv_eq_ringInverse]
    rfl

end TreatmentLocality

end


open TreatmentLocality in
theorem solution {S : Type*} [DecidableEq S]
    [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (M : Model S) (m : S → Bool → ℝ) (v : S → Bool → ℝ≥0)
    (hgauss : M.GaussianRewards m v) (α : S → Bool → ℝ) (β : S → Bool → S → ℝ)
    (hcent : ∀ (s : S) (γ : Bool),
      ∑ j, (M.trans s (M.act γ s) j).toReal * β s (M.act γ s) j = 0)
    (a : Bool) (s : S) :
    HasDerivAt (fun t : ℝ => (perturbModel M m v α β t).value a s)
      ((((1 : Matrix S S ℝ) - M.γdisc • M.polTrans a)⁻¹).mulVec
        (fun i => α i (M.act a i) * (v i (M.act a i) : ℝ)
          + M.γdisc * ∑ j, M.polTrans a i j * β i (M.act a i) j * M.value a j) s) 0 :=
  TreatmentLocality.hasDerivAt_perturbModel_value_aux M m v hgauss α β hcent a s
