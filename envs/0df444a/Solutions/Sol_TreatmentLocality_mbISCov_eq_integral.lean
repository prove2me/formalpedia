-- Prove2me | solution 1 for TreatmentLocality.mbISCov_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-22T02:55:15.166113+00:00
-- url     : https://prove2.me/submissions/caaecbb6-343e-4ad0-9bd1-70be9966e9e1

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
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Definitions.Def_MarkovAsymptoticVariance

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

-- === tl_bell.lean ===
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

-- === tl_cons.lean ===


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

-- === tl_grad.lean ===
section


attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S]

/-- The plug-in system matrix factors as `Diag(N^a) · (I - γ P̂^a)`. -/
lemma mbSystem_eq_diagonal_mul (M : Model S) (v : EstInput S) (a : Bool)
    (hN : ∀ i, ∑ k, (v a).1 i k ≠ 0) :
    mbSystem M v a
      = (Matrix.diagonal fun i => ∑ k, (v a).1 i k)
          * ((1 : Matrix S S ℝ) - M.γdisc • mbTrans v a) := by
  ext i j
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [Matrix.diagonal_apply_ne _ (Ne.symm hb)])
    (fun h => absurd (Finset.mem_univ i) h)]
  rw [Matrix.diagonal_apply_eq]
  have hentry : ((1 : Matrix S S ℝ) - M.γdisc • mbTrans v a) i j
      = (if i = j then (1 : ℝ) else 0) - M.γdisc * ((v a).1 i j / ∑ k, (v a).1 i k) := by
    simp [Matrix.sub_apply, Matrix.one_apply, mbTrans, smul_eq_mul]
  have hNi : (∑ k, (v a).1 i k) ≠ 0 := hN i
  have hc : (v a).1 i j / (∑ k, (v a).1 i k) * (∑ k, (v a).1 i k) = (v a).1 i j := by
    field_simp
  have h2 : (∑ k, (v a).1 i k) * (M.γdisc * ((v a).1 i j / ∑ k, (v a).1 i k))
      = M.γdisc * (v a).1 i j := by
    calc (∑ k, (v a).1 i k) * (M.γdisc * ((v a).1 i j / ∑ k, (v a).1 i k))
        = M.γdisc * ((v a).1 i j / (∑ k, (v a).1 i k) * (∑ k, (v a).1 i k)) := by ring
      _ = M.γdisc * (v a).1 i j := by rw [hc]
  rw [mbSystem_apply, hentry, mul_sub, h2]
  congr 1
  split_ifs <;> ring

end TreatmentLocality

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S]

/-- With positive visit counts the plug-in value function solves the plug-in Bellman
system: `V̂^a = (Diag(N^a) - γ K^a)⁻¹ R^a`. -/
lemma mbValue_eq_mbSystem_inv_mulVec (M : Model S) (v : EstInput S) (a : Bool)
    (hN : ∀ i, ∑ k, (v a).1 i k ≠ 0) :
    mbValue M v a = (mbSystem M v a)⁻¹.mulVec (fun i => (v a).2 i) := by
  have hDinv : (Matrix.diagonal fun i => ∑ k, (v a).1 i k)⁻¹
      = Matrix.diagonal (fun i => (∑ k, (v a).1 i k)⁻¹) := by
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.diagonal_mul_diagonal]
    rw [show (fun i => (∑ k, (v a).1 i k) * (∑ k, (v a).1 i k)⁻¹) = (fun _ : S => (1 : ℝ)) from
      funext fun i => mul_inv_cancel₀ (hN i)]
    exact Matrix.diagonal_one
  simp only [mbValue]
  rw [mbSystem_eq_diagonal_mul M v a hN, Matrix.mul_inv_rev, hDinv, ← Matrix.mulVec_mulVec]
  congr 1
  funext i
  rw [Matrix.mulVec_diagonal]
  simp [mbReward, div_eq_inv_mul]

/-- Applying the plug-in system matrix to a vector. -/
lemma mbSystem_mulVec_apply (M : Model S) (u : EstInput S) (a : Bool) (x : S → ℝ) (i : S) :
    (mbSystem M u a).mulVec x i = ∑ j, (u a).1 i j * (x i - M.γdisc * x j) := by
  simp only [Matrix.mulVec, dotProduct, mbSystem_apply, sub_mul, mul_sub,
    Finset.sum_sub_distrib]
  congr 1
  · have hstep : ∀ j : S, (if i = j then (∑ k, (u a).1 i k) else 0) * x j
        = (if i = j then (∑ k, (u a).1 i k) * x i else 0) := by
      intro j
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    rw [Finset.sum_congr rfl (fun j _ => hstep j), Finset.sum_ite_eq]
    simp [Finset.sum_mul]
  · exact Finset.sum_congr rfl fun j _ => by ring

/-- The plug-in system matrix as a continuous linear map of the statistics. -/
noncomputable def mbSystemL (M : Model S) (a : Bool) : EstInput S →L[ℝ] Matrix S S ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => mbSystem M u a
      map_add' := by
        intro u₁ u₂
        ext i j
        simp only [mbSystem_apply, Matrix.add_apply, Pi.add_apply, Prod.fst_add,
          Finset.sum_add_distrib]
        split_ifs <;> ring
      map_smul' := by
        intro r u
        ext i j
        simp only [mbSystem_apply, Matrix.smul_apply, Pi.smul_apply, Prod.smul_fst,
          smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
        split_ifs <;> ring }

lemma mbSystemL_apply (M : Model S) (a : Bool) (u : EstInput S) :
    mbSystemL M a u = mbSystem M u a := rfl

/-- The visit count as a continuous linear functional. -/
noncomputable def visitL (a : Bool) (i : S) : EstInput S →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => ∑ k, (u a).1 i k
      map_add' := by intro u₁ u₂; simp [Finset.sum_add_distrib]
      map_smul' := by intro r u; simp [Finset.mul_sum] }

lemma visitL_apply (a : Bool) (i : S) (u : EstInput S) : visitL a i u = ∑ k, (u a).1 i k := rfl

/-- The reward statistic as a continuous linear functional. -/
noncomputable def rewardL (a : Bool) (i : S) : EstInput S →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => (u a).2 i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

lemma rewardL_apply (a : Bool) (i : S) (u : EstInput S) : rewardL a i u = (u a).2 i := rfl

/-- Reading off a matrix entry, as a continuous linear functional. -/
noncomputable def entryL (i j : S) : Matrix S S ℝ →L[ℝ] ℝ :=
  (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap

lemma entryL_apply (i j : S) (A : Matrix S S ℝ) : entryL i j A = A i j := rfl

end TreatmentLocality

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S]

/-- The derivative of the inverse plug-in system matrix, as a continuous linear map. -/
noncomputable def invDL (M : Model S) (v : EstInput S) (a : Bool) :
    EstInput S →L[ℝ] Matrix S S ℝ :=
  (-ContinuousLinearMap.mulLeftRight ℝ (Matrix S S ℝ)
    (Ring.inverse (mbSystem M v a)) (Ring.inverse (mbSystem M v a))).comp (mbSystemL M a)

lemma invDL_apply (M : Model S) (v : EstInput S) (a : Bool) (h : EstInput S) :
    invDL M v a h = -(Ring.inverse (mbSystem M v a) * mbSystem M h a
      * Ring.inverse (mbSystem M v a)) := by
  show (-ContinuousLinearMap.mulLeftRight ℝ (Matrix S S ℝ)
    (Ring.inverse (mbSystem M v a)) (Ring.inverse (mbSystem M v a))) (mbSystemL M a h) = _
  rw [ContinuousLinearMap.neg_apply, ContinuousLinearMap.mulLeftRight_apply, mbSystemL_apply]

/-- One summand of the gradient of the plug-in value function. -/
noncomputable def gradPiece (M : Model S) (v : EstInput S) (a : Bool) (s i : S) :
    EstInput S →L[ℝ] ℝ :=
  (Ring.inverse (mbSystem M v a) s i) • (rewardL a i)
    + ((v a).2 i) • ((entryL s i).comp (invDL M v a))

lemma gradPiece_apply (M : Model S) (v : EstInput S) (a : Bool) (s i : S) (h : EstInput S) :
    gradPiece M v a s i h
      = Ring.inverse (mbSystem M v a) s i * (h a).2 i
        - (v a).2 i * ((Ring.inverse (mbSystem M v a) * mbSystem M h a
            * Ring.inverse (mbSystem M v a)) s i) := by
  show (Ring.inverse (mbSystem M v a) s i) • (rewardL a i h)
    + ((v a).2 i) • ((entryL s i) (invDL M v a h)) = _
  rw [rewardL_apply, invDL_apply, entryL_apply, Matrix.neg_apply]
  simp only [smul_eq_mul]
  ring

/-- The plug-in value function is Fréchet differentiable in the statistics, with the
derivative obtained by differentiating the plug-in Bellman system. -/
theorem hasFDerivAt_mbValue (M : Model S) (v : EstInput S) (a : Bool)
    (hN : ∀ i, ∑ k, (v a).1 i k ≠ 0) (hB : IsUnit (mbSystem M v a)) (s : S) :
    HasFDerivAt (fun u : EstInput S => mbValue M u a s)
      (∑ i : S, gradPiece M v a s i) v := by
  have hsys : HasFDerivAt (fun u : EstInput S => mbSystem M u a) (mbSystemL M a) v :=
    (mbSystemL M a).hasFDerivAt
  have hDinvM : HasFDerivAt (fun u : EstInput S => Ring.inverse (mbSystem M u a))
      (invDL M v a) v := by
    have h1 := hasFDerivAt_ringInverse (𝕜 := ℝ) hB.unit
    rw [hB.unit_spec] at h1
    have h2 : ((hB.unit⁻¹ : (Matrix S S ℝ)ˣ) : Matrix S S ℝ)
        = Ring.inverse (mbSystem M v a) := by
      rw [← Ring.inverse_unit hB.unit, hB.unit_spec]
    rw [h2] at h1
    exact h1.comp v hsys
  have hEach : ∀ i : S, HasFDerivAt
      (fun u : EstInput S => Ring.inverse (mbSystem M u a) s i * (u a).2 i)
      (gradPiece M v a s i) v := by
    intro i
    have hc : HasFDerivAt (fun u : EstInput S => Ring.inverse (mbSystem M u a) s i)
        ((entryL s i).comp (invDL M v a)) v := (entryL s i).hasFDerivAt.comp v hDinvM
    have hd : HasFDerivAt (fun u : EstInput S => (u a).2 i) (rewardL a i) v :=
      (rewardL a i).hasFDerivAt
    exact hc.mul hd
  have hsum : HasFDerivAt
      (fun u : EstInput S => ∑ i : S, Ring.inverse (mbSystem M u a) s i * (u a).2 i)
      (∑ i : S, gradPiece M v a s i) v :=
    HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => hEach i)
  have hopen : ∀ᶠ u in nhds v, ∀ i : S, ∑ k, (u a).1 i k ≠ 0 := by
    rw [Filter.eventually_all]
    intro i
    have hne : visitL a i v ≠ 0 := by rw [visitL_apply]; exact hN i
    exact (visitL a i).continuous.continuousAt.eventually (eventually_ne_nhds hne)
  have heq : (fun u : EstInput S => mbValue M u a s)
      =ᶠ[nhds v] (fun u : EstInput S => ∑ i : S, Ring.inverse (mbSystem M u a) s i * (u a).2 i) := by
    filter_upwards [hopen] with u hu
    rw [mbValue_eq_mbSystem_inv_mulVec M u a hu, Matrix.nonsing_inv_eq_ringInverse]
    simp [Matrix.mulVec, dotProduct]
  exact hsum.congr_of_eventuallyEq heq

end TreatmentLocality

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S]

lemma sub_mbSystem_mulVec_mbValue (M : Model S) (v h : EstInput S) (a : Bool) :
    (fun i => (h a).2 i) - (mbSystem M h a).mulVec (mbValue M v a)
      = fun i => (h a).2 i + ∑ j, (h a).1 i j *
          (M.γdisc * mbValue M v a j - mbValue M v a i) := by
  funext i
  simp only [Pi.sub_apply, mbSystem_mulVec_apply]
  have hneg : ∀ j : S, (h a).1 i j * (M.γdisc * mbValue M v a j - mbValue M v a i)
      = -((h a).1 i j * (mbValue M v a i - M.γdisc * mbValue M v a j)) := fun j => by ring
  rw [Finset.sum_congr rfl (fun j _ => hneg j), sub_eq_add_neg]
  congr 1
  simp

/-- **The gradient of the model-based plug-in estimator**, in closed form. -/
theorem fderiv_mbValue_apply (M : Model S) (v : EstInput S) (a : Bool)
    (hN : ∀ i, ∑ k, (v a).1 i k ≠ 0) (hB : IsUnit (mbSystem M v a)) (s : S) (h : EstInput S) :
    fderiv ℝ (fun u : EstInput S => mbValue M u a s) v h
      = ((mbSystem M v a)⁻¹.mulVec (fun i =>
          (h a).2 i + ∑ j, (h a).1 i j *
            (M.γdisc * mbValue M v a j - mbValue M v a i))) s := by
  have key := hasFDerivAt_mbValue M v a hN hB s
  rw [key.fderiv, ContinuousLinearMap.sum_apply]
  have hri : Ring.inverse (mbSystem M v a) = (mbSystem M v a)⁻¹ :=
    (Matrix.nonsing_inv_eq_ringInverse _).symm
  simp only [gradPiece_apply, hri]
  set B := (mbSystem M v a)⁻¹ with hBdef
  set X := mbSystem M h a with hXdef
  rw [Finset.sum_sub_distrib]
  have e1 : ∑ i, B s i * (h a).2 i = (B.mulVec (fun i => (h a).2 i)) s := rfl
  have e2 : ∑ i, (v a).2 i * ((B * X * B) s i)
      = ((B * X * B).mulVec (fun i => (v a).2 i)) s := by
    show _ = ∑ i, (B * X * B) s i * (v a).2 i
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2]
  have e3 : (B * X * B).mulVec (fun i => (v a).2 i)
      = B.mulVec (X.mulVec (mbValue M v a)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      ← mbValue_eq_mbSystem_inv_mulVec M v a hN]
  rw [e3, ← Pi.sub_apply, ← Matrix.mulVec_sub, sub_mbSystem_mulVec_mbValue M v h a]

end TreatmentLocality

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S]

/-- **The gradient of the model-based ATE estimator**: the difference of the two arm
gradients. -/
theorem fderiv_mbATE_apply (M : Model S) (v : EstInput S)
    (hN : ∀ a i, ∑ k, (v a).1 i k ≠ 0) (hB : ∀ a, IsUnit (mbSystem M v a))
    (s : S) (h : EstInput S) :
    fderiv ℝ (fun u : EstInput S => mbATE M u s) v h
      = ((mbSystem M v true)⁻¹.mulVec (fun i =>
          (h true).2 i + ∑ j, (h true).1 i j *
            (M.γdisc * mbValue M v true j - mbValue M v true i))) s
        - ((mbSystem M v false)⁻¹.mulVec (fun i =>
          (h false).2 i + ∑ j, (h false).1 i j *
            (M.γdisc * mbValue M v false j - mbValue M v false i))) s := by
  have ht := hasFDerivAt_mbValue M v true (hN true) (hB true) s
  have hf := hasFDerivAt_mbValue M v false (hN false) (hB false) s
  have hsub : HasFDerivAt (fun u : EstInput S => mbATE M u s)
      ((∑ i : S, gradPiece M v true s i) - (∑ i : S, gradPiece M v false s i)) v := by
    have := ht.sub hf
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
    exact congrFun (mbATE_eq_mbValue M u) s
  rw [hsub.fderiv, ContinuousLinearMap.sub_apply, ← ht.fderiv, ← hf.fderiv,
    fderiv_mbValue_apply M v true (hN true) (hB true) s h,
    fderiv_mbValue_apply M v false (hN false) (hB false) s h]

end TreatmentLocality

end

-- === tl_mds.lean ===




namespace TreatmentLocality

section Aux

variable {α : Type*} [MeasurableSpace α]

lemma integrable_of_bdd (μ : Measure α) [IsFiniteMeasure μ] {f : α → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀ x, |f x| ≤ C) : Integrable f μ :=
  (integrable_const C).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hC x)

end Aux

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

/-- Integrability against the one-step experiment law, arm by arm. -/
lemma integrable_stepLaw (M : Model S) (s : S) {F : Bool × S × ℝ → ℝ} (hF : Measurable F)
    (hint : ∀ γ : Bool, Integrable (fun q : S × ℝ => F (γ, q))
      (((M.trans s (M.act γ s)).toMeasure).prod (M.reward s (M.act γ s)))) :
    Integrable F (stepLaw M s) := by
  have hintd : ∀ γ : Bool, Integrable F ((Measure.dirac γ).prod
      (((M.trans s (M.act γ s)).toMeasure).prod (M.reward s (M.act γ s)))) := by
    intro γ
    rw [Measure.dirac_prod]
    exact (integrable_map_measure hF.aestronglyMeasurable
      measurable_prodMk_left.aemeasurable).2 (hint γ)
  rw [stepLaw]
  exact Integrable.smul_measure (integrable_add_measure.mpr ⟨hintd true, hintd false⟩)
    (by norm_num)

/-- The scheme weight is measurable. -/
lemma measurable_isWeight (M : Model S) (s : S) (a : Bool) :
    Measurable (fun p : Bool × S × ℝ =>
      (if s = M.crucial then 2 * (if p.1 = a then (1 : ℝ) else 0) else 1)) := by
  by_cases hs : s = M.crucial
  · simp only [if_pos hs]
    exact (Measurable.ite (measurable_fst (measurableSet_singleton a))
      measurable_const measurable_const).const_mul 2
  · simp only [if_neg hs]; exact measurable_const

lemma isWeight_abs_le (M : Model S) (s : S) (a : Bool) (p : Bool × S × ℝ) :
    |(if s = M.crucial then 2 * (if p.1 = a then (1 : ℝ) else 0) else 1)| ≤ 2 := by
  split_ifs <;> norm_num

/-- The weighted next-state value, integrated against the step law, is `P^a` applied to
the value vector. -/
lemma integral_stepLaw_value (M : Model S) (s : S) (a : Bool) (V : S → ℝ) :
    ∫ p : Bool × S × ℝ,
        ((if s = M.crucial then 2 * (if p.1 = a then (1 : ℝ) else 0) else 1) * V p.2.1)
        ∂(stepLaw M s)
      = ∑ j, M.polTrans a s j * V j := by
  classical
  have hsplit : ∀ p : Bool × S × ℝ,
      ((if s = M.crucial then 2 * (if p.1 = a then (1 : ℝ) else 0) else 1) * V p.2.1)
        = ∑ j, V j *
          ((if s = M.crucial then 2 * (if p.1 = a then (1 : ℝ) else 0) else 1)
            * (if p.2.1 = j then (1 : ℝ) else 0)) := by
    intro p
    rw [Finset.sum_eq_single p.2.1 (fun b _ hb => by simp [Ne.symm hb])
      (fun h => absurd (Finset.mem_univ _) h)]
    simp
    ring
  have hmeas : ∀ j : S, Measurable (fun p : Bool × S × ℝ => V j *
      ((if s = M.crucial then 2 * (if p.1 = a then (1 : ℝ) else 0) else 1)
        * (if p.2.1 = j then (1 : ℝ) else 0))) := by
    intro j
    exact ((measurable_isWeight M s a).mul (Measurable.ite
      ((measurable_fst.comp measurable_snd) (measurableSet_singleton j))
      measurable_const measurable_const)).const_mul _
  have hint : ∀ j : S, Integrable (fun p : Bool × S × ℝ => V j *
      ((if s = M.crucial then 2 * (if p.1 = a then (1 : ℝ) else 0) else 1)
        * (if p.2.1 = j then (1 : ℝ) else 0))) (stepLaw M s) := by
    intro j
    refine integrable_of_bdd _ (hmeas j) (C := |V j| * 2) (fun p => ?_)
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [abs_mul]
    have h2 : |if p.2.1 = j then (1 : ℝ) else 0| ≤ 1 := by split_ifs <;> norm_num
    calc |if s = M.crucial then 2 * (if p.1 = a then (1 : ℝ) else 0) else 1|
          * |if p.2.1 = j then (1 : ℝ) else 0| ≤ 2 * 1 :=
          mul_le_mul (isWeight_abs_le M s a p) h2 (abs_nonneg _) (by norm_num)
      _ = 2 := by norm_num
  rw [integral_congr_ae (Filter.Eventually.of_forall hsplit)]
  rw [integral_finsetSum (μ := stepLaw M s)
    (f := fun (j : S) (p : Bool × S × ℝ) => V j *
      ((if s = M.crucial then 2 * (if p.1 = a then (1 : ℝ) else 0) else 1)
        * (if p.2.1 = j then (1 : ℝ) else 0))) _ (fun j _ => hint j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_stepLaw_indicator M s j a]
  rw [Model.polTrans, Matrix.of_apply]
  ring

/-- The scheme weight integrates to `1`. -/
lemma integral_stepLaw_weight (M : Model S) (s : S) (a : Bool) :
    ∫ p : Bool × S × ℝ,
        (if s = M.crucial then 2 * (if p.1 = a then (1 : ℝ) else 0) else 1) ∂(stepLaw M s)
      = 1 := by
  have h := integral_stepLaw_value M s a (fun _ => (1 : ℝ))
  simp only [mul_one] at h
  rw [h]
  exact polTrans_row_sum M a s

/-- Integrability of a function of the reward coordinate against a product law. -/
lemma integrable_prod_snd (μ : Measure S) (ρ : Measure ℝ) [IsProbabilityMeasure μ] [SFinite ρ]
    {g : ℝ → ℝ} (hg : Measurable g) (hint : Integrable g ρ) :
    Integrable (fun q : S × ℝ => g q.2) (μ.prod ρ) := by
  have h1 : (μ.prod ρ).map Prod.snd = ρ := by rw [Measure.map_snd_prod]; simp
  refine (integrable_map_measure (g := g) (f := Prod.snd) (μ := μ.prod ρ) ?_
    measurable_snd.aemeasurable).1 ?_
  · rw [h1]; exact hg.aestronglyMeasurable
  · rw [h1]; exact hint

/-- The weighted reward is integrable against the step law. -/
lemma integrable_stepLaw_rwd (M : Model S) (s : S) (a : Bool)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y)) :
    Integrable (fun p : Bool × S × ℝ =>
      (if s = M.crucial then 2 * (if p.1 = a then (1 : ℝ) else 0) else 1) * p.2.2)
      (stepLaw M s) := by
  refine integrable_stepLaw M s
    ((measurable_isWeight M s a).mul (measurable_snd.comp measurable_snd)) (fun γ => ?_)
  show Integrable (fun q : S × ℝ =>
    (if s = M.crucial then 2 * (if γ = a then (1 : ℝ) else 0) else 1) * q.2) _
  exact Integrable.const_mul
    (integrable_prod_snd ((M.trans s (M.act γ s)).toMeasure) (M.reward s (M.act γ s))
      (g := fun r : ℝ => r) measurable_id (hR s (M.act γ s))) _

/-- **The inverse-probability-weighted temporal difference, integrated against the one-step
experiment law.** -/
lemma integral_stepLaw_td (M : Model S) (s : S) (a : Bool)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y)) (V : S → ℝ) :
    ∫ p : Bool × S × ℝ,
        ((if s = M.crucial then 2 * (if p.1 = a then (1 : ℝ) else 0) else 1)
          * (p.2.2 + M.γdisc * V p.2.1 - V s)) ∂(stepLaw M s)
      = M.polReward a s + M.γdisc * (∑ j, M.polTrans a s j * V j) - V s := by
  classical
  obtain ⟨C, hC⟩ : ∃ C, ∀ j, |V j| ≤ C :=
    ⟨∑ t, |V t|, fun j => Finset.single_le_sum (fun t _ => abs_nonneg (V t)) (Finset.mem_univ j)⟩
  set W : Bool × S × ℝ → ℝ :=
    fun p => (if s = M.crucial then 2 * (if p.1 = a then (1 : ℝ) else 0) else 1) with hW
  have hWm : Measurable W := measurable_isWeight M s a
  have hWb : ∀ p, |W p| ≤ 2 := isWeight_abs_le M s a
  have h1 : Integrable (fun p : Bool × S × ℝ => W p * p.2.2) (stepLaw M s) :=
    integrable_stepLaw_rwd M s a hR
  have h2 : Integrable (fun p : Bool × S × ℝ => M.γdisc * (W p * V p.2.1)) (stepLaw M s) := by
    refine integrable_of_bdd _ ((hWm.mul
      ((measurable_of_countable V).comp (measurable_fst.comp measurable_snd))).const_mul _)
      (C := |M.γdisc| * (2 * C)) (fun p => ?_)
    rw [abs_mul, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    exact mul_le_mul (hWb p) (hC _) (abs_nonneg _) (by norm_num)
  have h3 : Integrable (fun p : Bool × S × ℝ => V s * W p) (stepLaw M s) := by
    refine integrable_of_bdd _ (hWm.const_mul _) (C := |V s| * 2) (fun p => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hWb p) (abs_nonneg _)
  have hexp : ∀ p : Bool × S × ℝ,
      W p * (p.2.2 + M.γdisc * V p.2.1 - V s)
        = (W p * p.2.2 + M.γdisc * (W p * V p.2.1)) - V s * W p := fun p => by ring
  have e1 : ∫ p : Bool × S × ℝ,
        (W p * p.2.2 + M.γdisc * (W p * V p.2.1) - V s * W p) ∂(stepLaw M s)
      = (∫ p, W p * p.2.2 ∂(stepLaw M s))
        + (∫ p, M.γdisc * (W p * V p.2.1) ∂(stepLaw M s))
        - (∫ p, V s * W p ∂(stepLaw M s)) := by
    have h12 : Integrable (fun p : Bool × S × ℝ => W p * p.2.2 + M.γdisc * (W p * V p.2.1))
        (stepLaw M s) := h1.add h2
    rw [← integral_add h1 h2, ← integral_sub h12 h3]
  rw [integral_congr_ae (Filter.Eventually.of_forall hexp), e1]
  simp only [hW]
  rw [integral_const_mul, integral_const_mul, integral_stepLaw_rwd M s a hR,
    integral_stepLaw_value M s a V, integral_stepLaw_weight M s a, mul_one]

/-- Integrability of the weighted temporal-difference error against the step law. -/
lemma integrable_stepLaw_td (M : Model S) (s : S) (a : Bool)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y)) (V : S → ℝ) :
    Integrable (fun p : Bool × S × ℝ =>
      (if s = M.crucial then 2 * (if p.1 = a then (1 : ℝ) else 0) else 1)
        * (p.2.2 + M.γdisc * V p.2.1 - V s)) (stepLaw M s) := by
  classical
  obtain ⟨C, hC⟩ : ∃ C, ∀ j, |V j| ≤ C :=
    ⟨∑ t, |V t|, fun j => Finset.single_le_sum (fun t _ => abs_nonneg (V t)) (Finset.mem_univ j)⟩
  set W : Bool × S × ℝ → ℝ :=
    fun p => (if s = M.crucial then 2 * (if p.1 = a then (1 : ℝ) else 0) else 1) with hW
  have hWm : Measurable W := measurable_isWeight M s a
  have hWb : ∀ p, |W p| ≤ 2 := isWeight_abs_le M s a
  have h1 : Integrable (fun p : Bool × S × ℝ => W p * p.2.2) (stepLaw M s) :=
    integrable_stepLaw_rwd M s a hR
  have h2 : Integrable (fun p : Bool × S × ℝ => M.γdisc * (W p * V p.2.1)) (stepLaw M s) := by
    refine integrable_of_bdd _ ((hWm.mul
      ((measurable_of_countable V).comp (measurable_fst.comp measurable_snd))).const_mul _)
      (C := |M.γdisc| * (2 * C)) (fun p => ?_)
    rw [abs_mul, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    exact mul_le_mul (hWb p) (hC _) (abs_nonneg _) (by norm_num)
  have h3 : Integrable (fun p : Bool × S × ℝ => V s * W p) (stepLaw M s) := by
    refine integrable_of_bdd _ (hWm.const_mul _) (C := |V s| * 2) (fun p => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hWb p) (abs_nonneg _)
  have h12 : Integrable (fun p : Bool × S × ℝ => W p * p.2.2 + M.γdisc * (W p * V p.2.1))
      (stepLaw M s) := h1.add h2
  refine ((h12.sub h3).congr (Filter.Eventually.of_forall fun p => ?_))
  simp only [Pi.sub_apply, hW]
  ring

end TreatmentLocality

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S]

/-- The per-step statistic contracted against the plug-in gradient vector: an
inverse-probability-weighted temporal-difference error supported at the current state. -/
lemma estObs_grad_vec (M : Model S) (v : EstInput S) (a : Bool) (z : Step S) (i : S) :
    (estObs M .IS z a).2 i + ∑ j, (estObs M .IS z a).1 i j *
        (M.γdisc * mbValue M v a j - mbValue M v a i)
      = (if Step.state z = i then (1 : ℝ) else 0) *
        (schemeWeight M .IS a z *
          (Step.rwd z + M.γdisc * mbValue M v a (Step.next z) - mbValue M v a i)) := by
  classical
  by_cases h : Step.state z = i
  · rw [if_pos h]
    have h2 : ∀ j : S, (estObs M .IS z a).1 i j
        = schemeWeight M .IS a z * (if Step.next z = j then (1 : ℝ) else 0) := by
      intro j; simp [estObs, h]
    have h1 : (estObs M .IS z a).2 i = schemeWeight M .IS a z * Step.rwd z := by
      simp [estObs, h]
    rw [h1, Finset.sum_congr rfl (fun j _ => by rw [h2 j]),
      Finset.sum_eq_single (Step.next z) (fun b _ hb => by simp [Ne.symm hb])
        (fun hc => absurd (Finset.mem_univ _) hc)]
    simp
    ring
  · rw [if_neg h]
    have h1 : (estObs M .IS z a).2 i = 0 := by simp [estObs, h]
    have h2 : ∀ j : S, (estObs M .IS z a).1 i j = 0 := by intro j; simp [estObs, h]
    rw [h1, Finset.sum_congr rfl (fun j _ => by rw [h2 j])]
    simp

/-- The arm-`a` half of the influence function of the model-based estimator. -/
lemma mulVec_estObs_grad (M : Model S) (v : EstInput S) (a : Bool) (s : S) (z : Step S) :
    ((mbSystem M v a)⁻¹.mulVec (fun i =>
        (estObs M .IS z a).2 i + ∑ j, (estObs M .IS z a).1 i j *
          (M.γdisc * mbValue M v a j - mbValue M v a i))) s
      = (mbSystem M v a)⁻¹ s (Step.state z) *
        (schemeWeight M .IS a z *
          (Step.rwd z + M.γdisc * mbValue M v a (Step.next z)
            - mbValue M v a (Step.state z))) := by
  classical
  rw [Matrix.mulVec, dotProduct,
    Finset.sum_congr rfl (fun i _ => by rw [estObs_grad_vec M v a z i]),
    Finset.sum_eq_single (Step.state z) (fun b _ hb => by simp [Ne.symm hb])
      (fun hc => absurd (Finset.mem_univ _) hc)]
  simp

/-- **The influence function of the model-based estimator**, in closed form: a difference
of inverse-probability-weighted temporal-difference errors. -/
theorem fderiv_mbATE_estObs (M : Model S) (v : EstInput S)
    (hN : ∀ a i, ∑ k, (v a).1 i k ≠ 0) (hB : ∀ a, IsUnit (mbSystem M v a))
    (s : S) (z : Step S) :
    fderiv ℝ (fun u : EstInput S => mbATE M u s) v (estObs M .IS z)
      = (mbSystem M v true)⁻¹ s (Step.state z) *
          (schemeWeight M .IS true z *
            (Step.rwd z + M.γdisc * mbValue M v true (Step.next z)
              - mbValue M v true (Step.state z)))
        - (mbSystem M v false)⁻¹ s (Step.state z) *
          (schemeWeight M .IS false z *
            (Step.rwd z + M.γdisc * mbValue M v false (Step.next z)
              - mbValue M v false (Step.state z))) := by
  rw [fderiv_mbATE_apply M v hN hB s (estObs M .IS z),
    mulVec_estObs_grad M v true s z, mulVec_estObs_grad M v false s z]

end TreatmentLocality

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

/-- **The influence weight of the true value function is centred at every state**: the
inverse-probability-weighted temporal-difference error has zero mean under the one-step
experiment law. -/
theorem integral_stepLaw_td_value (M : Model S) (s : S) (a : Bool)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y)) :
    ∫ p : Bool × S × ℝ,
        ((if s = M.crucial then 2 * (if p.1 = a then (1 : ℝ) else 0) else 1)
          * (p.2.2 + M.γdisc * M.value a p.2.1 - M.value a s)) ∂(stepLaw M s)
      = 0 := by
  rw [integral_stepLaw_td M s a hR (M.value a)]
  have h := value_bellman_apply M a s
  linarith

end TreatmentLocality

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

lemma measurable_schemeWeight (M : Model S) (a : Bool) :
    Measurable (fun z : Step S => schemeWeight M .IS a z) := by
  have hcr : MeasurableSet {z : Step S | Step.state z = M.crucial} :=
    measurable_fst (measurableSet_singleton M.crucial)
  have harm : MeasurableSet {z : Step S | Step.arm z = a} :=
    (measurable_fst.comp measurable_snd) (measurableSet_singleton a)
  exact Measurable.ite hcr
    ((Measurable.ite harm measurable_const measurable_const).const_mul 2) measurable_const

lemma meanObs_IS_visit_ne_zero (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0) (a : Bool) (i : S) :
    ∑ k, ((meanObs M .IS ν) a).1 i k ≠ 0 := by
  rw [meanObs_IS_visit M ν hinv a i]; exact hμ i

/-- At the population statistics the plug-in Bellman system is invertible. -/
theorem isUnit_mbSystem_meanObs_IS (M : Model S) (ν : Measure (Step S))
    [IsProbabilityMeasure ν] (hinv : Kernel.Invariant (expKernel M) ν)
    (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0) (a : Bool) :
    IsUnit (mbSystem M (meanObs M .IS ν) a) := by
  have hN : ∀ i, ∑ k, ((meanObs M .IS ν) a).1 i k ≠ 0 :=
    fun i => meanObs_IS_visit_ne_zero M ν hinv hμ a i
  rw [mbSystem_eq_diagonal_mul M _ a hN, mbTrans_meanObs_IS M ν hinv hμ a]
  refine IsUnit.mul ?_ (isUnit_one_sub_smul_polTrans M a)
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal]
  exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.mpr fun i _ => hN i)

/-- **The influence function of the information-sharing estimator at the population
statistics**: a difference of inverse-probability-weighted temporal-difference errors of
the *true* value functions. -/
theorem influence_eq (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y))
    (hrint : Integrable (fun z : Step S => Step.rwd z) ν)
    (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0)
    (s : S) (y : Step S) :
    fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν) (estObs M .IS y)
      = (mbSystem M (meanObs M .IS ν) true)⁻¹ s (Step.state y) *
          (schemeWeight M .IS true y * (Step.rwd y + M.γdisc * M.value true (Step.next y)
            - M.value true (Step.state y)))
        - (mbSystem M (meanObs M .IS ν) false)⁻¹ s (Step.state y) *
          (schemeWeight M .IS false y * (Step.rwd y + M.γdisc * M.value false (Step.next y)
            - M.value false (Step.state y))) := by
  rw [fderiv_mbATE_estObs M (meanObs M .IS ν)
    (fun a i => meanObs_IS_visit_ne_zero M ν hinv hμ a i)
    (fun a => isUnit_mbSystem_meanObs_IS M ν hinv hμ a) s y,
    mbValue_meanObs_IS M ν hinv hR hrint hμ true,
    mbValue_meanObs_IS M ν hinv hR hrint hμ false]

lemma measurable_influence (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y))
    (hrint : Integrable (fun z : Step S => Step.rwd z) ν)
    (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0) (s : S) :
    Measurable (fun y : Step S =>
      fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν) (estObs M .IS y)) := by
  have hst : Measurable (fun y : Step S => Step.state y) := measurable_fst
  have hnx : Measurable (fun y : Step S => Step.next y) :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hrw : Measurable (fun y : Step S => Step.rwd y) :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  have key : ∀ a : Bool, Measurable (fun y : Step S =>
      (mbSystem M (meanObs M .IS ν) a)⁻¹ s (Step.state y) *
        (schemeWeight M .IS a y * (Step.rwd y + M.γdisc * M.value a (Step.next y)
          - M.value a (Step.state y)))) := by
    intro a
    refine Measurable.mul ((measurable_of_countable _).comp hst) ?_
    exact (measurable_schemeWeight M a).mul
      ((hrw.add (((measurable_of_countable (M.value a)).comp hnx).const_mul _)).sub
        ((measurable_of_countable (M.value a)).comp hst))
  simp only [influence_eq M ν hinv hR hrint hμ s]
  exact (key true).sub (key false)

/-- **The influence function is centred under the one-step experiment law.** -/
theorem integral_stepLaw_influence_eq_zero (M : Model S) (ν : Measure (Step S))
    [IsProbabilityMeasure ν] (hinv : Kernel.Invariant (expKernel M) ν)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y))
    (hrint : Integrable (fun z : Step S => Step.rwd z) ν)
    (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0)
    (s : S) (s₀ : S) :
    ∫ p : Bool × S × ℝ,
        fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν) (estObs M .IS (s₀, p))
        ∂(stepLaw M s₀) = 0 := by
  simp only [influence_eq M ν hinv hR hrint hμ s]
  show ∫ p : Bool × S × ℝ,
      ((mbSystem M (meanObs M .IS ν) true)⁻¹ s s₀ *
          ((if s₀ = M.crucial then 2 * (if p.1 = true then (1 : ℝ) else 0) else 1)
            * (p.2.2 + M.γdisc * M.value true p.2.1 - M.value true s₀))
        - (mbSystem M (meanObs M .IS ν) false)⁻¹ s s₀ *
          ((if s₀ = M.crucial then 2 * (if p.1 = false then (1 : ℝ) else 0) else 1)
            * (p.2.2 + M.γdisc * M.value false p.2.1 - M.value false s₀)))
      ∂(stepLaw M s₀) = 0
  have hint : ∀ a : Bool, Integrable (fun p : Bool × S × ℝ =>
      (if s₀ = M.crucial then 2 * (if p.1 = a then (1 : ℝ) else 0) else 1)
        * (p.2.2 + M.γdisc * M.value a p.2.1 - M.value a s₀)) (stepLaw M s₀) :=
    fun a => integrable_stepLaw_td M s₀ a hR (M.value a)
  have hA := (hint true).const_mul ((mbSystem M (meanObs M .IS ν) true)⁻¹ s s₀)
  have hB := (hint false).const_mul ((mbSystem M (meanObs M .IS ν) false)⁻¹ s s₀)
  rw [integral_sub hA hB, integral_const_mul, integral_const_mul,
    integral_stepLaw_td_value M s₀ true hR, integral_stepLaw_td_value M s₀ false hR]
  ring

/-- **The influence function has zero conditional mean given the past**: it is a
martingale difference along the experiment chain. -/
theorem integral_influence_expKernel_eq_zero (M : Model S) (ν : Measure (Step S))
    [IsProbabilityMeasure ν] (hinv : Kernel.Invariant (expKernel M) ν)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y))
    (hrint : Integrable (fun z : Step S => Step.rwd z) ν)
    (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0)
    (s : S) (z : Step S) :
    ∫ y, fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν) (estObs M .IS y)
        ∂(expKernel M z) = 0 := by
  rw [integral_expKernel M z (measurable_influence M ν hinv hR hrint hμ s)]
  exact integral_stepLaw_influence_eq_zero M ν hinv hR hrint hμ s (Step.next z)

end TreatmentLocality

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

lemma schemeWeight_IS_abs_le (M : Model S) (a : Bool) (y : Step S) :
    |schemeWeight M .IS a y| ≤ 2 := by
  show |if Step.state y = M.crucial then 2 * (if Step.arm y = a then (1 : ℝ) else 0) else 1| ≤ 2
  split_ifs <;> norm_num

private lemma abs_sub_le_add (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  calc |x - y| = |x + -y| := by ring_nf
    _ ≤ |x| + |-y| := abs_add_le _ _
    _ = |x| + |y| := by rw [abs_neg]

/-- The influence function is integrable against any finite measure with integrable
reward coordinate. -/
theorem integrable_influence (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y))
    (hrint : Integrable (fun z : Step S => Step.rwd z) ν)
    (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0) (s : S)
    (μ : Measure (Step S)) [IsFiniteMeasure μ]
    (hr : Integrable (fun z : Step S => Step.rwd z) μ) :
    Integrable (fun y : Step S =>
      fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν) (estObs M .IS y)) μ := by
  have hst : Measurable (fun y : Step S => Step.state y) := measurable_fst
  have hnx : Measurable (fun y : Step S => Step.next y) :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hrw : Measurable (fun y : Step S => Step.rwd y) :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  have key : ∀ a : Bool, Integrable (fun y : Step S =>
      (mbSystem M (meanObs M .IS ν) a)⁻¹ s (Step.state y) *
        (schemeWeight M .IS a y * (Step.rwd y + M.γdisc * M.value a (Step.next y)
          - M.value a (Step.state y)))) μ := by
    intro a
    obtain ⟨C, hC0, hC⟩ : ∃ C, 0 ≤ C ∧ ∀ i, |(mbSystem M (meanObs M .IS ν) a)⁻¹ s i| ≤ C :=
      ⟨∑ t, |(mbSystem M (meanObs M .IS ν) a)⁻¹ s t|,
        Finset.sum_nonneg fun t _ => abs_nonneg _,
        fun i => Finset.single_le_sum
          (f := fun t => |(mbSystem M (meanObs M .IS ν) a)⁻¹ s t|)
          (fun t _ => abs_nonneg _) (Finset.mem_univ i)⟩
    obtain ⟨D, hD0, hD⟩ : ∃ D, 0 ≤ D ∧ ∀ i, |M.value a i| ≤ D :=
      ⟨∑ t, |M.value a t|, Finset.sum_nonneg fun t _ => abs_nonneg _,
        fun i => Finset.single_le_sum (f := fun t => |M.value a t|)
          (fun t _ => abs_nonneg _) (Finset.mem_univ i)⟩
    have hgm : Measurable (fun y : Step S =>
        (mbSystem M (meanObs M .IS ν) a)⁻¹ s (Step.state y) * schemeWeight M .IS a y) :=
      ((measurable_of_countable _).comp hst).mul (measurable_schemeWeight M a)
    have hgb : ∀ y : Step S, |(mbSystem M (meanObs M .IS ν) a)⁻¹ s (Step.state y)
        * schemeWeight M .IS a y| ≤ C * 2 := by
      intro y
      rw [abs_mul]
      exact mul_le_mul (hC _) (schemeWeight_IS_abs_le M a y) (abs_nonneg _) hC0
    have hhm : Measurable (fun y : Step S =>
        ((mbSystem M (meanObs M .IS ν) a)⁻¹ s (Step.state y) * schemeWeight M .IS a y)
          * (M.γdisc * M.value a (Step.next y) - M.value a (Step.state y))) :=
      hgm.mul ((((measurable_of_countable (M.value a)).comp hnx).const_mul _).sub
        ((measurable_of_countable (M.value a)).comp hst))
    have hhb : ∀ y : Step S,
        |((mbSystem M (meanObs M .IS ν) a)⁻¹ s (Step.state y) * schemeWeight M .IS a y)
          * (M.γdisc * M.value a (Step.next y) - M.value a (Step.state y))|
          ≤ (C * 2) * (|M.γdisc| * D + D) := by
      intro y
      rw [abs_mul]
      refine mul_le_mul (hgb y) ?_ (abs_nonneg _) (by positivity)
      refine (abs_sub_le_add _ _).trans ?_
      have h1 : |M.γdisc * M.value a (Step.next y)| ≤ |M.γdisc| * D := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hD _) (abs_nonneg _)
      exact add_le_add h1 (hD _)
    have e : ∀ y : Step S,
        (mbSystem M (meanObs M .IS ν) a)⁻¹ s (Step.state y) *
          (schemeWeight M .IS a y * (Step.rwd y + M.γdisc * M.value a (Step.next y)
            - M.value a (Step.state y)))
        = ((mbSystem M (meanObs M .IS ν) a)⁻¹ s (Step.state y) * schemeWeight M .IS a y)
            * Step.rwd y
          + ((mbSystem M (meanObs M .IS ν) a)⁻¹ s (Step.state y) * schemeWeight M .IS a y)
            * (M.γdisc * M.value a (Step.next y) - M.value a (Step.state y)) :=
      fun y => by ring
    refine Integrable.congr ?_ (Filter.Eventually.of_forall fun y => (e y).symm)
    exact (hr.bdd_mul hgm.aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hgb y)).add
      (integrable_of_bdd _ hhm hhb)
  simp only [influence_eq M ν hinv hR hrint hμ s]
  exact (key true).sub (key false)

/-- The influence function has mean zero under the stationary law. -/
theorem integral_influence_eq_zero (M : Model S) (ν : Measure (Step S))
    [IsProbabilityMeasure ν] (hinv : Kernel.Invariant (expKernel M) ν)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y))
    (hrint : Integrable (fun z : Step S => Step.rwd z) ν)
    (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0) (s : S) :
    ∫ y, fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν) (estObs M .IS y) ∂ν
      = 0 := by
  rw [integral_eq_integral_stepLaw M ν hinv (measurable_influence M ν hinv hR hrint hμ s)
    (integrable_influence M ν hinv hR hrint hμ s ν hrint)]
  rw [integral_congr_ae (Filter.Eventually.of_forall fun z =>
    integral_stepLaw_influence_eq_zero M ν hinv hR hrint hμ s (Step.state z))]
  simp

end TreatmentLocality

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

/-- The conditional expectation of the influence function at any positive lag vanishes. -/
theorem integral_iterKernel_influence (M : Model S) (ν : Measure (Step S))
    [IsProbabilityMeasure ν] (hinv : Kernel.Invariant (expKernel M) ν)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y))
    (hrint : Integrable (fun z : Step S => Step.rwd z) ν)
    (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0)
    (hiter : ∀ (k : ℕ) (x : Step S), Integrable (fun z : Step S => Step.rwd z)
      (MarkovChainCLT.iterKernel (expKernel M) k x))
    (s : S) (k : ℕ) (x : Step S) :
    ∫ y, fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν) (estObs M .IS y)
        ∂(MarkovChainCLT.iterKernel (expKernel M) (k + 1) x) = 0 := by
  have hI : Integrable (fun y : Step S =>
      fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν) (estObs M .IS y))
      (MarkovChainCLT.iterKernel (expKernel M) (k + 1) x) :=
    integrable_influence M ν hinv hR hrint hμ s _ (hiter (k + 1) x)
  rw [MarkovChainCLT.iterKernel_succ] at hI ⊢
  rw [Kernel.integral_comp hI]
  simp only [integral_influence_expKernel_eq_zero M ν hinv hR hrint hμ s]
  simp

/-- **All lagged autocovariances of the influence function vanish.** -/
theorem lagCovariance_influence_succ (M : Model S) (ν : Measure (Step S))
    [IsProbabilityMeasure ν] (hinv : Kernel.Invariant (expKernel M) ν)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y))
    (hrint : Integrable (fun z : Step S => Step.rwd z) ν)
    (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0)
    (hiter : ∀ (k : ℕ) (x : Step S), Integrable (fun z : Step S => Step.rwd z)
      (MarkovChainCLT.iterKernel (expKernel M) k x))
    (s s' : S) (k : ℕ) :
    MarkovChainCLT.lagCovariance (expKernel M) ν
      (fun z => fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν)
        (estObs M .IS z))
      (fun z => fderiv ℝ (fun u : EstInput S => mbATE M u s') (meanObs M .IS ν)
        (estObs M .IS z)) (k + 1) = 0 := by
  rw [MarkovChainCLT.lagCovariance]
  have hz : ∀ x : Step S,
      (fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν) (estObs M .IS x)
          - ∫ y, fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν)
              (estObs M .IS y) ∂ν)
        * ((∫ y, fderiv ℝ (fun u : EstInput S => mbATE M u s') (meanObs M .IS ν)
              (estObs M .IS y) ∂(MarkovChainCLT.iterKernel (expKernel M) (k + 1) x))
          - ∫ y, fderiv ℝ (fun u : EstInput S => mbATE M u s') (meanObs M .IS ν)
              (estObs M .IS y) ∂ν) = 0 := by
    intro x
    rw [integral_iterKernel_influence M ν hinv hR hrint hμ hiter s' k x,
      integral_influence_eq_zero M ν hinv hR hrint hμ s']
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hz)]
  simp

/-- **The asymptotic covariance of the information-sharing estimator is instantaneous.**
Because the influence function is a martingale difference along the experiment chain, the
lagged terms of `Σ_IS` all vanish and only the one-step covariance survives. -/
theorem mbISCov_eq_integral_aux (M : Model S) (ν : Measure (Step S))
    [IsProbabilityMeasure ν] (hinv : Kernel.Invariant (expKernel M) ν)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y))
    (hrint : Integrable (fun z : Step S => Step.rwd z) ν)
    (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0)
    (hiter : ∀ (k : ℕ) (x : Step S), Integrable (fun z : Step S => Step.rwd z)
      (MarkovChainCLT.iterKernel (expKernel M) k x))
    (s s' : S) :
    mbISCov M ν s s'
      = ∫ z, (fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν)
                (estObs M .IS z))
            * (fderiv ℝ (fun u : EstInput S => mbATE M u s') (meanObs M .IS ν)
                (estObs M .IS z)) ∂ν := by
  rw [mbISCov, Matrix.of_apply, MarkovChainCLT.asymptoticCovariance,
    tsum_congr (fun k => lagCovariance_influence_succ M ν hinv hR hrint hμ hiter s s' k),
    tsum_congr (fun k => lagCovariance_influence_succ M ν hinv hR hrint hμ hiter s' s k),
    tsum_zero, add_zero, add_zero, MarkovChainCLT.lagCovariance]
  have hdir : ∀ x : Step S,
      ∫ y, fderiv ℝ (fun u : EstInput S => mbATE M u s') (meanObs M .IS ν) (estObs M .IS y)
          ∂(MarkovChainCLT.iterKernel (expKernel M) 0 x)
        = fderiv ℝ (fun u : EstInput S => mbATE M u s') (meanObs M .IS ν) (estObs M .IS x) := by
    intro x
    rw [MarkovChainCLT.iterKernel_zero, Kernel.id_apply]
    exact integral_dirac' _ x (measurable_influence M ν hinv hR hrint hμ s').stronglyMeasurable
  have e : ∀ x : Step S,
      (fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν) (estObs M .IS x)
          - ∫ y, fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν)
              (estObs M .IS y) ∂ν)
        * ((∫ y, fderiv ℝ (fun u : EstInput S => mbATE M u s') (meanObs M .IS ν)
              (estObs M .IS y) ∂(MarkovChainCLT.iterKernel (expKernel M) 0 x))
          - ∫ y, fderiv ℝ (fun u : EstInput S => mbATE M u s') (meanObs M .IS ν)
              (estObs M .IS y) ∂ν)
        = (fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν) (estObs M .IS x))
          * (fderiv ℝ (fun u : EstInput S => mbATE M u s') (meanObs M .IS ν)
              (estObs M .IS x)) := by
    intro x
    rw [hdir x, integral_influence_eq_zero M ν hinv hR hrint hμ s,
      integral_influence_eq_zero M ν hinv hR hrint hμ s']
    ring
  exact integral_congr_ae (Filter.Eventually.of_forall e)

end TreatmentLocality


open TreatmentLocality in
theorem solution {S : Type*} [DecidableEq S] [Fintype S]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y))
    (hrint : Integrable (fun z : Step S => Step.rwd z) ν)
    (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0)
    (hiter : ∀ (k : ℕ) (x : Step S), Integrable (fun z : Step S => Step.rwd z)
      (MarkovChainCLT.iterKernel (expKernel M) k x))
    (s s' : S) :
    mbISCov M ν s s'
      = ∫ z, (fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν)
                (estObs M .IS z))
            * (fderiv ℝ (fun u : EstInput S => mbATE M u s') (meanObs M .IS ν)
                (estObs M .IS z)) ∂ν :=
  TreatmentLocality.mbISCov_eq_integral_aux M ν hinv hR hrint hμ hiter s s'
