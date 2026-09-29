-- Prove2me | solution 1 for TreatmentLocality.influence_tangent_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-22T03:40:05.788369+00:00
-- url     : https://prove2.me/submissions/9cdc924f-ffed-4598-b5ac-39a0f8bca39a

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
import Definitions.Def_MarkovIterKernel
import Mathlib.Probability.Distributions.Gaussian.Real
import Definitions.Def_MarkovChainPathMeasure
import Theorems.Thm_MarkovChainCLT_setIntegral_next_coord_eq
import Theorems.Thm_MarkovChainCLT_map_coord_chainMeasure
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Definitions.Def_MarkovErgodicity
import Mathlib.Probability.Martingale.Basic

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

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
theorem mbISCov_eq_integral (M : Model S) (ν : Measure (Step S))
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

-- === tl_mom.lean ===




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
theorem integrable_rwd_of_invariant (M : Model S) (ν : Measure (Step S))
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

-- === mc_l1.lean ===




namespace MarkovChainCLT

variable {X : Type*} [MeasurableSpace X]

/-- The σ-algebra generated by the coordinates `≤ k`. -/
def pathSigma (X : Type*) [MeasurableSpace X] (k : ℕ) : MeasurableSpace (ℕ → X) :=
  MeasurableSpace.comap (Preorder.frestrictLe (π := fun _ : ℕ => X) k) inferInstance

lemma pathSigma_le (k : ℕ) :
    pathSigma X k ≤ (inferInstance : MeasurableSpace (ℕ → X)) :=
  Measurable.comap_le (Preorder.measurable_frestrictLe (X := fun _ : ℕ => X) k)

lemma measurable_coord_pathSigma {i k : ℕ} (hik : i ≤ k) :
    Measurable[pathSigma X k] (fun ω : ℕ → X => ω i) := by
  have hfr : Measurable[pathSigma X k] (Preorder.frestrictLe (π := fun _ : ℕ => X) k) :=
    Measurable.of_comap_le le_rfl
  exact (measurable_pi_apply (⟨i, Finset.mem_Iic.2 hik⟩ : ↑(Finset.Iic k))).comp hfr

/-- The truncation of a real function at level `n`. -/
noncomputable def trunc (h : X → ℝ) (n : ℕ) : X → ℝ :=
  fun x => if |h x| ≤ (n : ℝ) then h x else 0

lemma measurable_trunc {h : X → ℝ} (hh : Measurable h) (n : ℕ) : Measurable (trunc h n) := by
  refine Measurable.ite ?_ hh measurable_const
  exact (hh.abs) measurableSet_Iic

lemma abs_trunc_le (h : X → ℝ) (n : ℕ) (x : X) : |trunc h n x| ≤ (n : ℝ) := by
  rw [trunc]
  split_ifs with hx
  · exact hx
  · simpa using Nat.cast_nonneg n

lemma abs_trunc_le_abs (h : X → ℝ) (n : ℕ) (x : X) : |trunc h n x| ≤ |h x| := by
  rw [trunc]
  split_ifs
  · exact le_rfl
  · simpa using abs_nonneg (h x)

lemma tendsto_trunc (h : X → ℝ) (x : X) :
    Tendsto (fun n : ℕ => trunc h n x) atTop (𝓝 (h x)) := by
  refine tendsto_atTop_of_eventually_const (i₀ := ⌈|h x|⌉₊) (fun n hn => ?_)
  have : |h x| ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (Nat.cast_le.2 hn)
  simp [trunc, this]

end MarkovChainCLT

namespace MarkovChainCLT

variable {X : Type*} [MeasurableSpace X]

lemma measurable_kernel_integral (P : Kernel X X) [IsMarkovKernel P] {g : X → ℝ}
    (hg : Measurable g) : Measurable (fun x => ∫ y, g y ∂(P x)) :=
  (StronglyMeasurable.integral_kernel (κ := P) hg.stronglyMeasurable).measurable

set_option maxHeartbeats 1000000 in
/-- **The Markov property of the path measure, for integrable observables.** -/
theorem condExp_next_coord_of_integrable (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (h : X → ℝ) (hh : Measurable h) (hint : Integrable h π) (k : ℕ) :
    (fun ω : ℕ → X => ∫ y, h y ∂(P (ω k)))
      =ᵐ[chainMeasure P π] (chainMeasure P π)[fun ω : ℕ → X => h (ω (k + 1)) |
        pathSigma X k] := by
  set μ := chainMeasure P π with hμdef
  have hm : pathSigma X k ≤ (inferInstance : MeasurableSpace (ℕ → X)) := pathSigma_le k
  have hmap : ∀ n : ℕ, Measure.map (fun ω : ℕ → X => ω n) μ = π :=
    fun n => map_coord_chainMeasure P π hinv n
  have hqmp : ∀ n : ℕ, Measure.QuasiMeasurePreserving (fun ω : ℕ → X => ω n) μ π :=
    fun n => ⟨measurable_pi_apply n, by rw [hmap n]⟩
  -- the observed coordinate is integrable
  have hf : Integrable (fun ω : ℕ → X => h (ω (k + 1))) μ := by
    have hiff := integrable_map_measure (g := h) (f := fun ω : ℕ → X => ω (k + 1)) (μ := μ)
      (by rw [hmap (k + 1)]; exact hh.aestronglyMeasurable)
      (measurable_pi_apply (k + 1)).aemeasurable
    rw [hmap (k + 1)] at hiff
    exact hiff.1 hint
  -- integrability along the kernel
  have hcomp : Integrable h (P ∘ₘ π) := by
    show Integrable h (π.bind P)
    rw [hinv]; exact hint
  obtain ⟨hae, hnorm⟩ := (Measure.integrable_comp_iff (κ := P) (μ := π) (f := h)
    (by show AEStronglyMeasurable h (π.bind P); rw [hinv]; exact hh.aestronglyMeasurable)).1 hcomp
  have haeμ : ∀ᵐ ω ∂μ, Integrable h (P (ω k)) := (hqmp k).ae hae
  have hnormm : Measurable (fun x : X => ∫ y, ‖h y‖ ∂(P x)) :=
    measurable_kernel_integral P hh.norm
  have hnormμ : Integrable (fun ω : ℕ → X => ∫ y, ‖h y‖ ∂(P (ω k))) μ := by
    have hiff := integrable_map_measure (g := fun x : X => ∫ y, ‖h y‖ ∂(P x))
      (f := fun ω : ℕ → X => ω k) (μ := μ)
      (by rw [hmap k]; exact hnormm.aestronglyMeasurable)
      (measurable_pi_apply k).aemeasurable
    rw [hmap k] at hiff
    exact hiff.1 hnorm
  have hgm : Measurable (fun x : X => ∫ y, h y ∂(P x)) := measurable_kernel_integral P hh
  have hgint : Integrable (fun ω : ℕ → X => ∫ y, h y ∂(P (ω k))) μ := by
    refine hnormμ.mono' ((hgm.comp (measurable_pi_apply k)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    exact norm_integral_le_integral_norm _
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hf (fun s _ _ => hgint.integrableOn) ?_ ?_
  · rintro s ⟨A₀, hA₀, rfl⟩ -
    set T := (Preorder.frestrictLe (π := fun _ : ℕ => X) k) ⁻¹' A₀ with hT
    have key : ∀ n : ℕ,
        ∫ ω in T, trunc h n (ω (k + 1)) ∂μ
          = ∫ ω in T, (∫ y, trunc h n y ∂(P (ω k))) ∂μ :=
      fun n => setIntegral_next_coord_eq P π (trunc h n) (measurable_trunc hh n) (n : ℝ)
        (abs_trunc_le h n) k A₀ hA₀
    have L1 : Filter.Tendsto (fun n : ℕ => ∫ ω in T, trunc h n (ω (k + 1)) ∂μ) Filter.atTop
        (𝓝 (∫ ω in T, h (ω (k + 1)) ∂μ)) := by
      refine tendsto_integral_of_dominated_convergence (fun ω : ℕ → X => |h (ω (k + 1))|)
        (fun n => (((measurable_trunc hh n).comp
          (measurable_pi_apply (k + 1))).aestronglyMeasurable))
        (hf.abs.integrableOn) (fun n => Filter.Eventually.of_forall fun ω => ?_)
        (Filter.Eventually.of_forall fun ω => tendsto_trunc h (ω (k + 1)))
      simpa [Real.norm_eq_abs] using abs_trunc_le_abs h n (ω (k + 1))
    have L2 : Filter.Tendsto (fun n : ℕ => ∫ ω in T, (∫ y, trunc h n y ∂(P (ω k))) ∂μ)
        Filter.atTop (𝓝 (∫ ω in T, (∫ y, h y ∂(P (ω k))) ∂μ)) := by
      refine tendsto_integral_of_dominated_convergence
        (fun ω : ℕ → X => ∫ y, ‖h y‖ ∂(P (ω k)))
        (fun n => (((measurable_kernel_integral P (measurable_trunc hh n)).comp
          (measurable_pi_apply k)).aestronglyMeasurable))
        (hnormμ.integrableOn) (fun n => ?_) ?_
      · filter_upwards [ae_restrict_of_ae haeμ] with ω hω
        calc ‖∫ y, trunc h n y ∂(P (ω k))‖ ≤ ∫ y, ‖trunc h n y‖ ∂(P (ω k)) :=
              norm_integral_le_integral_norm _
          _ ≤ ∫ y, ‖h y‖ ∂(P (ω k)) := by
              refine integral_mono ?_ hω.norm (fun y => ?_)
              · exact (hω.norm.mono' (measurable_trunc hh n).norm.aestronglyMeasurable
                  (Filter.Eventually.of_forall fun y => by
                    simpa [Real.norm_eq_abs] using abs_trunc_le_abs h n y))
              · simpa [Real.norm_eq_abs] using abs_trunc_le_abs h n y
      · filter_upwards [ae_restrict_of_ae haeμ] with ω hω
        refine tendsto_integral_of_dominated_convergence (fun y => |h y|)
          (fun n => (measurable_trunc hh n).aestronglyMeasurable) hω.abs
          (fun n => Filter.Eventually.of_forall fun y => by
            simpa [Real.norm_eq_abs] using abs_trunc_le_abs h n y)
          (Filter.Eventually.of_forall fun y => tendsto_trunc h y)
    exact tendsto_nhds_unique L2 (L1.congr key)
  · exact ((hgm.comp (measurable_coord_pathSigma (le_refl k))) :
      Measurable[pathSigma X k] _).stronglyMeasurable.aestronglyMeasurable

end MarkovChainCLT

-- === tl_score.lean ===




namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

/-- The influence function is square-integrable wherever the reward is. -/
theorem memLp_influence (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y))
    (hrint : Integrable (fun z : Step S => Step.rwd z) ν)
    (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0) (s : S)
    (μ : Measure (Step S)) [IsFiniteMeasure μ]
    (hr2 : MemLp (fun z : Step S => Step.rwd z) 2 μ) :
    MemLp (fun y : Step S =>
      fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν)
        (estObs M .IS y)) 2 μ := by
  have hst : Measurable (fun y : Step S => Step.state y) := measurable_fst
  have hnx : Measurable (fun y : Step S => Step.next y) :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have key : ∀ a : Bool, MemLp (fun y : Step S =>
      (mbSystem M (meanObs M .IS ν) a)⁻¹ s (Step.state y) *
        (schemeWeight M .IS a y * (Step.rwd y + M.γdisc * M.value a (Step.next y)
          - M.value a (Step.state y)))) 2 μ := by
    intro a
    obtain ⟨C, hC0, hC⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ i, |(mbSystem M (meanObs M .IS ν) a)⁻¹ s i| ≤ C :=
      ⟨∑ t, |(mbSystem M (meanObs M .IS ν) a)⁻¹ s t|,
        Finset.sum_nonneg fun t _ => abs_nonneg _,
        fun i => Finset.single_le_sum
          (f := fun t => |(mbSystem M (meanObs M .IS ν) a)⁻¹ s t|)
          (fun t _ => abs_nonneg _) (Finset.mem_univ i)⟩
    obtain ⟨D, hD0, hD⟩ : ∃ D : ℝ, 0 ≤ D ∧ ∀ i, |M.value a i| ≤ D :=
      ⟨∑ t, |M.value a t|, Finset.sum_nonneg fun t _ => abs_nonneg _,
        fun i => Finset.single_le_sum (f := fun t => |M.value a t|)
          (fun t _ => abs_nonneg _) (Finset.mem_univ i)⟩
    obtain ⟨cw, hcwdef⟩ : ∃ f : Step S → ℝ, f = fun y : Step S =>
        (mbSystem M (meanObs M .IS ν) a)⁻¹ s (Step.state y) * schemeWeight M .IS a y :=
      ⟨_, rfl⟩
    have hcwm : Measurable cw := by
      rw [hcwdef]
      exact ((measurable_of_countable _).comp hst).mul (measurable_schemeWeight M a)
    have hcwb : ∀ y : Step S, |cw y| ≤ C * 2 := by
      intro y
      simp only [hcwdef]
      rw [abs_mul]
      exact mul_le_mul (hC _) (schemeWeight_IS_abs_le M a y) (abs_nonneg _) hC0
    have hvm : Measurable (fun y : Step S =>
        M.γdisc * M.value a (Step.next y) - M.value a (Step.state y)) :=
      (((measurable_of_countable (M.value a)).comp hnx).const_mul _).sub
        ((measurable_of_countable (M.value a)).comp hst)
    have hvb : ∀ y : Step S,
        |M.γdisc * M.value a (Step.next y) - M.value a (Step.state y)|
          ≤ |M.γdisc| * D + D := by
      intro y
      have hsub : ∀ x z : ℝ, |x - z| ≤ |x| + |z| := fun x z => by
        calc |x - z| = |x + -z| := by ring_nf
          _ ≤ |x| + |-z| := abs_add_le _ _
          _ = |x| + |z| := by rw [abs_neg]
      refine (hsub _ _).trans (add_le_add ?_ (hD _))
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hD _) (abs_nonneg _)
    have h1 : MemLp (fun y : Step S => cw y * Step.rwd y) 2 μ := by
      refine MemLp.of_le (hr2.const_mul (C * 2))
        (hcwm.mul measurable_rwd).aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ C * 2)]
      exact mul_le_mul_of_nonneg_right (hcwb y) (abs_nonneg _)
    have h2 : MemLp (fun y : Step S => cw y *
        (M.γdisc * M.value a (Step.next y) - M.value a (Step.state y))) 2 μ := by
      refine MemLp.of_bound (hcwm.mul hvm).aestronglyMeasurable
        ((C * 2) * (|M.γdisc| * D + D)) (Filter.Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hcwb y) (hvb y) (abs_nonneg _) (by positivity)
    have hfun : (fun y : Step S =>
        (mbSystem M (meanObs M .IS ν) a)⁻¹ s (Step.state y) *
          (schemeWeight M .IS a y * (Step.rwd y + M.γdisc * M.value a (Step.next y)
            - M.value a (Step.state y))))
        = fun y : Step S => cw y * Step.rwd y
          + cw y * (M.γdisc * M.value a (Step.next y) - M.value a (Step.state y)) := by
      funext y
      simp only [hcwdef]
      ring
    rw [hfun]
    exact h1.add h2
  simp only [influence_eq M ν hinv hR hrint hμ s]
  exact (key true).sub (key false)

end TreatmentLocality

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

/-- The influence function of the information-sharing estimator contracted against a
direction `w`. -/
noncomputable def infl (M : Model S) (ν : Measure (Step S)) (w : S → ℝ) (z : Step S) : ℝ :=
  ∑ s, w s * fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν) (estObs M .IS z)

lemma integrable_rwd_expKernel (M : Model S)
    (hR : ∀ t a, Integrable (fun r : ℝ => r) (M.reward t a)) (z : Step S) :
    Integrable (fun w : Step S => Step.rwd w) (expKernel M z) :=
  ⟨measurable_rwd.aestronglyMeasurable, lt_of_le_of_lt
    (lintegral_expKernel_rwd_le M (F := fun r : ℝ => ‖r‖ₑ) measurable_id.enorm z)
    (ENNReal.sum_lt_top.2 fun t _ => ENNReal.sum_lt_top.2 fun a _ => (hR t a).2)⟩

variable (M : Model S) (ν : Measure (Step S))

lemma measurable_infl [IsProbabilityMeasure ν] (hinv : Kernel.Invariant (expKernel M) ν)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y))
    (hrint : Integrable (fun z : Step S => Step.rwd z) ν)
    (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0) (w : S → ℝ) :
    Measurable (infl M ν w) :=
  Finset.measurable_sum _ fun s _ =>
    (measurable_influence M ν hinv hR hrint hμ s).const_mul _

lemma memLp_infl [IsProbabilityMeasure ν] (hinv : Kernel.Invariant (expKernel M) ν)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y))
    (hrint : Integrable (fun z : Step S => Step.rwd z) ν)
    (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0) (w : S → ℝ)
    (μ : Measure (Step S)) [IsFiniteMeasure μ]
    (hr2 : MemLp (fun z : Step S => Step.rwd z) 2 μ) :
    MemLp (infl M ν w) 2 μ :=
  memLp_finsetSum (μ := μ) (f := fun (s : S) (z : Step S) =>
      w s * fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν) (estObs M .IS z))
    _ fun s _ => (memLp_influence M ν hinv hR hrint hμ s μ hr2).const_mul (w s)

lemma integrable_infl [IsProbabilityMeasure ν] (hinv : Kernel.Invariant (expKernel M) ν)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y))
    (hrint : Integrable (fun z : Step S => Step.rwd z) ν)
    (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0) (w : S → ℝ)
    (μ : Measure (Step S)) [IsFiniteMeasure μ]
    (hr : Integrable (fun z : Step S => Step.rwd z) μ) :
    Integrable (infl M ν w) μ :=
  integrable_finsetSum (μ := μ) (f := fun (s : S) (z : Step S) =>
      w s * fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν) (estObs M .IS z))
    _ fun s _ => (integrable_influence M ν hinv hR hrint hμ s μ hr).const_mul (w s)

/-- **The contracted influence function has zero conditional mean.** -/
theorem integral_infl_expKernel_eq_zero [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y))
    (hrint : Integrable (fun z : Step S => Step.rwd z) ν)
    (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0) (w : S → ℝ)
    (z : Step S) :
    ∫ y, infl M ν w y ∂(expKernel M z) = 0 := by
  simp only [infl]
  rw [integral_finsetSum (μ := expKernel M z) (f := fun (s : S) (y : Step S) =>
      w s * fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν) (estObs M .IS y))
    _ fun s _ => (integrable_influence M ν hinv hR hrint hμ s (expKernel M z)
      (integrable_rwd_expKernel M hR z)).const_mul (w s)]
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [integral_const_mul, integral_influence_expKernel_eq_zero M ν hinv hR hrint hμ s z,
    mul_zero]

/-- The contracted influence function is centred under the stationary law. -/
theorem integral_infl_eq_zero [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y))
    (hrint : Integrable (fun z : Step S => Step.rwd z) ν)
    (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0) (w : S → ℝ) :
    ∫ z, infl M ν w z ∂ν = 0 := by
  simp only [infl]
  rw [integral_finsetSum (μ := ν) (f := fun (s : S) (z : Step S) =>
      w s * fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν) (estObs M .IS z))
    _ fun s _ => (integrable_influence M ν hinv hR hrint hμ s ν hrint).const_mul (w s)]
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [integral_const_mul, integral_influence_eq_zero M ν hinv hR hrint hμ s, mul_zero]

end TreatmentLocality

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

/-- **The second moment of the contracted influence function is the information-sharing
asymptotic variance in that direction.** -/
theorem integral_infl_sq (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y))
    (hrint : Integrable (fun z : Step S => Step.rwd z) ν)
    (hr2 : MemLp (fun z : Step S => Step.rwd z) 2 ν)
    (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0)
    (hiter : ∀ (k : ℕ) (x : Step S), Integrable (fun z : Step S => Step.rwd z)
      (MarkovChainCLT.iterKernel (expKernel M) k x)) (w : S → ℝ) :
    ∫ z, (infl M ν w z) ^ 2 ∂ν = ∑ s, ∑ s', w s * mbISCov M ν s s' * w s' := by
  have hL2 : ∀ s : S, MemLp (fun z : Step S =>
      fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν) (estObs M .IS z)) 2 ν :=
    fun s => memLp_influence M ν hinv hR hrint hμ s ν hr2
  have hprod : ∀ s s' : S, Integrable (fun z : Step S =>
      (fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν) (estObs M .IS z))
        * (fderiv ℝ (fun u : EstInput S => mbATE M u s') (meanObs M .IS ν)
            (estObs M .IS z))) ν := fun s s' => (hL2 s).integrable_mul (hL2 s')
  have hcprod : ∀ s s' : S, Integrable (fun z : Step S => (w s * w s') *
      ((fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν) (estObs M .IS z))
        * (fderiv ℝ (fun u : EstInput S => mbATE M u s') (meanObs M .IS ν)
            (estObs M .IS z)))) ν := fun s s' => (hprod s s').const_mul _
  have hexp : ∀ z : Step S, (infl M ν w z) ^ 2
      = ∑ s, ∑ s', (w s * w s') *
        ((fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν) (estObs M .IS z))
          * (fderiv ℝ (fun u : EstInput S => mbATE M u s') (meanObs M .IS ν)
              (estObs M .IS z))) := by
    intro z
    simp only [infl, sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => by ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hexp)]
  rw [integral_finsetSum (μ := ν) (f := fun (s : S) (z : Step S) => ∑ s', (w s * w s') *
      ((fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν) (estObs M .IS z))
        * (fderiv ℝ (fun u : EstInput S => mbATE M u s') (meanObs M .IS ν)
            (estObs M .IS z)))) _
    (fun s _ => integrable_finsetSum (μ := ν) (f := fun (s' : S) (z : Step S) =>
      (w s * w s') *
      ((fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν) (estObs M .IS z))
        * (fderiv ℝ (fun u : EstInput S => mbATE M u s') (meanObs M .IS ν)
            (estObs M .IS z)))) _ (fun s' _ => hcprod s s'))]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [integral_finsetSum (μ := ν) (f := fun (s' : S) (z : Step S) => (w s * w s') *
      ((fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν) (estObs M .IS z))
        * (fderiv ℝ (fun u : EstInput S => mbATE M u s') (meanObs M .IS ν)
            (estObs M .IS z)))) _ (fun s' _ => hcprod s s')]
  refine Finset.sum_congr rfl fun s' _ => ?_
  rw [integral_const_mul, ← mbISCov_eq_integral M ν hinv hR hrint hμ hiter s s']
  ring

end TreatmentLocality

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

section Chain

variable (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
  (hinv : Kernel.Invariant (expKernel M) ν)
  (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y))
  (hrint : Integrable (fun z : Step S => Step.rwd z) ν)
  (hr2 : MemLp (fun z : Step S => Step.rwd z) 2 ν)
  (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0)
  (w : S → ℝ)

include hinv hR hrint hμ in
lemma memLp_coord_infl (hr2 : MemLp (fun z : Step S => Step.rwd z) 2 ν) (n : ℕ) :
    MemLp (fun ω : ℕ → Step S => infl M ν w (ω n)) 2
      (MarkovChainCLT.chainMeasure (expKernel M) ν) := by
  have hmap := MarkovChainCLT.map_coord_chainMeasure (expKernel M) ν hinv n
  have h : MemLp (infl M ν w) 2
      (Measure.map (fun ω : ℕ → Step S => ω n) (MarkovChainCLT.chainMeasure (expKernel M) ν)) := by
    rw [hmap]; exact memLp_infl M ν hinv hR hrint hμ w ν hr2
  exact (memLp_map_measure_iff h.1 (measurable_pi_apply n).aemeasurable).1 h

include hinv hR hrint hμ in
lemma integral_coord_infl (n : ℕ) :
    ∫ ω, infl M ν w (ω n) ∂(MarkovChainCLT.chainMeasure (expKernel M) ν) = 0 := by
  have hmap := MarkovChainCLT.map_coord_chainMeasure (expKernel M) ν hinv n
  have h := integral_map (μ := MarkovChainCLT.chainMeasure (expKernel M) ν)
    (φ := fun ω : ℕ → Step S => ω n) (f := infl M ν w)
    (measurable_pi_apply n).aemeasurable
    (by rw [hmap]; exact (measurable_infl M ν hinv hR hrint hμ w).aestronglyMeasurable)
  rw [hmap] at h
  rw [← h]
  exact integral_infl_eq_zero M ν hinv hR hrint hμ w

include hinv hR hrint hμ in
lemma integral_coord_infl_sq
    (hr2 : MemLp (fun z : Step S => Step.rwd z) 2 ν)
    (hiter : ∀ (k : ℕ) (x : Step S), Integrable (fun z : Step S => Step.rwd z)
      (MarkovChainCLT.iterKernel (expKernel M) k x)) (n : ℕ) :
    ∫ ω, (infl M ν w (ω n)) ^ 2 ∂(MarkovChainCLT.chainMeasure (expKernel M) ν)
      = ∑ s, ∑ s', w s * mbISCov M ν s s' * w s' := by
  have hmap := MarkovChainCLT.map_coord_chainMeasure (expKernel M) ν hinv n
  have h := integral_map (μ := MarkovChainCLT.chainMeasure (expKernel M) ν)
    (φ := fun ω : ℕ → Step S => ω n) (f := fun z : Step S => (infl M ν w z) ^ 2)
    (measurable_pi_apply n).aemeasurable
    (by rw [hmap]
        exact ((measurable_infl M ν hinv hR hrint hμ w).pow_const 2).aestronglyMeasurable)
  rw [hmap] at h
  rw [← h]
  exact integral_infl_sq M ν hinv hR hrint hr2 hμ hiter w

include hinv hR hrint hμ in
lemma condExp_coord_infl (j : ℕ) :
    (MarkovChainCLT.chainMeasure (expKernel M) ν)[fun ω : ℕ → Step S => infl M ν w (ω (j + 1)) |
        MarkovChainCLT.pathSigma (Step S) j]
      =ᵐ[MarkovChainCLT.chainMeasure (expKernel M) ν] 0 := by
  have hker := (MarkovChainCLT.condExp_next_coord_of_integrable (expKernel M) ν hinv
    (infl M ν w) (measurable_infl M ν hinv hR hrint hμ w)
    (integrable_infl M ν hinv hR hrint hμ w ν hrint) j).symm
  filter_upwards [hker] with ω hω
  simp only [Pi.zero_apply]
  rw [hω]
  exact integral_infl_expKernel_eq_zero M ν hinv hR hrint hμ w (ω j)

include hinv hR hrint hμ in
lemma stronglyMeasurable_coord_infl {n j : ℕ} (hnj : n ≤ j) :
    StronglyMeasurable[MarkovChainCLT.pathSigma (Step S) j]
      (fun ω : ℕ → Step S => infl M ν w (ω n)) :=
  (((measurable_infl M ν hinv hR hrint hμ w).comp
    (MarkovChainCLT.measurable_coord_pathSigma hnj)) :
      Measurable[MarkovChainCLT.pathSigma (Step S) j] _).stronglyMeasurable

end Chain

end TreatmentLocality

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

/-- **The martingale score system of the SST experiment**, given the covariance identity
between the estimator and the accumulated influence function. -/
theorem exists_martingale_score_of_score_covariance
    (M : Model S) (m : S → Bool → ℝ) (v : S → Bool → ℝ≥0)
    (hgauss : M.GaussianRewards m v)
    (hpos : ∀ s a j, 0 < M.trans s (M.act a s) j)
    (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    (δ : (T : ℕ) → (Fin T → Step S) → S → ℝ)
    (hscore : ∀ (w : S → ℝ) (T : ℕ), 1 ≤ T →
      ∫ ω, (∑ s, w s * δ T (fun i => ω (i.1 + 1)) s)
            * (∑ i ∈ Finset.range (T + 1),
                ∑ s, w s * fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν)
                  (estObs M .IS (ω i)))
          ∂(MarkovChainCLT.chainMeasure (expKernel M) ν)
        = ∑ s, ∑ s', w s * mbISCov M ν s s' * w s') :
    ∀ w : S → ℝ, ∃ (V : ℕ → (ℕ → Step S) → ℝ) (c : (ℕ → Step S) → ℝ),
      (∀ j, MemLp (V j) 2 (MarkovChainCLT.chainMeasure (expKernel M) ν)) ∧
      (∀ j, StronglyMeasurable[MeasurableSpace.comap
          (Preorder.frestrictLe (π := fun _ : ℕ => Step S) (j + 1)) inferInstance] (V j)) ∧
      (∀ j, (MarkovChainCLT.chainMeasure (expKernel M) ν)[V j | MeasurableSpace.comap
            (Preorder.frestrictLe (π := fun _ : ℕ => Step S) j) inferInstance]
          =ᵐ[MarkovChainCLT.chainMeasure (expKernel M) ν] 0) ∧
      (∀ j, ∫ ω, (V j ω) ^ 2 ∂(MarkovChainCLT.chainMeasure (expKernel M) ν)
          = ∑ s, ∑ s', w s * mbISCov M ν s s' * w s') ∧
      MemLp c 2 (MarkovChainCLT.chainMeasure (expKernel M) ν) ∧
      StronglyMeasurable[MeasurableSpace.comap
        (Preorder.frestrictLe (π := fun _ : ℕ => Step S) 0) inferInstance] c ∧
      ∫ ω, c ω ∂(MarkovChainCLT.chainMeasure (expKernel M) ν) = 0 ∧
      (∀ T : ℕ, 1 ≤ T →
        ∫ ω, (∑ s, w s * δ T (fun i => ω (i.1 + 1)) s)
              * ((∑ j ∈ Finset.range T, V j ω) + c ω)
            ∂(MarkovChainCLT.chainMeasure (expKernel M) ν)
          = ∑ s, ∑ s', w s * mbISCov M ν s s' * w s') := by
  have hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y) :=
    fun x y => integrable_reward_of_gaussian M m v hgauss x y
  have hR2 : ∀ t a, MemLp (fun r : ℝ => r) 2 (M.reward t a) :=
    fun t a => memLp_reward_of_gaussian M m v hgauss t a
  have hrint := integrable_rwd_of_invariant M ν hinv hR
  have hr2 := memLp_rwd_of_invariant M ν hinv hR2
  have hμ := visit_ne_zero_of_trans_pos M ν hinv hpos
  have hiter := integrable_rwd_iterKernel M hR
  intro w
  refine ⟨fun j ω => infl M ν w (ω (j + 1)), fun ω => infl M ν w (ω 0),
    fun j => memLp_coord_infl M ν hinv hR hrint hμ w hr2 (j + 1),
    fun j => stronglyMeasurable_coord_infl M ν hinv hR hrint hμ w (le_refl (j + 1)),
    fun j => condExp_coord_infl M ν hinv hR hrint hμ w j,
    fun j => integral_coord_infl_sq M ν hinv hR hrint hμ w hr2 hiter (j + 1),
    memLp_coord_infl M ν hinv hR hrint hμ w hr2 0,
    stronglyMeasurable_coord_infl M ν hinv hR hrint hμ w (le_refl 0),
    integral_coord_infl M ν hinv hR hrint hμ w 0, ?_⟩
  intro T hT
  have e : ∀ ω : ℕ → Step S,
      (∑ s, w s * δ T (fun i => ω (i.1 + 1)) s)
          * ((∑ j ∈ Finset.range T, infl M ν w (ω (j + 1))) + infl M ν w (ω 0))
        = (∑ s, w s * δ T (fun i => ω (i.1 + 1)) s)
          * (∑ i ∈ Finset.range (T + 1), infl M ν w (ω i)) := by
    intro ω
    rw [Finset.sum_range_succ']
  rw [integral_congr_ae (Filter.Eventually.of_forall e)]
  exact hscore w T hT

end TreatmentLocality

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

/-- **The influence function lies in the tangent space of the SST family**: it is an
affine function of the reward, centred at the mean reward of the executed action, plus a
function of the realized transition that is centred under the true transition law. -/
theorem influence_tangent_decomposition_aux (M : Model S) (ν : Measure (Step S))
    [IsProbabilityMeasure ν] (hinv : Kernel.Invariant (expKernel M) ν)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y))
    (hrint : Integrable (fun z : Step S => Step.rwd z) ν)
    (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0) (w : S → ℝ) :
    ∃ (α : S → Bool → ℝ) (β : S → Bool → S → ℝ),
      (∀ (s : S) (γ : Bool),
        ∑ j, (M.trans s (M.act γ s) j).toReal * β s (M.act γ s) j = 0) ∧
      (∀ z : Step S, infl M ν w z
        = α (Step.state z) (M.act (Step.arm z) (Step.state z))
            * (Step.rwd z
              - ∫ x, x ∂(M.reward (Step.state z) (M.act (Step.arm z) (Step.state z))))
          + β (Step.state z) (M.act (Step.arm z) (Step.state z)) (Step.next z)) := by
  classical
  obtain ⟨G, hG⟩ : ∃ G : Bool → S → ℝ, G = fun a i =>
      ∑ s, w s * (mbSystem M (meanObs M .IS ν) a)⁻¹ s i := ⟨_, rfl⟩
  obtain ⟨Ct, hCt⟩ : ∃ Ct : S → Bool → ℝ, Ct = fun s a =>
      if s = M.crucial then (if a then 2 * G true s else 0) else G true s := ⟨_, rfl⟩
  obtain ⟨Cf, hCf⟩ : ∃ Cf : S → Bool → ℝ, Cf = fun s a =>
      if s = M.crucial then (if a then 0 else 2 * G false s) else G false s := ⟨_, rfl⟩
  refine ⟨fun s a => Ct s a - Cf s a,
    fun s a j => (Ct s a - Cf s a) * (∫ x, x ∂(M.reward s a))
      + M.γdisc * (Ct s a * M.value true j - Cf s a * M.value false j)
      - (Ct s a * M.value true s - Cf s a * M.value false s), ?_, ?_⟩
  · intro s γ
    have hsum1 : ∑ j, (M.trans s (M.act γ s) j).toReal = 1 :=
      pmf_sum_toReal (M.trans s (M.act γ s))
    have hbel : ∀ b : Bool, M.act b s = M.act γ s →
        (∫ x, x ∂(M.reward s (M.act γ s)))
          + M.γdisc * (∑ j, (M.trans s (M.act γ s) j).toReal * M.value b j)
          - M.value b s = 0 := by
      intro b hb
      have h1 : ∀ j : S, (M.trans s (M.act γ s) j).toReal = M.polTrans b s j := by
        intro j; rw [Model.polTrans, Matrix.of_apply, hb]
      have h2 : (∫ x, x ∂(M.reward s (M.act γ s))) = M.polReward b s := by
        rw [Model.polReward, hb]
      rw [h2, Finset.sum_congr rfl (fun j _ => by rw [h1 j])]
      have hv := value_bellman_apply M b s
      linarith
    have hexpand : ∑ j, (M.trans s (M.act γ s) j).toReal *
          ((Ct s (M.act γ s) - Cf s (M.act γ s)) * (∫ x, x ∂(M.reward s (M.act γ s)))
            + M.γdisc * (Ct s (M.act γ s) * M.value true j
              - Cf s (M.act γ s) * M.value false j)
            - (Ct s (M.act γ s) * M.value true s - Cf s (M.act γ s) * M.value false s))
        = Ct s (M.act γ s) * ((∫ x, x ∂(M.reward s (M.act γ s)))
            + M.γdisc * (∑ j, (M.trans s (M.act γ s) j).toReal * M.value true j)
            - M.value true s)
          - Cf s (M.act γ s) * ((∫ x, x ∂(M.reward s (M.act γ s)))
            + M.γdisc * (∑ j, (M.trans s (M.act γ s) j).toReal * M.value false j)
            - M.value false s) := by
      have hterm : ∀ j : S, (M.trans s (M.act γ s) j).toReal *
          ((Ct s (M.act γ s) - Cf s (M.act γ s)) * (∫ x, x ∂(M.reward s (M.act γ s)))
            + M.γdisc * (Ct s (M.act γ s) * M.value true j
              - Cf s (M.act γ s) * M.value false j)
            - (Ct s (M.act γ s) * M.value true s - Cf s (M.act γ s) * M.value false s))
          = ((Ct s (M.act γ s) - Cf s (M.act γ s)) * (∫ x, x ∂(M.reward s (M.act γ s)))
              - (Ct s (M.act γ s) * M.value true s - Cf s (M.act γ s) * M.value false s))
            * (M.trans s (M.act γ s) j).toReal
            + (M.γdisc * Ct s (M.act γ s))
              * ((M.trans s (M.act γ s) j).toReal * M.value true j)
            - (M.γdisc * Cf s (M.act γ s))
              * ((M.trans s (M.act γ s) j).toReal * M.value false j) := fun j => by ring
      rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_sub_distrib,
        Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hsum1]
      ring
    rw [hexpand]
    by_cases hs : s = M.crucial
    · cases γ
      · have hact : M.act false s = false := by simp [Model.act]
        have hct : Ct s (M.act false s) = 0 := by
          simp only [hCt, hact, if_pos hs]; simp
        have hcf : Cf s (M.act false s) = 2 * G false s := by
          simp only [hCf, hact, if_pos hs]; simp
        rw [hct, hcf, hbel false rfl]
        ring
      · have hact : M.act true s = true := by simp [Model.act, hs]
        have hct : Ct s (M.act true s) = 2 * G true s := by
          simp only [hCt, hact, if_pos hs]; simp
        have hcf : Cf s (M.act true s) = 0 := by
          simp only [hCf, hact, if_pos hs]; simp
        rw [hct, hcf, hbel true rfl]
        ring
    · have hactf : M.act false s = M.act γ s := by simp [Model.act, hs]
      have hactt : M.act true s = M.act γ s := by simp [Model.act, hs]
      rw [hbel true hactt, hbel false hactf]
      ring
  · intro z
    simp only [infl, influence_eq M ν hinv hR hrint hμ]
    have hsub : ∀ (T1 T2 : S → ℝ), ∑ s, w s * (T1 s - T2 s)
        = (∑ s, w s * T1 s) - (∑ s, w s * T2 s) := by
      intro T1 T2
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [hsub]
    have hfac : ∀ (a : Bool) (Y : ℝ),
        ∑ s, w s * ((mbSystem M (meanObs M .IS ν) a)⁻¹ s (Step.state z) * Y)
          = G a (Step.state z) * Y := by
      intro a Y
      rw [hG]
      simp only
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [hfac true, hfac false]
    have hWt : G true (Step.state z) * schemeWeight M .IS true z
        = Ct (Step.state z) (M.act (Step.arm z) (Step.state z)) := by
      rw [hCt]
      simp only
      by_cases hs : Step.state z = M.crucial
      · rw [if_pos hs]
        have : M.act (Step.arm z) (Step.state z) = Step.arm z := by simp [Model.act, hs]
        rw [this]
        show G true (Step.state z) *
          (if Step.state z = M.crucial then
            2 * (if Step.arm z = true then (1 : ℝ) else 0) else 1) = _
        rw [if_pos hs]
        cases Step.arm z <;> simp <;> ring
      · rw [if_neg hs]
        show G true (Step.state z) *
          (if Step.state z = M.crucial then
            2 * (if Step.arm z = true then (1 : ℝ) else 0) else 1) = _
        rw [if_neg hs, mul_one]
    have hWf : G false (Step.state z) * schemeWeight M .IS false z
        = Cf (Step.state z) (M.act (Step.arm z) (Step.state z)) := by
      rw [hCf]
      simp only
      by_cases hs : Step.state z = M.crucial
      · rw [if_pos hs]
        have : M.act (Step.arm z) (Step.state z) = Step.arm z := by simp [Model.act, hs]
        rw [this]
        show G false (Step.state z) *
          (if Step.state z = M.crucial then
            2 * (if Step.arm z = false then (1 : ℝ) else 0) else 1) = _
        rw [if_pos hs]
        cases Step.arm z <;> simp <;> ring
      · rw [if_neg hs]
        show G false (Step.state z) *
          (if Step.state z = M.crucial then
            2 * (if Step.arm z = false then (1 : ℝ) else 0) else 1) = _
        rw [if_neg hs, mul_one]
    rw [← mul_assoc, ← mul_assoc, hWt, hWf]
    ring

end TreatmentLocality


open TreatmentLocality in
theorem solution {S : Type*} [DecidableEq S]
    [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y))
    (hrint : Integrable (fun z : Step S => Step.rwd z) ν)
    (hμ : ∀ i, ∫ z, (if Step.state z = i then (1 : ℝ) else 0) ∂ν ≠ 0) (w : S → ℝ) :
    ∃ (α : S → Bool → ℝ) (β : S → Bool → S → ℝ),
      (∀ (s : S) (γ : Bool),
        ∑ j, (M.trans s (M.act γ s) j).toReal * β s (M.act γ s) j = 0) ∧
      (∀ z : Step S,
        (∑ s, w s * fderiv ℝ (fun u : EstInput S => mbATE M u s) (meanObs M .IS ν)
            (estObs M .IS z))
          = α (Step.state z) (M.act (Step.arm z) (Step.state z))
              * (Step.rwd z
                - ∫ x, x ∂(M.reward (Step.state z) (M.act (Step.arm z) (Step.state z))))
            + β (Step.state z) (M.act (Step.arm z) (Step.state z)) (Step.next z)) :=
  TreatmentLocality.influence_tangent_decomposition_aux M ν hinv hR hrint hμ w
