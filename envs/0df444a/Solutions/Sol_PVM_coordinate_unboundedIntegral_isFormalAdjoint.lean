-- Prove2me | solution 1 for PVM.coordinate_unboundedIntegral_isFormalAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:01:48.26985+00:00
-- url     : https://prove2.me/submissions/0a43b75d-24ba-4123-8a0a-325dba3e423c

import Definitions.Def_Spectral_PVM_Integral
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Function.L2Space
import Definitions.Def_Spectral_PVM_Unbounded
import Theorems.Thm_PVM_ofReal_norm_sq_integral_sub_unboundedIntegral
import Theorems.Thm_PVM_simpleIntegral_const
import Theorems.Thm_PVM_simpleIntegral_one
import Theorems.Thm_PVM_simpleIntegral_zero
import Theorems.Thm_PVM_tendsto_simpleIntegral_of_tendstoUniformly
attribute [local simp] PVM.simpleIntegral_one
attribute [local simp] PVM.simpleIntegral_zero


section
open MeasureTheory
open Function
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
open Filter
private theorem PVM.integral_const_for_symmetry (E_pvm : PVM E) (z : ℂ) :
    E_pvm.integral (fun _ : ℝ => z) measurable_const
      ⟨‖z‖, fun _ => le_refl _⟩ = z • 1 := by
  have hUniform : TendstoUniformly
      (fun (_n : ℕ) (t : ℝ) => SimpleFunc.const ℝ z t)
      (fun _t : ℝ => z) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [] with n
    intro t
    change dist z z < ε
    rw [dist_self]
    exact hε
  have hlim := E_pvm.tendsto_simpleIntegral_of_tendstoUniformly
    (fun _ : ℝ => z) measurable_const ⟨‖z‖, fun _ => le_refl _⟩
    (fun _n => SimpleFunc.const ℝ z) hUniform
  have hconst : Tendsto (fun _n : ℕ => z • (1 : E →L[ℂ] E)) atTop
      (nhds (z • 1)) := tendsto_const_nhds
  apply tendsto_nhds_unique hlim
  simpa only [E_pvm.simpleIntegral_const] using hconst
private theorem coordinateImaginaryDistances (r : ℝ) :
    ‖Complex.I - (r : ℂ)‖₊ ^ 2 = ‖-Complex.I - (r : ℂ)‖₊ ^ 2 := by
  apply NNReal.eq
  change ‖Complex.I - (r : ℂ)‖ ^ 2 = ‖-Complex.I - (r : ℂ)‖ ^ 2
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
    Complex.normSq_apply]
  norm_num
private theorem PVM.coordinate_inner_self_real (E_pvm : PVM E)
    (x : (E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
      Complex.continuous_ofReal.measurable).domain) :
    (starRingEnd ℂ) (@inner ℂ E _
      (E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
        Complex.continuous_ofReal.measurable x) (x : E)) =
      @inner ℂ E _
        (E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
          Complex.continuous_ofReal.measurable x) (x : E) := by
  let A := E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
    Complex.continuous_ofReal.measurable
  let fi : ℝ → ℂ := fun _ => Complex.I
  let fni : ℝ → ℂ := fun _ => -Complex.I
  have hfi : Measurable fi := measurable_const
  have hfni : Measurable fni := measurable_const
  let hbi : ∃ C, ∀ r, ‖fi r‖ ≤ C :=
    ⟨‖Complex.I‖, fun _ => le_refl _⟩
  let hbni : ∃ C, ∀ r, ‖fni r‖ ≤ C :=
    ⟨‖-Complex.I‖, fun _ => le_refl _⟩
  have hi := E_pvm.ofReal_norm_sq_integral_sub_unboundedIntegral
    fi hfi hbi ((↑) : ℝ → ℂ) Complex.continuous_ofReal.measurable x
  have hni := E_pvm.ofReal_norm_sq_integral_sub_unboundedIntegral
    fni hfni hbni ((↑) : ℝ → ℂ) Complex.continuous_ofReal.measurable x
  have hright :
      (∫⁻ r, ‖fi r - (r : ℂ)‖₊ ^ 2 ∂(E_pvm.scalarMeasure (x : E))) =
        ∫⁻ r, ‖fni r - (r : ℂ)‖₊ ^ 2 ∂(E_pvm.scalarMeasure (x : E)) := by
    apply lintegral_congr
    intro r
    exact_mod_cast coordinateImaginaryDistances r
  have hsq :
      ‖Complex.I • (x : E) - A x‖ ^ 2 =
        ‖(-Complex.I) • (x : E) - A x‖ ^ 2 := by
    have hofReal : ENNReal.ofReal
          (‖E_pvm.integral fi hfi hbi (x : E) - A x‖ ^ 2) =
        ENNReal.ofReal
          (‖E_pvm.integral fni hfni hbni (x : E) - A x‖ ^ 2) :=
      hi.trans (hright.trans hni.symm)
    have hsquares := (ENNReal.ofReal_eq_ofReal_iff
      (sq_nonneg ‖E_pvm.integral fi hfi hbi (x : E) - A x‖)
      (sq_nonneg ‖E_pvm.integral fni hfni hbni (x : E) - A x‖)).mp hofReal
    rw [show E_pvm.integral fi hfi hbi = Complex.I • 1 by
      exact E_pvm.integral_const_for_symmetry Complex.I,
      show E_pvm.integral fni hfni hbni = (-Complex.I) • 1 by
        exact E_pvm.integral_const_for_symmetry (-Complex.I)] at hsquares
    simpa only [smul_apply, one_apply_eq_self] using hsquares
  have hIm : (@inner ℂ E _ (x : E) (A x)).im = 0 := by
    have hstarI : (starRingEnd ℂ) Complex.I = -Complex.I := Complex.conj_I
    have hstarNegI : (starRingEnd ℂ) (-Complex.I) = Complex.I := by
      rw [map_neg, Complex.conj_I, neg_neg]
    have hreI : RCLike.re (Complex.I * @inner ℂ E _ (x : E) (A x)) =
        -(@inner ℂ E _ (x : E) (A x)).im := by
      change (Complex.I * @inner ℂ E _ (x : E) (A x)).re = _
      rw [Complex.mul_re, Complex.I_re, Complex.I_im]
      ring
    have hreNegI : RCLike.re (-(Complex.I * @inner ℂ E _ (x : E) (A x))) =
        (@inner ℂ E _ (x : E) (A x)).im := by
      rw [map_neg, hreI]
      ring
    rw [norm_sub_sq (𝕜 := ℂ), norm_sub_sq (𝕜 := ℂ), norm_smul, norm_smul,
      Complex.norm_I, norm_neg, Complex.norm_I, one_mul,
      inner_smul_left, inner_smul_left, hstarI, hstarNegI,
      neg_mul, hreI, hreNegI] at hsq
    linarith
  change (starRingEnd ℂ) (@inner ℂ E _ (A x) (x : E)) =
    @inner ℂ E _ (A x) (x : E)
  apply Complex.conj_eq_iff_im.mpr
  rw [← inner_conj_symm (A x) (x : E), Complex.conj_im, hIm, neg_zero]
omit [CompleteSpace E] in
private theorem linearPMap_isFormalAdjoint_self_of_inner_real
    (A : E →ₗ.[ℂ] E)
    (hreal : ∀ z : A.domain,
      (starRingEnd ℂ) (@inner ℂ E _ (A z) (z : E)) =
        @inner ℂ E _ (A z) (z : E)) :
    A.IsFormalAdjoint A := by
  intro x y
  have hpolarization (a b : A.domain) :
      @inner ℂ E _ (A b) (a : E) =
        (@inner ℂ E _ (A (a + b)) ((a + b : A.domain) : E) -
            @inner ℂ E _ (A (a - b)) ((a - b : A.domain) : E) +
              Complex.I * @inner ℂ E _ (A (a + Complex.I • b))
                ((a + Complex.I • b : A.domain) : E) -
            Complex.I * @inner ℂ E _ (A (a - Complex.I • b))
              ((a - Complex.I • b : A.domain) : E)) / 4 := by
    simp only [LinearPMap.map_add, LinearPMap.map_sub, inner_add_left, inner_add_right,
      LinearPMap.map_smul, inner_smul_left, inner_smul_right, Complex.conj_I,
      ← pow_two, Complex.I_sq, inner_sub_left, inner_sub_right, mul_add,
      ← mul_assoc, mul_neg, neg_neg, one_mul, neg_one_mul, mul_sub, sub_sub,
      Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul]
    ring
  have hpolarization' (a b : A.domain) :
      @inner ℂ E _ (A a) (b : E) =
        (@inner ℂ E _ (A (a + b)) ((a + b : A.domain) : E) -
            @inner ℂ E _ (A (a - b)) ((a - b : A.domain) : E) -
              Complex.I * @inner ℂ E _ (A (a + Complex.I • b))
                ((a + Complex.I • b : A.domain) : E) +
            Complex.I * @inner ℂ E _ (A (a - Complex.I • b))
              ((a - Complex.I • b : A.domain) : E)) / 4 := by
    simp only [LinearPMap.map_add, LinearPMap.map_sub, inner_add_left, inner_add_right,
      LinearPMap.map_smul, inner_smul_left, inner_smul_right, Complex.conj_I,
      ← pow_two, Complex.I_sq, inner_sub_left, inner_sub_right, mul_add,
      ← mul_assoc, mul_neg, neg_neg, one_mul, neg_one_mul, mul_sub, sub_sub,
      Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul]
    ring
  rw [← inner_conj_symm (x : E) (A y), hpolarization x y]
  simp only [starRingEnd_apply, star_div₀, star_sub, star_add, star_mul]
  simp only [← starRingEnd_apply]
  rw [hreal (x + y), hreal (x - y), hreal (x + Complex.I • y),
    hreal (x - Complex.I • y)]
  simp only [Complex.conj_I, map_ofNat]
  rw [hpolarization' x y]
  norm_num
  ring
end

set_option autoImplicit false
open MeasureTheory
open Function
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
open Filter
namespace PVM
theorem _root_.solution (E_pvm : PVM E) :
    let A := E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
      Complex.continuous_ofReal.measurable
    A.IsFormalAdjoint A := by
  dsimp only
  apply linearPMap_isFormalAdjoint_self_of_inner_real
  exact E_pvm.coordinate_inner_self_real
end PVM
