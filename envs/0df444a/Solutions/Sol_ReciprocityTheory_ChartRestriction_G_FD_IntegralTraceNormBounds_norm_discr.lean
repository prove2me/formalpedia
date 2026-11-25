-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.IntegralTraceNormBounds.norm_discr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:56:36.69988+00:00
-- url     : https://prove2.me/submissions/0a8bfc3d-2356-4373-bde6-379f630e69d1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TraceIntegralBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegralTraceNormBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.IntegralTraceNormBounds
open NumberField InfinitePlace Module Submodule TraceIntegralBasis
open scoped ComplexConjugate Classical
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace ReciprocityTheory.ChartRestriction.G.FD.IntegralTraceNormBounds
theorem _root_.solution (β : E) (hβ : β ≠ 0)
    (hint : ∀ γ : 𝓞 E, ∃ m : ℤ, Algebra.trace ℚ E (β * (γ : E)) = m) :
    1 ≤ |(Algebra.norm ℚ β : ℝ)| * dE E := by
  choose m hm using fun i j => hint (RingOfIntegers.basis E i * RingOfIntegers.basis E j)
  have hbB : ∀ i, integralBasis E i = ((RingOfIntegers.basis E i : 𝓞 E) : E) := by
    intro i
    rw [integralBasis_apply]
  have hP : Matrix.of (fun i j => ((m i j : ℤ) : ℚ)) =
      Algebra.traceMatrix ℚ (integralBasis E) * Algebra.leftMulMatrix (integralBasis E) β := by
    ext i j
    rw [Matrix.of_apply, ← hm i j, Matrix.mul_apply]
    have e : β * ((RingOfIntegers.basis E i * RingOfIntegers.basis E j : 𝓞 E) : E) =
        integralBasis E i * (β * integralBasis E j) := by
      rw [hbB, hbB]
      push_cast
      ring
    rw [e]
    conv_lhs => rw [← (integralBasis E).sum_repr (β * integralBasis E j)]
    rw [Finset.mul_sum, map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Algebra.leftMulMatrix_eq_repr_mul, Algebra.traceMatrix_apply, Algebra.traceForm_apply,
      mul_smul_comm, LinearMap.map_smul, smul_eq_mul]
    ring
  have h1 : ((Matrix.of m).det : ℚ) = (Matrix.of (fun i j => ((m i j : ℤ) : ℚ))).det := by
    rw [show ((Matrix.of m).det : ℚ) = (Int.castRingHom ℚ) (Matrix.of m).det from rfl,
      RingHom.map_det]
    rfl
  have hdet : ((Matrix.of m).det : ℚ) = (NumberField.discr E : ℚ) * Algebra.norm ℚ β := by
    rw [h1, hP, Matrix.det_mul, NumberField.coe_discr, Algebra.discr_def,
      Algebra.norm_eq_matrix_det (integralBasis E)]
  have hN0 : Algebra.norm ℚ β ≠ 0 := Algebra.norm_ne_zero_iff.mpr hβ
  have hD0 : (NumberField.discr E : ℚ) ≠ 0 := by exact_mod_cast NumberField.discr_ne_zero E
  have hZ : (Matrix.of m).det ≠ 0 := by
    intro h
    have h0 : ((Matrix.of m).det : ℚ) = 0 := by rw [h]; simp
    rw [hdet] at h0
    exact mul_ne_zero hD0 hN0 h0
  have hR : ((Matrix.of m).det : ℝ) =
      ((NumberField.discr E : ℤ) : ℝ) * ((Algebra.norm ℚ β : ℚ) : ℝ) := by
    have h2 := congrArg (Rat.cast : ℚ → ℝ) hdet
    simp only [Rat.cast_mul, Rat.cast_intCast] at h2
    exact h2
  unfold dE
  rw [← abs_mul, mul_comm, ← hR]
  exact_mod_cast Int.one_le_abs hZ
end ReciprocityTheory.ChartRestriction.G.FD.IntegralTraceNormBounds
