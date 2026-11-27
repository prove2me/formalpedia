-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.injective_map_of_int_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:25:16.435024+00:00
-- url     : https://prove2.me/submissions/2b7c0c34-806f-4dd8-8f8e-347016310944

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_coe_dehK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.coe_dehK



set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder Matrix
variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {R r : ℕ} (M : Matrix (Fin R) (Fin r) ℤ)
    (key : ∀ u : Fin r → ℤ, M *ᵥ u = 0 → u = 0) :
    Function.Injective (M.map (Int.cast : ℤ → ℚ)).mulVec := by
  intro v w hvw
  have hd : M.map (Int.cast : ℤ → ℚ) *ᵥ (v - w) = 0 := by
    rw [Matrix.mulVec_sub, hvw, sub_self]
  obtain ⟨⟨c, hc⟩, hcu⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) (v - w)
  choose u hu using hcu
  have hu2 : ∀ i, ((u i : ℤ) : ℚ) = (c : ℚ) * (v - w) i := fun i => by
    have := hu i
    simp only [zsmul_eq_mul, algebraMap_int_eq, eq_intCast] at this
    exact this
  have hMu : M *ᵥ u = 0 := by
    funext p
    have h1 := RingHom.map_mulVec (Int.castRingHom ℚ) M u p
    have h2 : (Int.castRingHom ℚ) ∘ u = (c : ℚ) • (v - w) := by
      funext i; simp [hu2 i]
    rw [h2, Matrix.mulVec_smul] at h1
    simp only [Int.coe_castRingHom] at h1
    rw [hd, smul_zero] at h1
    simp only [Pi.zero_apply] at h1 ⊢
    exact_mod_cast h1
  have hu0 := key u hMu
  have hc0 : c ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hc
  funext i
  have := hu2 i
  rw [hu0] at this
  simp only [Pi.zero_apply, Int.cast_zero] at this
  have h3 : (v - w) i = 0 := by
    rcases mul_eq_zero.mp this.symm with h | h
    · exact absurd (by exact_mod_cast h) hc0
    · exact h
  simpa [sub_eq_zero] using h3
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
