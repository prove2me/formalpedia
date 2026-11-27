-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.psd_sub_of_quad_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:25:52.843492+00:00
-- url     : https://prove2.me/submissions/57154474-3290-4d0f-8be0-6bda97018221

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStB
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
open Matrix
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {r : ℕ} {P Q : Matrix (Fin r) (Fin r) ℂ} (hP : P.IsHermitian)
    (hQ : Q.IsHermitian) (h : ∀ c : Fin r → ℂ, (star c ⬝ᵥ Q *ᵥ c).re ≤ (star c ⬝ᵥ P *ᵥ c).re) :
    (P - Q).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hP.sub hQ) fun c => ?_
  have hreal := (hP.sub hQ).im_star_dotProduct_mulVec_self c
  have hsplit : star c ⬝ᵥ (P - Q) *ᵥ c = star c ⬝ᵥ P *ᵥ c - star c ⬝ᵥ Q *ᵥ c := by
    simp [Matrix.sub_mulVec]
  rw [Complex.nonneg_iff]
  refine ⟨?_, hreal.symm⟩
  rw [hsplit, Complex.sub_re]
  linarith [h c]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
