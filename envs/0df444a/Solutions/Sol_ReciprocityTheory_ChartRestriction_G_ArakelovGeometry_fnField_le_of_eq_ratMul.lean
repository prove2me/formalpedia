-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.fnField_le_of_eq_ratMul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:42:19.409582+00:00
-- url     : https://prove2.me/submissions/399b1a02-49ae-479a-a692-4045056cfce7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ProjDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsNatMulMemConeRingIntFin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo Polynomial
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} [Finite κ] {D : ℕ}
variable {ι : Type*}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (x x' : ι → Ω) (c : ι → ℚ) (hc : ∀ i, x' i = algebraMap ℚ Ω (c i) * x i) :
    fnField x' ≤ fnField x := by

  rw [fnField, IntermediateField.adjoin_le_iff]
  rintro t ⟨i, j, rfl⟩
  rw [hc i, hc j]
  have e : algebraMap ℚ Ω (c i) * x i / (algebraMap ℚ Ω (c j) * x j) =
      algebraMap ℚ Ω (c i / c j) * (x i / x j) := by
    rw [map_div₀, mul_div_mul_comm]
  rw [e]
  exact mul_mem (IntermediateField.algebraMap_mem _ _) (IntermediateField.subset_adjoin _ _ ⟨i, j, rfl⟩)
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
