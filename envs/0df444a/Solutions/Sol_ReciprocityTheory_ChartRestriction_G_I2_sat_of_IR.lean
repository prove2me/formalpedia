-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.sat_of_IR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:54:17.763211+00:00
-- url     : https://prove2.me/submissions/d9e0e63e-e058-46ef-bb13-74e4f01c2f6c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ExistsMaximal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
open scoped InnerProductSpace
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {X : PT E} {I : Submodule ℤ (Vsp X.dim)} (hs : ∀ x ∈ X.L, x ∈ IR I → x ∈ I) :
    ∀ x ∈ X.L, ∀ k : ℤ, k ≠ 0 → k • x ∈ I → x ∈ I := by
  intro x hx k hk hkx
  apply hs x hx
  have h1 : (k • x : Vsp X.dim) ∈ IR I := Submodule.subset_span hkx
  have hk' : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
  have h2 : x = (k : ℝ)⁻¹ • (k • x) := by
    rw [← Int.cast_smul_eq_zsmul ℝ, inv_smul_smul₀ hk']
  rw [h2]
  exact Submodule.smul_mem _ _ h1
end ReciprocityTheory.ChartRestriction.G.I2
