-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.nstatement_hyps_consistent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:25:42.357406+00:00
-- url     : https://prove2.me/submissions/f3a8ac3d-7d69-4bc8-93d7-cf4d2cdbb778

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_NstatementHypsConsistent
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_inhab

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
open ReciprocityTheory.ChartRestriction.G.I2 NumberField Complex
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
theorem _root_.solution (q n : ℕ) (hq : 1 ≤ q) :
    ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E) (X : PT E)
      (π : Vsp X.dim →ₗ[ℂ] Vsp X.dim) (s : (Fin 1 → Vsp X.dim) → ℂ)
      (K : Finset (Fin n → Vsp X.dim)),
      1 ≤ q ∧ IsPi X q π ∧ s ∈ X.Sec 1 1 ∧ s ≠ 0 ∧ IsReps X q n π K :=
  ⟨E4, inferInstance, inferInstance, inferInstance, X0, LinearMap.id, fun _ => 1, {0}, hq, inhab q n hq⟩
end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
