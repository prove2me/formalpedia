-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.bdd_trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:09:01.447777+00:00
-- url     : https://prove2.me/submissions/82c1f701-bbee-4f14-8f76-499d6ce11779

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_TileIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
open MeasureTheory Module Set Submodule
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {ι : Type} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
theorem _root_.solution {s : Set V} (hs : Bornology.IsBounded s) (c : V) :
    Bornology.IsBounded ((fun x => x - c) ⁻¹' s) := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hs
  refine isBounded_iff_forall_norm_le.2 ⟨R + ‖c‖, fun x hx => ?_⟩
  have hxc : ‖x - c‖ ≤ R := hR _ hx
  calc ‖x‖ = ‖(x - c) + c‖ := by rw [sub_add_cancel]
    _ ≤ ‖x - c‖ + ‖c‖ := norm_add_le _ _
    _ ≤ R + ‖c‖ := by gcongr
end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
