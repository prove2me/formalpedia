-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.vol_fdQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:09:07.847094+00:00
-- url     : https://prove2.me/submissions/691ffc66-d712-45ad-b487-340b66a81d5e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_MemSpanBn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_TileIntegral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_MemSpanMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_finrank_V
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_fdQ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
open ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory MeasureTheory.Measure Complex Module Set Submodule
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
theorem _root_.solution (X : PT E) {q : ℕ} (hq : 1 ≤ q) : volume.real (ZSpan.fundamentalDomain (bQ X hq)) =
    (((q : ℝ) ^ Fintype.card (Idx X.dim)) ^ 2)⁻¹ * volume.real (ZSpan.fundamentalDomain X.b) := by
  rw [fdQ, measureReal_def, Measure.addHaar_preimage_smul volume (q_ne hq), finrank_V, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _), measureReal_def]
  congr 1
  rw [abs_inv, abs_of_pos (pow_pos (Nat.cast_pos.mpr (by omega)) _)]
  ring
end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
