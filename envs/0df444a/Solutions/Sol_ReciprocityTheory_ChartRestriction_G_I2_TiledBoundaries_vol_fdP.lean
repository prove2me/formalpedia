-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.vol_fdP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:25:58.611063+00:00
-- url     : https://prove2.me/submissions/c4383e25-c327-492e-be21-667c89ca2804

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_MemSpanBn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_TileIntegral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_MemSpanMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_fdP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_piR_preimage
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_finrank_V
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
theorem _root_.solution (X : PT E) {q : ℕ} {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim} (hq : 1 ≤ q) (hπ : IsPi X q π) : volume.real (ZSpan.fundamentalDomain (bP X hq hπ)) =
    ((q : ℝ) ^ Fintype.card (Idx X.dim))⁻¹ * volume.real (ZSpan.fundamentalDomain X.b) := by
  have hmeas : MeasurableSet ((fun x => Real.sqrt q • x) ⁻¹' ZSpan.fundamentalDomain X.b) :=
    (ZSpan.fundamentalDomain_measurableSet X.b).preimage (measurable_const_smul _)
  rw [fdP, piR_preimage, measureReal_def,
    ((Ui X hq hπ).measurePreserving).measure_preimage hmeas.nullMeasurableSet,
    Measure.addHaar_preimage_smul volume (sqrt_q_pos hq).ne', finrank_V, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _), measureReal_def]
  congr 1
  rw [abs_inv, pow_mul, Real.sq_sqrt (Nat.cast_nonneg q),
    abs_of_pos (pow_pos (Nat.cast_pos.mpr (by omega)) _)]
end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
