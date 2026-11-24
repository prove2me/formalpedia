-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Bump.integral_scale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:49.344864+00:00
-- url     : https://prove2.me/submissions/6d598fe6-55ad-4631-bd19-ffba6aabe5ff

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_ExistsDensity
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplexFourier
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_IntegrableConjPowGaussian
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_nm_pos
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_map_mul_volume_pi_complex
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_meas_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Loc PositivityTheory.ThKG.Loc.Bump
open MeasureTheory Filter Topology Set
open scoped ComplexConjugate
variable {ι : Type} [Fintype ι]
namespace PositivityTheory.ThKG.Loc.Bump
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {y : ι → ℂ} (hy : ∀ w, y w ≠ 0) {g : (ι → ℂ) → E}
    (hg : AEStronglyMeasurable g volume) : ∫ x, g (y * x) = (nm y)⁻¹ • ∫ x, g x := by
  rw [← integral_map (meas_mul y).aemeasurable (by rw [map_mul_volume_pi_complex hy]; exact hg.smul_measure _), map_mul_volume_pi_complex hy,
    integral_smul_measure, ENNReal.toReal_ofReal (inv_pos.2 (nm_pos hy)).le]
end PositivityTheory.ThKG.Loc.Bump
