-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Bump.integrable_scale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:48.975806+00:00
-- url     : https://prove2.me/submissions/11da7a45-6365-4478-9b18-5f57f59a3a6a

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_ExistsDensity
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplexFourier
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_IntegrableConjPowGaussian
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
theorem _root_.solution {y : ι → ℂ} (hy : ∀ w, y w ≠ 0) {g : (ι → ℂ) → ℂ} (hg : Integrable g) : Integrable fun x => g (y * x) := by
  have : Integrable g (Measure.map (fun x : ι → ℂ => y * x) volume) := by
    rw [map_mul_volume_pi_complex hy]; exact hg.smul_measure ENNReal.ofReal_ne_top
  exact this.comp_measurable (meas_mul y)
end PositivityTheory.ThKG.Loc.Bump
