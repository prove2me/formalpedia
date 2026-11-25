-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Bump.continuous_FT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:08:45.845112+00:00
-- url     : https://prove2.me/submissions/ddf3d368-6294-4dfd-a299-323f65fd0918

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_ExistsDensity
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplexFourier
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_IntegrableConjPowGaussian
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_continuous_pr
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_continuous_ch
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_norm_ch


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
theorem _root_.solution {h : (ι → ℂ) → ℂ} (hh : Integrable h) : Continuous (FT h) := by
  refine continuous_of_dominated (bound := fun x => ‖h x‖) (fun t => ?_) (fun t => Eventually.of_forall fun x => ?_) hh.norm
    (Eventually.of_forall fun x => ?_)
  · exact (continuous_ch.comp (continuous_pr.comp (continuous_id.prodMk continuous_const)).neg).aestronglyMeasurable.mul hh.1
  · rw [norm_mul, norm_ch, one_mul]
  · exact (continuous_ch.comp (continuous_pr.comp (continuous_const.prodMk continuous_id)).neg).mul continuous_const
end PositivityTheory.ThKG.Loc.Bump
