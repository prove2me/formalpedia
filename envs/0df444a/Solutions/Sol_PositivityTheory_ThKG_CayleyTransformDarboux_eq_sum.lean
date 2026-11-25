-- Prove2me | solution 1 for PositivityTheory.ThKG.CayleyTransformDarboux.eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:49:48.248598+00:00
-- url     : https://prove2.me/submissions/8d2bd19d-d792-4e6d-98ab-627a51b9fcdf

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreMain
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ToralCohomology_ShiftLow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open FockH1Action PositivityTheory.KReal
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.CayleyTransformDarboux
variable {ι I M : Type} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I] [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.ThKG.CayleyTransformDarboux
theorem _root_.solution (Z : ι → Matrix I I ℂ) : Z = ∑ w, ∑ a, ∑ b, Z w a b • un w a b := by
  ext w a b
  simp only [un, Finset.sum_apply, Pi.smul_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single w, Finset.sum_eq_single a, Finset.sum_eq_single b] <;>
    simp +contextual [Pi.single_apply, Matrix.single_apply, eq_comm]
end PositivityTheory.ThKG.CayleyTransformDarboux
