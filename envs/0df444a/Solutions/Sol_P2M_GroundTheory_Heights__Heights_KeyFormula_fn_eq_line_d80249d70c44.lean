-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KeyFormula_fn_eq_line_d80249d70c44
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:29:30.241191+00:00
-- url     : https://prove2.me/submissions/3506a654-3d79-46d3-9722-b4c10ed3a7b4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_RigSymFormTauINontrivial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_ThetaThreeFamLinearIndependent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.KeyFormula
open Complex Real MeasureTheory intervalIntegral Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights.KeyFormula
theorem _root_.solution (f : (Fin 1 → ℂ) → ℂ) (z : Fin 1 → ℂ) : f z = f (fun _ => z 0) := by
  congr 1; funext i; fin_cases i; rfl
end GroundTheory.Heights₂.Heights.KeyFormula
