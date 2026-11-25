-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AnalyticLimit_mixedForms_all_c66f07fd1005
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:53:33.564523+00:00
-- url     : https://prove2.me/submissions/0f0f419b-6655-4089-9e3e-ab445eabb6bc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_GreenMassZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_GreenMassStep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_GreenMassReplace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_GreenMassError
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_UniformIntegrability

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.AnalyticLimit
open ReciprocityTheory.AnForm.M (mInt)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (ell errE)
noncomputable section
namespace GroundTheory.Heights₂.Heights.AnalyticLimit
theorem _root_.solution {W : Type} [TopologicalSpace W] {D : ℕ} (Om : ReciprocityTheory.AnForm.M.LocPot W)
    (T : Fin (D + 1) → ReciprocityTheory.AnForm.M.LocPot W) : mixedForms Om T (D + 1) = T :=
  funext fun i => if_pos i.isLt
end GroundTheory.Heights₂.Heights.AnalyticLimit
