-- Prove2me | solution 1 for PositivityTheory.ThKG.CayleyTransformDarboux.Lie.comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:50:12.081865+00:00
-- url     : https://prove2.me/submissions/adc38475-6e34-4b81-b8d3-7a670c1f84d2

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
variable {A M : Type} [Ring A] [Algebra ℂ A] [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.ThKG.CayleyTransformDarboux
namespace Lie
theorem _root_.solution {act : A →ₗ[ℂ] Module.End ℂ M} (h : Lie act) (X Y : A) (x : M) :
    act X (act Y x) = act Y (act X x) + act (X * Y - Y * X) x := by
  have := LinearMap.congr_fun (h X Y) x
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at this
  rw [← this]; abel
end Lie
end PositivityTheory.ThKG.CayleyTransformDarboux
