-- Prove2me | solution 1 for PI.VolStabW.TopoGram.hform_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:58:46.168087+00:00
-- url     : https://prove2.me/submissions/43fbd64f-25ee-46f6-aacf-ae5c1a9b9db4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_NuInvLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoGram

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.TopoGram
open Matrix
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
namespace PI.VolStabW.TopoGram
theorem _root_.solution (σ : A →+* A) (J : Matrix n n A) (x y : n → A) :
    Formalism.UG.hform σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]
end PI.VolStabW.TopoGram
