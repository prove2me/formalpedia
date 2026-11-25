-- Prove2me | solution 1 for PI.VolStabW.TopoGram.hform_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:26:44.451213+00:00
-- url     : https://prove2.me/submissions/299d1d11-bc5e-46a7-81d9-52c0ab8d1e73

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_NuInvLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoGram
import Theorems.Thm_PI_VolStabW_TopoGram_hform_eq

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
theorem _root_.solution (σ : A →+* A) (J G : Matrix n n A) (x y : n → A) :
    Formalism.UG.hform σ J (G *ᵥ x) (G *ᵥ y) = Formalism.UG.hform σ (Formalism.UG.cT σ G * J * G) x y := by
  rw [hform_eq, hform_eq, ← mulVec_mulVec, ← mulVec_mulVec]
  conv_rhs => rw [dotProduct_mulVec, Formalism.UG.cT, vecMul_transpose]
  congr 1
  funext i
  exact RingHom.map_mulVec σ G x i
end PI.VolStabW.TopoGram
