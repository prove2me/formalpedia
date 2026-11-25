-- Prove2me | solution 1 for PositivityTheory.ThKF0.Chr.IsImp.law_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:06:42.541738+00:00
-- url     : https://prove2.me/submissions/a304e10e-5ca6-475e-bc0b-ffc2a83c7f6c

import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_ResAdm
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_SchrodingerApplyZeroOfFst
import Theorems.Thm_PositivityTheory_ThKF0_Chr_extend_dot
import Theorems.Thm_PositivityTheory_ThKF0_Chr_extend_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKF0 PositivityTheory.ThKF0.Chr
open Matrix GlobalTheory.WeilM
variable {R : Type} [CommRing R] [Invertible (2 : R)] {C : TestClass R} {ψ : AddChar R ℂ}
  {κ κ₁ : Type} [Fintype κ] [Fintype κ₁]
namespace PositivityTheory.ThKF0.Chr
namespace IsImp
theorem _root_.solution {S : V R κ ≃ₗ[R] V R κ} {T : Module.End ℂ ((κ → R) → ℂ)} (hT : IsImp C ψ S T) {j : κ₁ → κ}
    (hj : Function.Injective j) : Law C ψ S j (res R j ∘ₗ T) := fun w w₁ hw φ hφ => by
  funext x
  show T _ (Function.extend j x 0) = schr ψ w₁ (fun y => T φ (Function.extend j y 0)) x
  rw [hT.law _ _ hφ]
  simp only [schr, hw.1, extend_dot hj, hw.2, extend_add hj]
end IsImp
end PositivityTheory.ThKF0.Chr
