-- Prove2me | solution 1 for PositivityTheory.ThKF0.Chr.extend_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:59:45.070053+00:00
-- url     : https://prove2.me/submissions/4ab29961-6133-483f-b6c0-743403bf0206

import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_ResAdm
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_SchrodingerApplyZeroOfFst

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
omit [Invertible (2 : R)] [Fintype κ] [Fintype κ₁]
namespace PositivityTheory.ThKF0.Chr
theorem _root_.solution {j : κ₁ → κ} (hj : Function.Injective j) (a b : κ₁ → R) :
    Function.extend j (a + b) 0 = Function.extend j a 0 + Function.extend j b 0 := by
  funext k
  by_cases h : ∃ x, j x = k
  · obtain ⟨x, rfl⟩ := h
    simp [hj.extend_apply]
  · simp [Function.extend_apply' _ _ _ h]
end PositivityTheory.ThKF0.Chr
