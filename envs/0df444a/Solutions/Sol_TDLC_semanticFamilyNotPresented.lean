-- Prove2me | solution 1 for TDLC.semanticFamilyNotPresented
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:25:50.33212+00:00
-- url     : https://prove2.me/submissions/76e18adb-5c72-44a4-ad04-50a81f0d8fae


import Definitions.Def_TDLC_Solution
import Theorems.Thm_TDLC_evaluatedHeadTagConstant

set_option autoImplicit true
open TDLC
universe u
namespace TDLC
theorem _root_.solution :
    ¬ ∃ e : HomotopyStepI (fun _ : Bool => Unit.unit) (fun _ : Bool => Unit.unit),
      ∀ b, (evalHomotopyStepI e).family b = mixedUnitFamily b := by
  rintro ⟨e, h⟩
  have uniform := evaluatedHeadTagConstant e false true
  rw [h false, h true] at uniform
  have impossible : (0 : Nat) = 4 := by
    exact uniform
  exact Nat.noConfusion impossible
end TDLC
