-- Prove2me | solution 1 for TDLC.evalHomotopyStepI_apCong
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:25:29.309866+00:00
-- url     : https://prove2.me/submissions/9c1e8ca1-00a2-4dac-99fd-3a20e3e95a82


import Definitions.Def_TDLC_Solution

set_option autoImplicit true
open TDLC
universe u
namespace TDLC
theorem _root_.solution {A B C : Type u} (v : B → C)
    {f g : A → B} (e : HomotopyStepI f g) (x : A) :
    (evalHomotopyStepI (.apCong v e)).family x =
      Step.apCong v ((evalHomotopyStepI e).family x) := rfl
end TDLC
