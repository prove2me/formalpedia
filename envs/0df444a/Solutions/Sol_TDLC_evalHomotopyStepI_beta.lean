-- Prove2me | solution 1 for TDLC.evalHomotopyStepI_beta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:25:25.682217+00:00
-- url     : https://prove2.me/submissions/7b5cf0f9-139e-4c76-9e22-9ff1824e3ebf


import Definitions.Def_TDLC_Solution

set_option autoImplicit true
open TDLC
universe u
namespace TDLC
theorem _root_.solution {A B : Type u} (f : A → B) (x : A) :
    (evalHomotopyStepI (.beta f)).family x = Step.beta f x := rfl
end TDLC
