-- Prove2me | solution 1 for TDLC.evalHomotopyStepI_refl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:25:23.861127+00:00
-- url     : https://prove2.me/submissions/c6cf9cf6-90f5-4787-8fe4-6f9a53012c3a


import Definitions.Def_TDLC_Solution

set_option autoImplicit true
open TDLC
universe u
namespace TDLC
theorem _root_.solution {A B : Type u} (f : A → B) (x : A) :
    (evalHomotopyStepI (.refl f)).family x = Step.refl (f x) := rfl
end TDLC
