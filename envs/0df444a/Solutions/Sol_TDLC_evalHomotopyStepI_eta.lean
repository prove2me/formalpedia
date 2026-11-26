-- Prove2me | solution 1 for TDLC.evalHomotopyStepI_eta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:25:28.485082+00:00
-- url     : https://prove2.me/submissions/47bcf889-b1df-40cb-bcb2-867415322c17


import Definitions.Def_TDLC_Solution

set_option autoImplicit true
open TDLC
universe u
namespace TDLC
theorem _root_.solution {A B : Type u} (f : A → B) :
    (evalHomotopyStepI (@HomotopyStepI.eta A B)).family f = Step.eta f := rfl
end TDLC
