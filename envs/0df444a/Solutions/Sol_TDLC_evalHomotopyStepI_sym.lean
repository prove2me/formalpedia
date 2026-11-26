-- Prove2me | solution 1 for TDLC.evalHomotopyStepI_sym
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:25:32.259354+00:00
-- url     : https://prove2.me/submissions/30da56ce-4dd9-4535-a429-88d7e1b5a415


import Definitions.Def_TDLC_Solution

set_option autoImplicit true
open TDLC
universe u
namespace TDLC
theorem _root_.solution {A B : Type u} {f g : A → B}
    (e : HomotopyStepI f g) (x : A) :
    (evalHomotopyStepI (.sym e)).family x =
      Step.sym ((evalHomotopyStepI e).family x) := rfl
end TDLC
