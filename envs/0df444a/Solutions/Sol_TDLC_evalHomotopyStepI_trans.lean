-- Prove2me | solution 1 for TDLC.evalHomotopyStepI_trans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:25:33.859988+00:00
-- url     : https://prove2.me/submissions/7acb9916-490e-4f3e-9558-17e844b6b39a


import Definitions.Def_TDLC_Solution

set_option autoImplicit true
open TDLC
universe u
namespace TDLC
theorem _root_.solution {A B : Type u} {f g k : A → B}
    (e : HomotopyStepI f g) (d : HomotopyStepI g k) (x : A) :
    (evalHomotopyStepI (.trans e d)).family x =
      Step.trans ((evalHomotopyStepI e).family x)
        ((evalHomotopyStepI d).family x) := rfl
end TDLC
