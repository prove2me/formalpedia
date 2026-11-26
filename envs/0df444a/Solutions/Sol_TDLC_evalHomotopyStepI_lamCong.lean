-- Prove2me | solution 1 for TDLC.evalHomotopyStepI_lamCong
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:25:37.880254+00:00
-- url     : https://prove2.me/submissions/904dd30f-0be6-47c1-80de-61f82e5bc2e1


import Definitions.Def_TDLC_Solution

set_option autoImplicit true
open TDLC
universe u
namespace TDLC
theorem _root_.solution {A B : Type u} {f g : A → B}
    (e : HomotopyStepI f g) (x : A) :
    (evalHomotopyStepI (.lamCong e)).family x =
      Step.apCong (fun k : A → B => k x)
        (Step.lamCong (evalHomotopyStepI e).family) := rfl
end TDLC
