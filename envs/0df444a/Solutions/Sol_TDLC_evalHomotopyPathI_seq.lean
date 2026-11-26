-- Prove2me | solution 1 for TDLC.evalHomotopyPathI_seq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:25:43.353433+00:00
-- url     : https://prove2.me/submissions/f6929cff-209d-450e-8675-8046490961c8


import Definitions.Def_TDLC_Solution

set_option autoImplicit true
open TDLC
universe u
namespace TDLC
theorem _root_.solution {A B : Type u} {f g k : A → B}
    (e : HomotopyStepI f g) (hp : HomotopyPathI g k) (x : A) :
    evalHomotopyPathI (.seq e hp) x =
      Path.seq ((evalHomotopyStepI e).family x) (evalHomotopyPathI hp x) := rfl
end TDLC
