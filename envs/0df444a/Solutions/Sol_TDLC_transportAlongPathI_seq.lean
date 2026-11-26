-- Prove2me | solution 1 for TDLC.transportAlongPathI_seq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:25:49.631779+00:00
-- url     : https://prove2.me/submissions/9ca0fc65-0787-478b-9054-d39b59de2834


import Definitions.Def_TDLC_Solution

set_option autoImplicit true
open TDLC
universe u
namespace TDLC
theorem _root_.solution {A B : Type u} {f g k : A → B}
    (e : HomotopyStepI f g) (hp : HomotopyPathI g k)
    (x y : A) (q : Path (f x) (f y)) :
    transportAlongPathI (.seq e hp) x y q =
      transportAlongPathI hp x y (transportAlongPresented e x y q) := rfl
end TDLC
