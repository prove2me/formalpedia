-- Prove2me | solution 1 for TDLC.transportAlongPathI_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:25:46.840888+00:00
-- url     : https://prove2.me/submissions/9add32dc-a645-433e-b0c2-60cd0af51630


import Definitions.Def_TDLC_Solution

set_option autoImplicit true
open TDLC
universe u
namespace TDLC
theorem _root_.solution {A B : Type u} (f : A → B)
    (x y : A) (q : Path (f x) (f y)) :
    transportAlongPathI (.nil f) x y q = q := rfl
end TDLC
