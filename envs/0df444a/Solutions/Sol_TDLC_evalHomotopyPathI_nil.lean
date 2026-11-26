-- Prove2me | solution 1 for TDLC.evalHomotopyPathI_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:25:38.354659+00:00
-- url     : https://prove2.me/submissions/3a58d981-9e32-4cdb-bdd6-e1096fd99448


import Definitions.Def_TDLC_Solution

set_option autoImplicit true
open TDLC
universe u
namespace TDLC
theorem _root_.solution {A B : Type u} (f : A → B) (x : A) :
    evalHomotopyPathI (.nil f) x = Path.nil (f x) := rfl
end TDLC
