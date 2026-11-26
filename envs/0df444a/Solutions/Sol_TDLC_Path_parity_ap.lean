-- Prove2me | solution 1 for TDLC.Path.parity_ap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:24:16.241434+00:00
-- url     : https://prove2.me/submissions/7a69d324-4ad9-401d-94b2-69e4204ec97d


import Definitions.Def_TDLC_Solution

set_option autoImplicit true
open TDLC
universe u
namespace TDLC
namespace Path
theorem _root_.solution {A B : Type u} (f : A → B) {x y : A}
    (p : Path x y) : Path.parity (Path.ap f p) = Path.parity p := by
  induction p with
  | nil => rfl
  | seq s p ih =>
      change
        bxor (Step.parity s) (Path.parity (Path.ap f p)) =
          bxor (Step.parity s) (Path.parity p)
      rw [ih]
end Path
end TDLC
