-- Prove2me | solution 1 for TDLC.path2PreservesParity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:26:55.659357+00:00
-- url     : https://prove2.me/submissions/54cf4a3a-f69e-40fc-a791-50ca52c85d39


import Definitions.Def_TDLC_Solution
import Theorems.Thm_TDLC_step2PreservesParity

set_option autoImplicit true
open TDLC
universe u
namespace TDLC
theorem _root_.solution {A : Type u} {x y : A} {p q : Path x y}
    (cells : Path2 p q) : Path.parity p = Path.parity q := by
  induction cells with
  | nil2 p => rfl
  | seq2 cell cells ih => exact (step2PreservesParity cell).trans ih
end TDLC
