-- Prove2me | solution 1 for TDLC.Path.parity_concat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:25:40.204814+00:00
-- url     : https://prove2.me/submissions/697513b9-dd46-412f-bc83-96e9e045bd12


import Definitions.Def_TDLC_Solution
import Theorems.Thm_TDLC_bxor_assoc

set_option autoImplicit true
open TDLC
universe u
namespace TDLC
namespace Path
theorem _root_.solution {A : Type u} {x y z : A}
    (p : Path x y) (q : Path y z) :
    Path.parity (p ++ₚ q) = bxor (Path.parity p) (Path.parity q) := by
  induction p with
  | nil => rfl
  | seq s p ih =>
      change
        bxor (Step.parity s) (Path.parity (p ++ₚ q)) =
          bxor (bxor (Step.parity s) (Path.parity p)) (Path.parity q)
      rw [ih]
      exact (bxor_assoc _ _ _).symm
end Path
end TDLC
