-- Prove2me | solution 1 for P2M_MellinDuality_val_neg_of_ne_zero__83959e09f3a6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:44:06.002957+00:00
-- url     : https://prove2.me/submissions/6b3bcdc3-b103-407c-8455-47d69cb4a2ff

module
public import Definitions.Def_MellinDuality_Defs
public import Definitions.Def_MellinDuality_Half

set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace MellinDuality
theorem _root_.solution {x : ZMod p} (hx : x ≠ 0) : (-x).val = p - x.val := by
  rw [ZMod.neg_val, ite_eq_right_iff.mpr (fun h => absurd h hx)]
end MellinDuality
