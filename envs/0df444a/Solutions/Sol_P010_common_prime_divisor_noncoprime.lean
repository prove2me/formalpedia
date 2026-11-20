-- Prove2me | solution 1 for P010.common_prime_divisor_noncoprime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:28:43.824647+00:00
-- url     : https://prove2.me/submissions/694b4130-0679-4290-a092-ae850ad79705

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof

set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution {p x y : ℕ}
    (hp : Nat.Prime p) (hx : p ∣ x) (hy : p ∣ y) :
    ¬Nat.Coprime x y := by
  exact Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, hx, hy⟩
end P010
