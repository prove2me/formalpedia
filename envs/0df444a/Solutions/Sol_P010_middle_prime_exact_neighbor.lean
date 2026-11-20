-- Prove2me | solution 1 for P010.middle_prime_exact_neighbor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:54:00.888633+00:00
-- url     : https://prove2.me/submissions/af59bc86-7730-4104-a2f2-a0eedbeaf282

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_middle_prime_unique_neighbor

set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution {n p : ℕ} (hp : Nat.Prime p)
    (hthird : n / 3 < p) (hhalf : p ≤ n / 2) :
    ∃ x : ℕ, 0 < x ∧ x ≤ n ∧ x ≠ p ∧ ¬Nat.Coprime p x ∧
      ∀ y : ℕ, 0 < y → y ≤ n → y ≠ p → ¬Nat.Coprime p y → y = x := by
  have hppos : 0 < p := by have := hp.two_le; omega
  refine ⟨2 * p, by omega, by omega, by omega, ?_, ?_⟩
  · apply (hp.dvd_iff_not_coprime).1
    exact ⟨2, by omega⟩
  · intro y hypos hyle hyne hyn
    exact middle_prime_unique_neighbor hp hthird hypos hyle hyne hyn
end P010
