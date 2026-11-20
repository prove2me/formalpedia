-- Prove2me | solution 1 for P010.large_prime_path_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:44:12.017921+00:00
-- url     : https://prove2.me/submissions/d26d66bc-a818-40a0-ae4d-fb4c7181cebf

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_large_prime_isolated
public import Theorems.Thm_P010_mem_largePrimes
public import Theorems.Thm_P010_isolated_member_forces_singleton

set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution (n p : ℕ) (a : List ℕ)
    (hp : p ∈ largePrimes n)
    (hchain : NonCoprimeChain a)
    (hnodup : a.Nodup)
    (hmem : p ∈ a)
    (hbound : ∀ t ∈ a, 0 < t ∧ t ≤ n) :
    a = [p] := by
  obtain ⟨hprime, hbig, _⟩ := mem_largePrimes.mp hp
  apply isolated_member_forces_singleton p a hchain hnodup hmem
  intro x hx hne
  obtain ⟨hxpos, hxle⟩ := hbound x hx
  exact large_prime_isolated hprime hbig hxpos hxle hne
end P010
