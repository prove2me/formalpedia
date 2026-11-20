-- Prove2me | solution 1 for P010.mem_middlePrimes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:28:08.221891+00:00
-- url     : https://prove2.me/submissions/3d7d102a-dfaa-4823-8e66-cc2d6d37334c

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof

set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution {n p : ℕ} :
    p ∈ middlePrimes n ↔ Nat.Prime p ∧ n / 3 < p ∧ p ≤ n / 2 := by
  constructor
  · intro h
    obtain ⟨hp, hnot⟩ := Finset.mem_sdiff.mp h
    obtain ⟨hle, hprime⟩ := Nat.mem_primesLE.mp hp
    have hbig : n / 3 < p := by
      by_contra hsmall
      apply hnot
      exact Nat.mem_primesLE.mpr ⟨by omega, hprime⟩
    exact ⟨hprime, hbig, hle⟩
  · rintro ⟨hprime, hbig, hle⟩
    apply Finset.mem_sdiff.mpr
    constructor
    · exact Nat.mem_primesLE.mpr ⟨hle, hprime⟩
    · intro hp
      have hle' := (Nat.mem_primesLE.mp hp).1
      omega
end P010
