-- Prove2me | solution 1 for P010.mem_intermediatePrimes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:28:18.796432+00:00
-- url     : https://prove2.me/submissions/90b5be6b-4fac-404c-82d7-c16ec9206737

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
    p ∈ intermediatePrimes n ↔
      Nat.Prime p ∧ n / 4 < p ∧ p ≤ n / 3 := by
  constructor
  · intro h
    obtain ⟨hm, hnot⟩ := Finset.mem_sdiff.mp h
    obtain ⟨hle, hp⟩ := Nat.mem_primesLE.mp hm
    have hbig : n / 4 < p := by
      by_contra hsmall
      exact hnot (Nat.mem_primesLE.mpr ⟨by omega, hp⟩)
    exact ⟨hp, hbig, hle⟩
  · rintro ⟨hp, hbig, hle⟩
    apply Finset.mem_sdiff.mpr
    constructor
    · exact Nat.mem_primesLE.mpr ⟨hle, hp⟩
    · intro hsmall
      have hle' := (Nat.mem_primesLE.mp hsmall).1
      omega
end P010
