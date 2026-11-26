-- Prove2me | solution 1 for Rank2Sha.curve389a1_kuriharaNumber_ne_zero
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @barindersbanwait
-- created : 2026-11-26T14:28:10.13763+00:00
-- url     : https://prove2.me/submissions/12a8ffc7-1795-49c3-89dc-39bfafd3d948
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.Finset.Range
import Definitions.Def_Rank2Sha_Kurihara389
import Theorems.Thm_Rank2Sha_curve389a1_kurihara_mazurTate
import Theorems.Thm_Rank2Sha_curve389a1_tameDiscriminant_ne_zero

/-!
# Reduction of `Rank2Sha.curve389a1_kuriharaNumber_ne_zero`

Let `S₀` be the finite set of `Rank2Sha.curve389a1_kurihara_mazurTate` (K-MT′). For a prime
`p` outside `S₀ ∪ {0, …, 4} ∪ {389}`, `Rank2Sha.curve389a1_tameDiscriminant_ne_zero` (CHEB′)
gives distinct Kolyvagin primes `l₁, l₂` with `M(l₁, l₂) ≠ 0`, and K-MT′ gives
`δ_{l₁l₂} = M(l₁, l₂)`.
-/

open Rank2Sha in
theorem solution :
    ∃ S₀ : Finset ℕ, ∀ (p : ℕ) [Fact p.Prime], p ∉ S₀ →
      ∃ (l₁ l₂ : ℕ) (_ : Fact l₁.Prime) (_ : Fact l₂.Prime), l₁ ≠ l₂ ∧
        IsKolyvaginPrime p l₁ ∧ IsKolyvaginPrime p l₂ ∧
          kuriharaNumber389 p l₁ l₂ ≠ 0 := by
  obtain ⟨S₀, hS₀⟩ := curve389a1_kurihara_mazurTate
  refine ⟨S₀ ∪ Finset.range 5 ∪ {389}, fun p _ hp => ?_⟩
  simp only [Finset.mem_union, Finset.mem_range, Finset.mem_singleton, not_or, not_lt] at hp
  obtain ⟨⟨hpS, hp5⟩, hp389⟩ := hp
  obtain ⟨l₁, l₂, _, _, hne, hk₁, hk₂, hM⟩ := curve389a1_tameDiscriminant_ne_zero p hp5 hp389
  exact ⟨l₁, l₂, inferInstance, inferInstance, hne, hk₁, hk₂,
    (hS₀ p hpS l₁ l₂ hne hk₁ hk₂).trans_ne hM⟩
