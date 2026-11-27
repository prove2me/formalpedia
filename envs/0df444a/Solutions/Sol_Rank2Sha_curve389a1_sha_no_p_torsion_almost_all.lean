-- Prove2me | solution 1 for Rank2Sha.curve389a1_sha_no_p_torsion_almost_all
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @barindersbanwait
-- created : 2026-11-26T23:49:20.940487+00:00
-- url     : https://prove2.me/submissions/2560048c-073c-43e4-89ac-9e86bc662c02
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.Finset.Basic
import Definitions.Def_Rank2Sha_Kurihara389
import Definitions.Def_Rank2Sha_TateShafarevich
import Theorems.Thm_Rank2Sha_curve389a1_kuriharaNumber_ne_zero
import Theorems.Thm_Rank2Sha_curve389a1_sha_no_p_torsion_of_kuriharaNumber_ne_zero

/-!
# Reduction of `Rank2Sha.curve389a1_sha_no_p_torsion_almost_all`

Let `S₀` be the finite set of `Rank2Sha.curve389a1_kuriharaNumber_ne_zero` (K2) and `S₁` that
of `Rank2Sha.curve389a1_sha_no_p_torsion_of_kuriharaNumber_ne_zero`. For a prime `p` outside
`S₀ ∪ S₁`, K2 gives distinct Kolyvagin primes `l₁, l₂` with `δ_{l₁l₂} ≠ 0`, and the second
statement turns that pair into `Ш(E/ℚ)[p] = 0`.
-/

open Rank2Sha in
theorem solution :
    ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S →
      ∀ x : curve389a1.tateShafarevich, p • x = 0 → x = 0 := by
  obtain ⟨S₀, hS₀⟩ := curve389a1_kuriharaNumber_ne_zero
  obtain ⟨S₁, hS₁⟩ := curve389a1_sha_no_p_torsion_of_kuriharaNumber_ne_zero
  refine ⟨S₀ ∪ S₁, fun p hp hpS => ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  rw [Finset.mem_union, not_or] at hpS
  obtain ⟨l₁, l₂, _, _, hne, hk₁, hk₂, hδ⟩ := hS₀ p hpS.1
  exact hS₁ p hpS.2 l₁ l₂ hne hk₁ hk₂ hδ
