-- Prove2me | solution 1 for Rank2Sha.curve389a1_finite_sha
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @barindersbanwait
-- created : 2026-11-25T12:35:38.6858+00:00
-- url     : https://prove2.me/submissions/56874a59-c229-45fa-aa12-6de9ea7c4ed4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Rank2Sha_Curves
import Definitions.Def_Rank2Sha_TateShafarevich
import Theorems.Thm_Rank2Sha_curve389a1_rank_ge_two
import Theorems.Thm_Rank2Sha_tateShafarevich_isTorsion
import Theorems.Thm_Rank2Sha_finite_of_isTorsion_of_primary
import Theorems.Thm_Rank2Sha_curve389a1_sha_no_p_torsion_almost_all
import Theorems.Thm_Rank2Sha_curve389a1_sha_primary_finite

/-!
# Reduction of `Rank2Sha.curve389a1_finite_sha`

The Shafarevich--Tate group is a torsion group. It has no element of order `p` for `p`
outside a finite set `S` of primes, and its `p`-primary part is finite for every prime
`p`, in particular for `p` in `S`. A torsion abelian group with these two properties is
finite. The rank bound is cited as it stands.
-/

open Rank2Sha in
theorem solution :
    2 ≤ Module.finrank ℤ curve389a1.Point ∧ Finite curve389a1.tateShafarevich := by
  obtain ⟨S, hS⟩ := curve389a1_sha_no_p_torsion_almost_all
  exact ⟨curve389a1_rank_ge_two,
    finite_of_isTorsion_of_primary (tateShafarevich_isTorsion curve389a1) S hS
      (fun p _ hp => curve389a1_sha_primary_finite p hp)⟩
