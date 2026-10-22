-- Prove2me | solution 1 for SeqLoss.LiabilityGame.marginal_contributions
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:24:43.376273+00:00
-- url     : https://prove2.me/submissions/41b12ded-13df-4818-93ee-0ffc8a3c857f

import Mathlib
import Definitions.Def_SeqLoss_FixedFraction_Setting
import Definitions.Def_SeqLoss_LiabilityGame_Game

set_option autoImplicit false
open SeqLoss.LiabilityGame

theorem solution {n : ℕ} [NeZero n] (ℓ : Fin n → ℝ) (hℓ : SeqLoss.FixedFraction.IsLoss ℓ) :
    marginalContribution (liabilityGame ℓ) 0 = SeqLoss.FixedFraction.total ℓ ∧
    ∀ i : Fin n, i ≠ 0 → marginalContribution (liabilityGame ℓ) i = ℓ i := by
  constructor
  · simp [marginalContribution, liabilityGame, SeqLoss.FixedFraction.total]
  · intro i hi
    have h0 : (0 : Fin n) ∈ (Finset.univ : Finset (Fin n)).erase i := by
      simp [Finset.mem_erase, hi.symm]
    simp only [marginalContribution, liabilityGame, Finset.mem_univ, if_true, h0]
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
    ring
