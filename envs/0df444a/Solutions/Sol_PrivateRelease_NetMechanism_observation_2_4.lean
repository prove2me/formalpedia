-- Prove2me | solution 1 for PrivateRelease.NetMechanism.observation_2_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:54:07.736002+00:00
-- url     : https://prove2.me/submissions/bf2728dc-7c0f-4f91-8ec9-33f477179fcb

import Mathlib
import Definitions.Def_PrivateRelease_NetMechanism_Queries

set_option autoImplicit false
open PrivateRelease.NetMechanism

theorem solution {X : Type} (φ : X → Bool) (n : ℕ) (hn : 1 ≤ n) :
    GS (fun z : Fin n → X => countQ φ (inputDB z)) ≤ 1 / (n : ℝ) := by
  have key : ∀ z : Fin n → X, countQ φ (inputDB z) =
      (∑ i, if φ (z i) = true then (1 : ℝ) else 0) / n := by
    intro z
    unfold countQ inputDB
    rw [Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin]
    congr 1
    rw [Finset.sum_boole, Multiset.filter_map, Multiset.card_map]
    rfl
  unfold GS
  have hn0 : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  refine Real.iSup_le (fun p => ?_) hn0
  obtain ⟨i, hi, hj⟩ := p.2
  show |countQ φ (inputDB p.1.1) - countQ φ (inputDB p.1.2)| ≤ 1 / (n : ℝ)
  rw [key, key, ← sub_div, abs_div, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
  · split_ifs <;> simp
  · intro j _ hji
    rw [hj j hji]; simp
  · intro h; exact absurd (Finset.mem_univ i) h
