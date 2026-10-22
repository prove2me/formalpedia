-- Prove2me | solution 1 for SeqLoss.LiabilityGame.liabilityGame_convex
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:28:39.976666+00:00
-- url     : https://prove2.me/submissions/d1d1c098-f2c8-45d4-a0d7-b4ec78a60c1f

import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn
import Definitions.Def_Supermodularity_Cooperative_IsConvexGame
import Definitions.Def_SeqLoss_FixedFraction_Setting
import Definitions.Def_SeqLoss_LiabilityGame_Game

set_option autoImplicit false
open SeqLoss.LiabilityGame

theorem solution {n : ℕ} [NeZero n] (ℓ : Fin n → ℝ) (hℓ : SeqLoss.FixedFraction.IsLoss ℓ) :
    Supermodularity.Cooperative.IsConvexGame (liabilityGame ℓ) := by
  refine ⟨by simp [liabilityGame], ?_⟩
  intro S _ T _
  show liabilityGame ℓ S + liabilityGame ℓ T ≤ liabilityGame ℓ (S ⊔ T) + liabilityGame ℓ (S ⊓ T)
  have hsub1 : ∀ U V : Finset (Fin n), U ⊆ V → ∑ i ∈ U, ℓ i ≤ ∑ i ∈ V, ℓ i := fun U V h =>
    Finset.sum_le_sum_of_subset_of_nonneg h (fun i _ _ => hℓ i)
  have hU : S ⊔ T = S ∪ T := rfl
  have hI : S ⊓ T = S ∩ T := rfl
  rw [hU, hI]
  unfold liabilityGame
  by_cases hS : (0 : Fin n) ∈ S <;> by_cases hT : (0 : Fin n) ∈ T
  · have h1 : (0 : Fin n) ∈ S ∪ T := Finset.mem_union_left _ hS
    have h2 : (0 : Fin n) ∈ S ∩ T := Finset.mem_inter.mpr ⟨hS, hT⟩
    simp only [hS, hT, h1, h2, if_true]
    rw [Finset.sum_union_inter]
  · have h1 : (0 : Fin n) ∈ S ∪ T := Finset.mem_union_left _ hS
    have h2 : (0 : Fin n) ∉ S ∩ T := fun h => hT (Finset.mem_inter.mp h).2
    simp only [hS, hT, h1, h2, if_true, if_false]
    linarith [hsub1 S (S ∪ T) Finset.subset_union_left]
  · have h1 : (0 : Fin n) ∈ S ∪ T := Finset.mem_union_right _ hT
    have h2 : (0 : Fin n) ∉ S ∩ T := fun h => hS (Finset.mem_inter.mp h).1
    simp only [hS, hT, h1, h2, if_true, if_false]
    linarith [hsub1 T (S ∪ T) Finset.subset_union_right]
  · have h1 : (0 : Fin n) ∉ S ∪ T := by
      intro h; rcases Finset.mem_union.mp h with h | h
      · exact hS h
      · exact hT h
    have h2 : (0 : Fin n) ∉ S ∩ T := fun h => hS (Finset.mem_inter.mp h).1
    simp [hS, hT, h1, h2]
