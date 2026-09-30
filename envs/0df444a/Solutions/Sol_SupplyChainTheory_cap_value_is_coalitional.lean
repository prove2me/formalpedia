-- Prove2me | solution 1 for SupplyChainTheory.cap_value_is_coalitional
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-25T22:22:26.485313+00:00
-- url     : https://prove2.me/submissions/f72684f1-5cbf-425b-b607-a5866f7f1eb9

import Mathlib
import Definitions.Def_SupplyChainTheory_auctions

open SupplyChainTheory

theorem solution {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) :
    IsCoalitionalValue (capValue v) := by
  classical
  -- The feasible values of the allocation problem restricted to `T`.
  set F : Finset (Fin (n + 1)) → Set ℝ := fun T =>
    {w | ∃ y : Fin n → Option (Finset (Fin m)), (∀ i, i.succ ∉ T → y i = none)
      ∧ (∀ i j, i ≠ j → ∀ A B, y i = some A → y j = some B → Disjoint A B)
      ∧ w = ∑ i, (y i).elim 0 (v i)} with hF
  have hval : ∀ T, capValue v T = if (0 : Fin (n + 1)) ∈ T then sSup (F T) else 0 := fun T => rfl
  -- Finitely many allocations, so every value set is bounded above.
  have hbdd : ∀ T, BddAbove (F T) := by
    intro T
    refine (Set.Finite.subset (Set.finite_range
      (fun y : Fin n → Option (Finset (Fin m)) => ∑ i, (y i).elim 0 (v i))) ?_).bddAbove
    rintro w ⟨y, -, -, rfl⟩; exact ⟨y, rfl⟩
  -- The empty allocation is always feasible, with value `0`.
  have hzero : ∀ T, (0 : ℝ) ∈ F T := by
    intro T
    refine ⟨fun _ => none, fun _ _ => rfl, fun i j _ A B hA _ => by simp at hA, by simp⟩
  have hmono : ∀ T T', T ⊆ T' → F T ⊆ F T' := by
    rintro T T' hTT' w ⟨y, hy, hdisj, rfl⟩
    exact ⟨y, fun i hi => hy i (fun h => hi (hTT' h)), hdisj, rfl⟩
  refine ⟨fun T hT => by rw [hval, if_neg hT], fun T T' hTT' => ?_⟩
  rw [hval, hval]
  by_cases hT : (0 : Fin (n + 1)) ∈ T
  · rw [if_pos hT, if_pos (hTT' hT)]
    exact csSup_le_csSup (hbdd T') ⟨0, hzero T⟩ (hmono T T' hTT')
  · rw [if_neg hT]
    split_ifs
    · exact le_csSup (hbdd T') (hzero T')
    · exact le_refl _
