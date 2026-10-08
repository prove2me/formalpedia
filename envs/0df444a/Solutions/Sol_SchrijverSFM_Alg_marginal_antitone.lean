-- Prove2me | solution 1 for SchrijverSFM.Alg.marginal_antitone
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T01:30:10.039155+00:00
-- url     : https://prove2.me/submissions/f021d4b8-2bbf-43d4-ba47-dec6df004953

import Mathlib
import Definitions.Def_SchrijverSFM_Alg_Setting
open SchrijverSFM.Alg

open NonmonotoneSubmod.Shared

theorem solution {n : ℕ} (f : Finset (Fin n) → ℝ) (hsub : Submodular f) :
    ∀ X Y : Finset (Fin n), X ⊆ Y → ∀ v : Fin n, v ∉ Y →
      f (insert v Y) - f Y ≤ f (insert v X) - f X := by
  intro X Y hXY v hv
  have hu : insert v X ∪ Y = insert v Y := by
    ext a
    simp only [Finset.mem_union, Finset.mem_insert]
    constructor
    · rintro ((rfl | ha) | ha)
      · exact Or.inl rfl
      · exact Or.inr (hXY ha)
      · exact Or.inr ha
    · rintro (rfl | ha)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr ha
  have hi : insert v X ∩ Y = X := by
    ext a
    simp only [Finset.mem_inter, Finset.mem_insert]
    constructor
    · rintro ⟨rfl | ha, hy⟩
      · exact False.elim (hv hy)
      · exact ha
    · intro ha
      exact ⟨Or.inr ha, hXY ha⟩
  have h := hsub (insert v X) Y
  rw [hu, hi] at h
  linarith

#print axioms solution
