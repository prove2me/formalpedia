-- Prove2me | solution 1 for PutermanMDP.Sensitive.complementary_rank
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T03:03:14.041974+00:00
-- url     : https://prove2.me/submissions/ae32e0f3-f48b-4096-b47e-a7ef14708205

import Mathlib

theorem solution (m : ℕ) (F H : Matrix (Fin m) (Fin m) ℝ)
    (hfull : (F + H).rank = m) (hzero : F * H = 0) :
    F.rank + H.rank = m := by
  have h1 := Matrix.rank_add_rank_le_card_of_mul_eq_zero hzero
  simp only [Fintype.card_fin] at h1
  have h2 : (F + H).rank ≤ F.rank + H.rank := by
    unfold Matrix.rank
    have e : (F + H).mulVecLin = F.mulVecLin + H.mulVecLin := by
      ext v i; simp [Matrix.add_mulVec]
    rw [e]
    calc _ ≤ Module.finrank ℝ ↥(LinearMap.range F.mulVecLin ⊔ LinearMap.range H.mulVecLin) :=
          Submodule.finrank_mono (LinearMap.range_add_le _ _)
      _ ≤ _ := Submodule.finrank_add_le_finrank_add_finrank _ _
  omega

