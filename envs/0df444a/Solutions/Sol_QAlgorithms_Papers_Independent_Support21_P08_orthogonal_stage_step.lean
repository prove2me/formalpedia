-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P08.orthogonal_stage_step
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T07:46:42.212621+00:00
-- url     : https://prove2.me/submissions/3319a5e2-59e8-43a4-b171-04e6206855f1

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P08
noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Support21.P08

open QAlgorithms.Papers.Independent.Renew46.P16 (CellIndex)

open QAlgorithms.Papers.Independent.Next46.P12 (PrimitiveIdempotent)

section RingAppendix

variable {H : Type*} [Ring H]

theorem g67d_fP {d : ℕ} (f : Fin d → H) (k : ℕ) (hk : k < d) (hstage : OrthogonalStage f k)
    (i : Fin d) (hi : k < i.val) :
    f i * ∑ j ∈ Finset.univ.filter (fun j : Fin d => j.val ≤ k), f j = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := hstage
  rw [Finset.mul_sum]
  refine Finset.sum_eq_zero (fun j hj => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  rcases lt_or_eq_of_le hj with hj | hj
  · exact (h4 j i hj hi.le).2
  · exact h3 j i (by omega) (by rw [Fin.lt_def]; omega)

theorem g67d_Pf {d : ℕ} (f : Fin d → H) (k : ℕ) (hstage : OrthogonalStage f k)
    (i : Fin d) (hi : i.val ≤ k) :
    f i * ∑ j ∈ Finset.univ.filter (fun j : Fin d => j.val ≤ k), f j = f i := by
  obtain ⟨h1, h2, h3, h4⟩ := hstage
  rw [Finset.mul_sum, Finset.sum_eq_single i]
  · exact h1 i
  · intro j hj hji
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    rcases lt_or_eq_of_le hi with hi' | hi'
    · rcases lt_or_eq_of_le hj with hj' | hj'
      · exact h2 i j hi' hj' (Ne.symm hji)
      · exact (h4 i j hi' (by omega)).1
    · have : j.val < k := by
        rcases lt_or_eq_of_le hj with hj' | hj'
        · exact hj'
        · exact absurd (Fin.ext (by omega)) hji
      exact (h4 j i this (by omega)).2
  · intro h; exact absurd (by simpa using hi) h

theorem solution {d : ℕ} (f : Fin d → H) (k : ℕ)
    (hk : k < d) (hstage : OrthogonalStage f k) :
    OrthogonalStage (orthogonalStep f k) (k + 1) := by
  have hfP := g67d_fP f k hk hstage
  have hPf := g67d_Pf f k hstage
  obtain ⟨h1, h2, h3, h4⟩ := hstage
  set P := ∑ j ∈ Finset.univ.filter (fun j : Fin d => j.val ≤ k), f j with hPdef
  have hstep : ∀ i : Fin d, orthogonalStep f k i = if i.val ≤ k then f i else (1 - P) * f i := by
    intro i; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    rw [hstep]
    split_ifs with hi
    · exact h1 i
    · have := hfP i (by omega)
      calc (1 - P) * f i * ((1 - P) * f i) = (1 - P) * (f i * (1 - P) * f i) := by noncomm_ring
        _ = (1 - P) * f i := by rw [mul_sub, mul_one, this, sub_zero, h1]
  · intro i j hi hj hij
    rw [hstep, hstep, if_pos (by omega), if_pos (by omega)]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | hi' <;>
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | hj'
    · exact h2 i j hi' hj' hij
    · exact (h4 i j hi' (by omega)).1
    · exact (h4 j i hj' (by omega)).2
    · exact absurd (Fin.ext (by omega)) hij
  · intro i j hi hij
    have hij' : i.val < j.val := hij
    rw [hstep, hstep, if_neg (by omega), if_neg (by omega)]
    have := hfP j (by omega)
    have h3' := h3 i j (by omega) hij
    calc (1 - P) * f j * ((1 - P) * f i) = (1 - P) * (f j * f i - f j * P * f i) := by noncomm_ring
      _ = 0 := by rw [h3', this]; simp
  · intro i j hi hj
    rw [hstep, hstep, if_pos (by omega), if_neg (by omega)]
    have hfi := hPf i (by omega)
    have hji : f j * f i = 0 := by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | hi'
      · exact (h4 i j hi' (by omega)).2
      · exact h3 i j (by omega) (by rw [Fin.lt_def]; omega)
    constructor
    · calc f i * ((1 - P) * f j) = f i * f j - f i * P * f j := by noncomm_ring
        _ = 0 := by rw [hfi]; simp
    · calc (1 - P) * f j * f i = (1 - P) * (f j * f i) := by noncomm_ring
        _ = 0 := by rw [hji, mul_zero]

end RingAppendix

end
