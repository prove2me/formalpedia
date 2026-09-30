-- Prove2me | solution 1 for RossSolandGAP.Bound.substitution_y_eq_one_sub_x
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:55:56.99798+00:00
-- url     : https://prove2.me/submissions/ebe71ae6-de48-4065-9b9e-47af9cccfb48

import Definitions.Def_RossSolandGAP_Bound_Model
import Mathlib.Tactic
set_option autoImplicit false
open Finset RossSolandGAP.Bound

private theorem penalty_eq {m n : ℕ} (hm : 1 < m) (c : Fin m → Fin n → ℝ)
    (a : Fin n → Fin m) (j : Fin n) : pen hm c a j = c2 hm c a j-c (a j) j := by
  obtain ⟨k,hk,hmin⟩ := Finset.exists_mem_eq_inf' (others_nonempty hm (a j)) (fun k => c k j)
  apply le_antisymm
  · have hh := Finset.inf'_le (fun k => c k j-c (a j) j) hk
    change pen hm c a j ≤ c k j-c (a j) j at hh
    simpa only [c2,hmin] using hh
  · apply Finset.le_inf'
    intro k hk
    exact sub_le_sub_right (Finset.inf'_le (fun k => c k j) hk) _

private theorem sum_restrict {m n : ℕ} (a : Fin n → Fin m) (i : Fin m) (v f : Fin n → ℝ)
    (hv : ∀ j, a j ≠ i → v j=0) : ∑ j, f j*v j = ∑ j ∈ Jset a i, f j*v j := by
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro j hj hnot
  have hn : a j ≠ i := by simpa [Jset] using hnot
  simp [hv j hn]

theorem solution {m n : ℕ} (hm : 1 < m) (c r : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (a : Fin n → Fin m) (ha : IsCheapest c a) (i : Fin m) (v : Fin n → ℝ)
    (hv : ∀ j, a j ≠ i → v j = 0) :
    (∀ j, pen hm c a j = c2 hm c a j - c (a j) j) ∧
    ∑ j, (c i j - c2 hm c a j) * v j =
      -(∑ j ∈ Jset a i, pen hm c a j) + ∑ j ∈ Jset a i, pen hm c a j * (1 - v j) ∧
    (∑ j, r i j * v j ≤ b i ↔ dgap r b a i ≤ ∑ j ∈ Jset a i, r i j * (1 - v j)) := by
  refine ⟨penalty_eq hm c a,?_,?_⟩
  · rw [sum_restrict a i v (fun j => c i j-c2 hm c a j) hv]
    rw [← Finset.sum_neg_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have he : a j=i := by simpa [Jset] using hj
    rw [penalty_eq,he]
    ring
  · rw [sum_restrict a i v (r i) hv]
    have hs : ∑ j ∈ Jset a i, r i j*(1-v j) = load r a i-∑ j ∈ Jset a i, r i j*v j := by
      simp only [mul_sub,mul_one,Finset.sum_sub_distrib,load]
    rw [hs,dgap]
    constructor <;> intro h <;> linarith
