-- Prove2me | solution 1 for RossSolandGAP.Bound.PR_zeros_can_be_fixed
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:59:58.598564+00:00
-- url     : https://prove2.me/submissions/fb5ee7c9-7d84-4214-b10a-c88eb80afab0

import Definitions.Def_RossSolandGAP_Bound_Model
import Mathlib.Tactic
set_option autoImplicit false
open Finset RossSolandGAP.Bound

private theorem lag_identity {m n : ℕ} (c : Fin m → Fin n → ℝ) (lam : Fin n → ℝ)
    (x : Fin m → Fin n → ℝ) : lagObj c lam x = ∑ j, lam j-∑ i, knapObj c lam i (x i) := by
  have hs : (∑ j, lam j*∑ i, x i j) = ∑ i, ∑ j, lam j*x i j := by
    simp only [Finset.mul_sum]
    exact Finset.sum_comm
  simp_rw [lagObj,cost,knapObj,sub_mul,mul_sub,mul_one,Finset.sum_sub_distrib]
  rw [hs]
  ring

theorem solution {m n : ℕ} (hm : 1 < m) (c r : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (hr : ∀ i j, 0 ≤ r i j) (a : Fin n → Fin m) (ha : IsCheapest c a)
    (x : Fin m → Fin n → ℝ) (hx : FeasibleLag r b x) :
    FeasibleLag r b (fun i j => if a j = i then x i j else 0) ∧
    lagObj c (c2 hm c a) (fun i j => if a j = i then x i j else 0) ≤
      lagObj c (c2 hm c a) x := by
  have hx0 (i : Fin m) (j : Fin n) : 0 ≤ x i j := by
    rcases hx.1 i j with h|h <;> simp [h]
  constructor
  · constructor
    · intro i j
      dsimp only
      split_ifs
      · exact hx.1 i j
      · exact Or.inl rfl
    · intro i
      apply le_trans _ (hx.2 i)
      apply Finset.sum_le_sum
      intro j hj
      dsimp only
      split_ifs
      · exact le_rfl
      · simpa using mul_nonneg (hr i j) (hx0 i j)
  · rw [lag_identity,lag_identity]
    apply sub_le_sub_left
    apply Finset.sum_le_sum
    intro i hi
    unfold knapObj
    apply Finset.sum_le_sum
    intro j hj
    dsimp only
    split_ifs with he
    · exact le_rfl
    · have hci : c2 hm c a j ≤ c i j :=
        Finset.inf'_le _ (Finset.mem_erase.mpr ⟨Ne.symm he,Finset.mem_univ i⟩)
      simpa using mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hci) (hx0 i j)
