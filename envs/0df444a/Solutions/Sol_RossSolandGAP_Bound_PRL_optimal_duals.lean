-- Prove2me | solution 1 for RossSolandGAP.Bound.PRL_optimal_duals
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T09:04:40.368781+00:00
-- url     : https://prove2.me/submissions/8545ad8a-2a04-4295-ad03-79621679310d

import Definitions.Def_RossSolandGAP_Bound_Model
import Mathlib.Tactic
set_option autoImplicit false
open Finset RossSolandGAP.Bound

private theorem dual_columns {m n : ℕ} (lam : Fin n → ℝ) (u : Fin m → Fin n → ℝ) :
    dualObjPRL lam u = ∑ j, (lam j-∑ i, u i j) := by
  simp only [dualObjPRL,Finset.sum_sub_distrib]
  rw [Finset.sum_comm]

private theorem column_bound {m n : ℕ} (c : Fin m → Fin n → ℝ) (a : Fin n → Fin m)
    (lam : Fin n → ℝ) (u : Fin m → Fin n → ℝ) (h : DualFeasiblePRL c lam u) (j : Fin n) :
    lam j-∑ i, u i j ≤ c (a j) j := by
  have hu : u (a j) j ≤ ∑ i, u i j := Finset.single_le_sum (fun i _ => h.1 i j) (Finset.mem_univ _)
  have hc := h.2 (a j) j
  linarith

private theorem dual_bound {m n : ℕ} (c : Fin m → Fin n → ℝ) (a : Fin n → Fin m)
    (lam : Fin n → ℝ) (u : Fin m → Fin n → ℝ) (h : DualFeasiblePRL c lam u) :
    dualObjPRL lam u ≤ Z c a := by
  rw [dual_columns]
  exact Finset.sum_le_sum (fun j _ => column_bound c a lam u h j)

theorem solution {m n : ℕ} (hm : 1 < m) (c : Fin m → Fin n → ℝ)
    (a : Fin n → Fin m) (ha : IsCheapest c a) :
    (FeasiblePRL (xPR a) ∧ cost c (xPR a) = Z c a ∧
      ∀ x, FeasiblePRL x → Z c a ≤ cost c x) ∧
    ∀ lam : Fin n → ℝ, (∃ u, IsOptDualPRL c lam u) ↔
      ∀ j, c (a j) j ≤ lam j ∧ lam j ≤ c2 hm c a j := by
  classical
  have hcan : DualFeasiblePRL c (fun j => c (a j) j) (fun _ _ => 0) := by
    constructor
    · intro i j; exact le_rfl
    · intro i j; simpa using ha j i
  have hcanval : dualObjPRL (m := m) (fun j => c (a j) j) (fun _ _ => 0) = Z c a := by
    simp [dualObjPRL,Z]
  constructor
  · refine ⟨?_,?_,?_⟩
    · constructor
      · intro i j
        simp only [xPR]
        split_ifs <;> norm_num
      · intro j
        simp [xPR]
    · rw [cost,Finset.sum_comm]
      simp [xPR,Z]
    · intro x hx
      rw [cost,Finset.sum_comm]
      apply Finset.sum_le_sum
      intro j hj
      calc
        c (a j) j = ∑ i, c (a j) j*x i j := by rw [← Finset.mul_sum,hx.2 j,mul_one]
        _ ≤ ∑ i, c i j*x i j := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (ha j i) (hx.1 i j).1)
  · intro lam
    constructor
    · rintro ⟨u,hu⟩
      have hval : dualObjPRL lam u=Z c a :=
        le_antisymm (dual_bound c a lam u hu.1) (by simpa only [hcanval] using hu.2 _ _ hcan)
      have hcols : ∀ j, lam j-∑ i, u i j = c (a j) j := by
        have hs : ∑ j, (c (a j) j-(lam j-∑ i, u i j))=0 := by
          rw [Finset.sum_sub_distrib,← dual_columns,hval,Z,sub_self]
        have hn (j : Fin n) (_ : j∈univ) : 0 ≤ c (a j) j-(lam j-∑ i, u i j) :=
          sub_nonneg.mpr (column_bound c a lam u hu.1 j)
        intro j
        have he := (Finset.sum_eq_zero_iff_of_nonneg hn).mp hs j (Finset.mem_univ j)
        linarith
      intro j
      have hc := hcols j
      have hsum0 : 0 ≤ ∑ i, u i j := Finset.sum_nonneg (fun i _ => hu.1.1 i j)
      refine ⟨by linarith,?_⟩
      apply Finset.le_inf'
      intro k hk
      have hrest0 : 0 ≤ ∑ i ∈ univ.erase (a j), u i j := Finset.sum_nonneg (fun i _ => hu.1.1 i j)
      have hsum := Finset.sum_erase_add univ (fun i => u i j) (Finset.mem_univ (a j))
      have hca := hu.1.2 (a j) j
      have hrest : ∑ i ∈ univ.erase (a j), u i j=0 := by linarith
      have huk : u k j=0 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hu.1.1 i j)).mp hrest k hk
      simpa only [huk,sub_zero] using hu.1.2 k j
    · intro hlam
      let u : Fin m → Fin n → ℝ := fun i j => if a j=i then lam j-c (a j) j else 0
      have hufeas : DualFeasiblePRL c lam u := by
        constructor
        · intro i j
          dsimp [u]
          split_ifs
          · exact sub_nonneg.mpr (hlam j).1
          · exact le_rfl
        · intro i j
          by_cases he : a j=i
          · simp only [u,he,ite_true]
            ring_nf
            exact le_rfl
          · have hci : c2 hm c a j ≤ c i j := Finset.inf'_le _ (Finset.mem_erase.mpr ⟨Ne.symm he,Finset.mem_univ i⟩)
            simpa only [u,he,ite_false,sub_zero] using (hlam j).2.trans hci
      have huval : dualObjPRL lam u=Z c a := by
        rw [dual_columns]
        simp [u,Z]
      refine ⟨u,hufeas,?_⟩
      intro lam' u' hu'
      rw [huval]
      exact dual_bound c a lam' u' hu'
