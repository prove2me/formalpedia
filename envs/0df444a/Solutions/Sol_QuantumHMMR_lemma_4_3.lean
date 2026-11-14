-- Prove2me | solution 1 for QuantumHMMR.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @Jesko
-- created : 2026-11-13T19:31:30.584684+00:00
-- url     : https://prove2.me/submissions/542fc84a-4f88-4c47-a8cc-8b4635d774cb

import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 1500000

open scoped BigOperators

namespace PRUPowerSum

/-- Removing the last root leaves a power sum with one fewer term. -/
lemma eliminate_last (D j : ℕ) (b lam : Fin (D + 1) → ℂ) :
    (∑ i, b i * lam i ^ (j + 1)) =
      lam (Fin.last D) * (∑ i, b i * lam i ^ j) +
        ∑ i : Fin D, (b i.castSucc * (lam i.castSucc - lam (Fin.last D))) *
          lam i.castSucc ^ j := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp only [pow_succ, mul_add, Finset.mul_sum]
  conv_rhs => rw [add_right_comm]
  rw [← Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    ring
  · ring

/-- A stronger estimate, without the extra factor `D` in Lemma 4.3. -/
theorem bound (D : ℕ) (hD : 1 ≤ D) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (b lam : Fin D → ℂ) (hlam : ∀ i, ‖lam i‖ ≤ ρ) (B : ℝ)
    (hB : ∀ j : ℕ, 1 ≤ j → j ≤ D → ‖∑ i, b i * lam i ^ j‖ ≤ B) :
    ∀ j : ℕ, D ≤ j →
      ‖∑ i, b i * lam i ^ j‖ ≤
        B * 2 ^ D * ((j + D - 2).choose (D - 1) : ℝ) * ρ ^ (j - D) := by
  induction D generalizing B with
  | zero => omega
  | succ D ih =>
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 1 le_rfl hD)
    by_cases hz : D = 0
    · subst D
      intro j hj
      have hj1 : j = 1 + (j - 1) := by omega
      have hb : ‖b 0 * lam 0‖ ≤ B := by simpa using hB 1 le_rfl le_rfl
      have heq : b 0 * lam 0 ^ j = (b 0 * lam 0) * lam 0 ^ (j - 1) := by
        conv_lhs => rw [hj1, pow_add]
        simp [mul_assoc]
      simp only [Nat.zero_add, Nat.sub_self, Nat.choose_zero_right,
        pow_one, Nat.cast_one, mul_one]
      have hs : (∑ i, b i * lam i ^ j) = b 0 * lam 0 ^ j := Fin.sum_univ_one _
      rw [hs, heq, norm_mul, norm_pow]
      calc
        ‖b 0 * lam 0‖ * ‖lam 0‖ ^ (j - 1) ≤ B * ρ ^ (j - 1) :=
          mul_le_mul hb (pow_le_pow_left₀ (norm_nonneg _) (hlam 0) _) (by positivity) hB0
        _ ≤ B * 2 * ρ ^ (j - 1) := by gcongr; linarith
    · have hDp : 1 ≤ D := by omega
      let c : Fin D → ℂ := fun i => b i.castSucc * (lam i.castSucc - lam (Fin.last D))
      let lam' : Fin D → ℂ := fun i => lam i.castSucc
      have hc : ∀ j : ℕ, 1 ≤ j → j ≤ D → ‖∑ i, c i * lam' i ^ j‖ ≤ 2 * B := by
        intro j hj hjD
        have heq := eliminate_last D j b lam
        change (∑ i, b i * lam i ^ (j + 1)) =
          lam (Fin.last D) * (∑ i, b i * lam i ^ j) + (∑ i, c i * lam' i ^ j) at heq
        have heq' : (∑ i, c i * lam' i ^ j) = (∑ i, b i * lam i ^ (j + 1)) -
            lam (Fin.last D) * (∑ i, b i * lam i ^ j) := by rw [heq]; ring
        rw [heq']
        calc
          _ ≤ ‖∑ i, b i * lam i ^ (j + 1)‖ +
                ‖lam (Fin.last D) * (∑ i, b i * lam i ^ j)‖ := norm_sub_le _ _
          _ = ‖∑ i, b i * lam i ^ (j + 1)‖ +
                ‖lam (Fin.last D)‖ * ‖∑ i, b i * lam i ^ j‖ := by rw [norm_mul]
          _ ≤ B + ρ * B := by
            gcongr
            · exact hB (j + 1) (by omega) (by omega)
            · exact hlam _
            · exact hB j hj (by omega)
          _ ≤ 2 * B := by nlinarith
      have hrest := ih hDp c lam' (fun i => hlam i.castSucc) (2 * B) hc
      intro j hj
      induction j, hj using Nat.le_induction with
      | base =>
        have hchoose : (1 : ℝ) ≤ (((D + 1 + (D + 1) - 2).choose D : ℕ) : ℝ) := by
          exact_mod_cast Nat.choose_pos (by omega : D ≤ D + 1 + (D + 1) - 2)
        have htwo : (1 : ℝ) ≤ 2 ^ (D + 1) := one_le_pow₀ (by norm_num)
        simpa using (hB (D + 1) (by omega) le_rfl).trans
          (show B ≤ B * 2 ^ (D + 1) * (((D + 1 + (D + 1) - 2).choose D : ℕ) : ℝ) by
            nlinarith [mul_le_mul htwo hchoose (by positivity) (by positivity)])
      | succ j hj ihj =>
        have hjD : D ≤ j := by omega
        have hExp : j - D = (j - (D + 1)) + 1 := by omega
        have hExp' : j + 1 - (D + 1) = j - D := by omega
        have hIndex : j + (D + 1) - 2 = j + D - 2 + 1 := by omega
        have hIndex' : j + 1 + (D + 1) - 2 = j + D - 2 + 1 + 1 := by omega
        have hChoose :
            ((j + (D + 1) - 2).choose D : ℝ) + ((j + D - 2).choose (D - 1) : ℝ) ≤
              ((j + 1 + (D + 1) - 2).choose D : ℝ) := by
          have hm := Nat.choose_le_succ (j + D - 2) (D - 1)
          simp only [Nat.succ_eq_add_one] at hm
          have hP := Nat.choose_succ_succ (j + D - 2 + 1) (D - 1)
          have hd : (D - 1).succ = D := by omega
          rw [hd] at hP
          rw [hIndex, hIndex', hP, Nat.cast_add]
          exact_mod_cast (by omega :
            (j + D - 2 + 1).choose D + (j + D - 2).choose (D - 1) ≤
              (j + D - 2 + 1).choose (D - 1) + (j + D - 2 + 1).choose D)
        rw [eliminate_last D j b lam]
        calc
          _ ≤ ‖lam (Fin.last D)‖ * ‖∑ i, b i * lam i ^ j‖ +
                ‖∑ i : Fin D, c i * lam' i ^ j‖ := by
            simpa only [norm_mul, c, lam'] using norm_add_le
              (lam (Fin.last D) * (∑ i, b i * lam i ^ j)) (∑ i : Fin D, c i * lam' i ^ j)
          _ ≤ ρ * (B * 2 ^ (D + 1) * ((j + (D + 1) - 2).choose D : ℝ) *
                ρ ^ (j - (D + 1))) +
                (2 * B) * 2 ^ D * ((j + D - 2).choose (D - 1) : ℝ) * ρ ^ (j - D) := by
            apply add_le_add
            · exact mul_le_mul (hlam _) ihj (norm_nonneg _) (le_of_lt hρ0)
            · exact hrest j hjD
          _ = B * 2 ^ (D + 1) *
                (((j + (D + 1) - 2).choose D : ℝ) + ((j + D - 2).choose (D - 1) : ℝ)) *
                ρ ^ (j - D) := by rw [hExp, pow_succ, pow_succ]; ring
          _ ≤ B * 2 ^ (D + 1) * ((j + 1 + (D + 1) - 2).choose D : ℝ) *
                ρ ^ (j - D) := by gcongr
          _ = _ := by simp only [Nat.add_sub_cancel, hExp']

end PRUPowerSum

theorem solution (D : ℕ) (hD : 1 ≤ D) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (b lam : Fin D → ℂ) (hlam : ∀ i, ‖lam i‖ ≤ ρ) (B : ℝ)
    (hB : ∀ j : ℕ, 1 ≤ j → j ≤ D → ‖∑ i, b i * lam i ^ j‖ ≤ B) :
    ∀ j : ℕ, D ≤ j →
      ‖∑ i, b i * lam i ^ j‖ ≤ B * D * 2 ^ D *
        ((j + D - 2).choose (D - 1) : ℝ) * ρ ^ (j - D) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 1 le_rfl hD)
  intro j hj
  apply (PRUPowerSum.bound D hD ρ hρ0 hρ1 b lam hlam B hB j hj).trans
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  gcongr
  nlinarith

#print axioms solution
