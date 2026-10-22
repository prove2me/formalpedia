-- Prove2me | solution 1 for TradingPostNSW.Leontief.theorem_4_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T17:08:34.191611+00:00
-- url     : https://prove2.me/submissions/33919d57-c438-4012-95f1-9c982542cfe4

import Mathlib
import Definitions.Def_TradingPostNSW_Leontief_Setting
import Theorems.Thm_TradingPostNSW_Leontief_eps_me_sum_price_eq_total_budget
import Theorems.Thm_TradingPostNSW_Leontief_eq_14
import Theorems.Thm_TradingPostNSW_Leontief_ineq_13

namespace TPmarketAux
open TradingPostNSW.Leontief

variable {n m : ℕ}

lemma mem_D (I : Instance n m) (i : Fin n) (j : Fin m) : j ∈ D I i ↔ 0 < I.v i j := by
  simp [D]

lemma u_eq (I : Instance n m) (hI : Standing I) (i : Fin n) (y : Fin m → ℝ) :
    u I i y = (D I i).inf' (hI.D_nonempty i) (fun j => y j / I.v i j) := by
  simp [u, hI.D_nonempty i]

lemma u_le (I : Instance n m) (hI : Standing I) (i : Fin n) (y : Fin m → ℝ) (j : Fin m)
    (hj : j ∈ D I i) : u I i y ≤ y j / I.v i j := by
  rw [u_eq I hI]; exact Finset.inf'_le _ hj

lemma le_u (I : Instance n m) (hI : Standing I) (i : Fin n) (y : Fin m → ℝ) (t : ℝ)
    (h : ∀ j ∈ D I i, t ≤ y j / I.v i j) : t ≤ u I i y := by
  rw [u_eq I hI]; exact Finset.le_inf' _ _ h

lemma u_nonneg (I : Instance n m) (hI : Standing I) (i : Fin n) (y : Fin m → ℝ)
    (hy : ∀ j, 0 ≤ y j) : 0 ≤ u I i y :=
  le_u I hI i y 0 (fun j _ => div_nonneg (hy j) (hI.v_nonneg i j))

lemma u_mul_le (I : Instance n m) (hI : Standing I) (i : Fin n) (y : Fin m → ℝ)
    (hy : ∀ j, 0 ≤ y j) (j : Fin m) : u I i y * I.v i j ≤ y j := by
  by_cases hj : j ∈ D I i
  · have hv := (mem_D I i j).1 hj
    have := u_le I hI i y j hj
    rwa [le_div_iff₀ hv] at this
  · have hv : I.v i j = 0 := by
      have := hI.v_nonneg i j
      rw [mem_D] at hj; linarith
    rw [hv, mul_zero]; exact hy j

lemma u_scale (I : Instance n m) (hI : Standing I) (i : Fin n) (T : ℝ) :
    u I i (fun j => T * I.v i j) = T := by
  apply le_antisymm
  · obtain ⟨j, hj⟩ := hI.D_nonempty i
    have := u_le I hI i (fun j => T * I.v i j) j hj
    have hv := (mem_D I i j).1 hj
    simpa [mul_div_assoc, div_self hv.ne'] using this
  · apply le_u I hI
    intro j hj
    have hv := (mem_D I i j).1 hj
    rw [mul_div_assoc, div_self hv.ne', mul_one]

/-- Lower bound `u(y) φ_i(p) ≤ p · y`. -/
lemma u_mul_phi_le (I : Instance n m) (hI : Standing I) (i : Fin n) (p : Fin m → ℝ)
    (hp : ∀ j, 0 ≤ p j) (y : Fin m → ℝ) (hy : ∀ j, 0 ≤ y j) :
    u I i y * phi I i p ≤ ∑ j, p j * y j := by
  unfold phi
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have := u_mul_le I hI i y hy j
  nlinarith [hp j]

end TPmarketAux

open TradingPostNSW.Leontief TPmarketAux

theorem solution {n m : ℕ} (I : Instance n m) (ε : ℝ) (p : Fin m → ℝ)
    (x : Fin n → Fin m → ℝ) (hI : Standing I) (hε : 0 < ε) (hME : IsEpsME I ε p x)
    (y : Fin n → Fin m → ℝ) (hy : Feasible I y) :
    NSW I y ≤ (1 + ε) * NSW I x := by
  have hsum := eps_me_sum_price_eq_total_budget I ε p x hI hME
  have hBpos : ∀ i, 0 < I.B i := fun i => lt_of_lt_of_le zero_lt_one (hI.one_le_B i)
  have hux0 : ∀ i, 0 ≤ u I i (x i) := fun i => u_nonneg I hI i (x i) (hME.x_nonneg i)
  have hφ : ∀ i, 0 < phi I i p := by
    intro i
    have h0 : 0 ≤ phi I i p :=
      Finset.sum_nonneg (fun j _ => mul_nonneg (hI.v_nonneg i j) (hME.p_nonneg j))
    rcases h0.lt_or_eq with h | h
    · exact h
    exfalso
    set T := u I i (x i) * (1 + ε) + 1
    have hc : ∑ j, p j * (T * I.v i j) ≤ I.B i := by
      have : ∑ j, p j * (T * I.v i j) = T * phi I i p := by
        unfold phi; rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      rw [this, ← h, mul_zero]; exact (hBpos i).le
    have hT0 : 0 ≤ T := by have := hux0 i; positivity
    have := hME.eps_opt i (fun j => T * I.v i j)
      (fun j => mul_nonneg hT0 (hI.v_nonneg i j)) hc
    rw [u_scale I hI] at this
    linarith
  have hbd : ∀ i, I.B i / phi I i p ≤ u I i (x i) * (1 + ε) := by
    intro i
    obtain ⟨⟨z, hz0, hzc, hze⟩, _⟩ := eq_14 I hI p hME.p_nonneg i (hφ i)
    rw [hze]; exact hME.eps_opt i z hz0 hzc
  have h13 := ineq_13 I hI p hME.p_nonneg hsum hφ y hy
  have hprod : ∏ i, (u I i (y i)) ^ (I.B i) ≤
      (1 + ε) ^ (totalBudget I) * ∏ i, (u I i (x i)) ^ (I.B i) := by
    refine le_trans h13 ?_
    calc ∏ i, (I.B i / phi I i p) ^ (I.B i)
        ≤ ∏ i, (u I i (x i) * (1 + ε)) ^ (I.B i) := by
          apply Finset.prod_le_prod
          · intro i _; exact Real.rpow_nonneg (div_nonneg (hBpos i).le (hφ i).le) _
          · intro i _
            exact Real.rpow_le_rpow (div_nonneg (hBpos i).le (hφ i).le) (hbd i) (hBpos i).le
      _ = (1 + ε) ^ (totalBudget I) * ∏ i, (u I i (x i)) ^ (I.B i) := by
          rw [totalBudget, Real.rpow_sum_of_pos (by linarith) _ _, ← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl (fun i _ => ?_)
          rw [Real.mul_rpow (hux0 i) (by linarith), mul_comm]
  have hY0 : 0 ≤ ∏ i, (u I i (y i)) ^ (I.B i) :=
    Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (u_nonneg I hI i (y i) (hy.1 i)) _)
  have hX0 : 0 ≤ ∏ i, (u I i (x i)) ^ (I.B i) :=
    Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (hux0 i) _)
  have htot0 : 0 ≤ totalBudget I :=
    Finset.sum_nonneg (fun i _ => (hBpos i).le)
  unfold NSW
  calc (∏ i, (u I i (y i)) ^ (I.B i)) ^ (1 / totalBudget I)
      ≤ ((1 + ε) ^ (totalBudget I) * ∏ i, (u I i (x i)) ^ (I.B i)) ^ (1 / totalBudget I) :=
        Real.rpow_le_rpow hY0 hprod (by positivity)
    _ = ((1 + ε) ^ (totalBudget I)) ^ (1 / totalBudget I) *
          (∏ i, (u I i (x i)) ^ (I.B i)) ^ (1 / totalBudget I) :=
        Real.mul_rpow (Real.rpow_nonneg (by linarith) _) hX0
    _ ≤ (1 + ε) * (∏ i, (u I i (x i)) ^ (I.B i)) ^ (1 / totalBudget I) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hX0 _)
        rcases htot0.lt_or_eq with ht | ht
        · rw [← Real.rpow_mul (by linarith), mul_one_div_cancel ht.ne', Real.rpow_one]
        · rw [← ht]; simp; linarith
