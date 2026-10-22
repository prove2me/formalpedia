-- Prove2me | solution 1 for TradingPostNSW.Leontief.ineq_13
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T17:05:39.972656+00:00
-- url     : https://prove2.me/submissions/8308f3ed-d8b7-4ce5-9951-892e5c5e9490

import Mathlib
import Definitions.Def_TradingPostNSW_Leontief_Setting

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

theorem solution {n m : ℕ} (I : Instance n m) (hI : Standing I) (p : Fin m → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hsum : ∑ j, p j = ∑ i, I.B i) (hφ : ∀ i, 0 < phi I i p)
    (y : Fin n → Fin m → ℝ) (hy : Feasible I y) :
    ∏ i, (u I i (y i)) ^ (I.B i) ≤ ∏ i, (I.B i / phi I i p) ^ (I.B i) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  have hBpos : ∀ i, 0 < I.B i := fun i => lt_of_lt_of_le zero_lt_one (hI.one_le_B i)
  have hy0 : ∀ i j, 0 ≤ y i j := hy.1
  set P : Fin n → ℝ := fun i => u I i (y i) with hP
  have hP0 : ∀ i, 0 ≤ P i := fun i => u_nonneg I hI i (y i) (hy0 i)
  set a : Fin n → ℝ := fun i => P i * phi I i p / I.B i with ha
  have ha0 : ∀ i, 0 ≤ a i := fun i =>
    div_nonneg (mul_nonneg (hP0 i) (hφ i).le) (hBpos i).le
  have hTot : 0 < ∑ i, I.B i := by
    have : (⟨0, hn⟩ : Fin n) ∈ Finset.univ := Finset.mem_univ _
    exact Finset.sum_pos (fun i _ => hBpos i) ⟨_, this⟩
  -- Σ_i P_i φ_i ≤ Σ_i B_i
  have hS : ∑ i, I.B i * a i ≤ ∑ i, I.B i := by
    have e : ∀ i, I.B i * a i = P i * phi I i p := fun i => by
      simp only [ha]; field_simp [(hBpos i).ne']
    calc ∑ i, I.B i * a i = ∑ i, P i * phi I i p := Finset.sum_congr rfl (fun i _ => e i)
      _ ≤ ∑ i, ∑ j, p j * y i j :=
          Finset.sum_le_sum (fun i _ => u_mul_phi_le I hI i p hp (y i) (hy0 i))
      _ = ∑ j, ∑ i, p j * y i j := Finset.sum_comm
      _ = ∑ j, p j := Finset.sum_congr rfl (fun j _ => by rw [← Finset.mul_sum, hy.2 j, mul_one])
      _ = ∑ i, I.B i := hsum
  have hAMGM := Real.geom_mean_le_arith_mean Finset.univ (fun i => I.B i) a
    (fun i _ => (hBpos i).le) hTot (fun i _ => ha0 i)
  have hX0 : 0 ≤ ∏ i, a i ^ I.B i :=
    Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (ha0 i) _)
  have hX : ∏ i, a i ^ I.B i ≤ 1 := by
    have h1 : (∏ i, a i ^ I.B i) ^ (∑ i, I.B i)⁻¹ ≤ 1 := by
      refine le_trans hAMGM ?_
      rw [div_le_one hTot]; exact hS
    have := Real.rpow_le_rpow (Real.rpow_nonneg hX0 _) h1 hTot.le
    rwa [Real.rpow_inv_rpow hX0 hTot.ne', Real.one_rpow] at this
  have hsplit : ∀ i, P i ^ I.B i = a i ^ I.B i * (I.B i / phi I i p) ^ I.B i := by
    intro i
    rw [← Real.mul_rpow (ha0 i) (div_nonneg (hBpos i).le (hφ i).le)]
    congr 1
    simp only [ha]
    field_simp [(hBpos i).ne', (hφ i).ne']
  calc ∏ i, (u I i (y i)) ^ (I.B i) = ∏ i, P i ^ I.B i := rfl
    _ = (∏ i, a i ^ I.B i) * ∏ i, (I.B i / phi I i p) ^ (I.B i) := by
        rw [← Finset.prod_mul_distrib]; exact Finset.prod_congr rfl (fun i _ => hsplit i)
    _ ≤ 1 * ∏ i, (I.B i / phi I i p) ^ (I.B i) := by
        apply mul_le_mul_of_nonneg_right hX
        exact Finset.prod_nonneg (fun i _ => Real.rpow_nonneg
          (div_nonneg (hBpos i).le (hφ i).le) _)
    _ = _ := one_mul _
