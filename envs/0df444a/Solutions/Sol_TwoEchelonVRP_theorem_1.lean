-- Prove2me | solution 1 for TwoEchelonVRP.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T22:08:32.022551+00:00
-- url     : https://prove2.me/submissions/1bb301fb-2041-4bae-98a4-2a8c7a897fdc

import Mathlib
import Definitions.Def_TwoEchelonVRP_Instance
import Definitions.Def_TwoEchelonVRP_zF
import Definitions.Def_TwoEchelonVRP_MultFeasible
import Definitions.Def_TwoEchelonVRP_zRF

open TwoEchelonVRP in
theorem solution {ns nc : ℕ} (I : Instance ns nc) (β : Fin nc → Fin ns → ℝ) (lam : Fin nc → ℝ)
    (μ : Fin ns → ℝ) (μ0 : ℝ) (h : MultFeasible I β lam μ μ0) :
    zRF I β lam μ μ0 ≤ zF I := by
  classical
  obtain ⟨hμ, hμ0, hdual⟩ := h
  unfold zF
  apply le_sInf
  rintro z ⟨v, ⟨x, y, qd, hF, rfl⟩, rfl⟩
  obtain ⟨hL, hxb, hyb, hqi⟩ := hF
  set ξ : Fin nc → Fin ns → ℝ := fun i k => ∑ l, aCoef l i * x k l with hξ
  have hx0 : ∀ k l, 0 ≤ x k l := fun k l => by rcases hxb k l with h | h <;> rw [h]; norm_num
  have ha01 : ∀ (l : Route2 I) i, aCoef l i = 0 ∨ aCoef l i = 1 := by
    intro l i; unfold aCoef; split_ifs <;> simp
  have hcov : ∀ i, ∑ k, ξ i k = 1 := by
    intro i
    rw [← hL.cover i]
    apply Finset.sum_congr rfl; intro k _
    simp only [hξ, aCoef, Finset.sum_filter, ite_mul, one_mul, zero_mul]
  have hξ0 : ∀ i k, 0 ≤ ξ i k := fun i k =>
    Finset.sum_nonneg (fun l _ => mul_nonneg (by rcases ha01 l i with h | h <;> rw [h] <;> norm_num)
      (hx0 k l))
  have hξ1 : ∀ i k, ξ i k ≤ 1 := by
    intro i k
    rw [← hcov i]
    exact Finset.single_le_sum (f := fun k => ξ i k) (fun k _ => hξ0 i k) (Finset.mem_univ k)
  have hξnat : ∀ i k, ∃ N : ℕ, ξ i k = N := by
    intro i k
    have : ∀ l, ∃ b : ℕ, aCoef l i * x k l = b := by
      intro l
      rcases ha01 l i with h1 | h1 <;> rcases hxb k l with h2 | h2
      · exact ⟨0, by rw [h1, h2]; norm_num⟩
      · exact ⟨0, by rw [h1, h2]; norm_num⟩
      · exact ⟨0, by rw [h1, h2]; norm_num⟩
      · exact ⟨1, by rw [h1, h2]; norm_num⟩
    choose b hb using this
    exact ⟨∑ l, b l, by simp only [hξ, hb]; push_cast; rfl⟩
  have hξb : ∀ i k, ξ i k = 0 ∨ ξ i k = 1 := by
    intro i k
    obtain ⟨N, hN⟩ := hξnat i k
    have h1 := hξ1 i k
    rw [hN] at h1 ⊢
    have : N ≤ 1 := by exact_mod_cast h1
    interval_cases N <;> simp
  have hq : ∀ l : Route2 I, (load2 l : ℝ) = ∑ i, (I.q i : ℝ) * aCoef l i := by
    intro l; unfold load2 aCoef; push_cast
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hload : ∀ k, ∑ l, (load2 l : ℝ) * x k l = ∑ i, (I.q i : ℝ) * ξ i k := by
    intro k
    simp only [hq, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    simp only [hξ, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro l _
    ring
  have hRF : RFFeasible I ξ y qd := by
    refine ⟨hcov, fun k => ?_, fun k => ?_, hL.fleet1, hL.cap1, hyb, hqi, hL.off_route, hξb⟩
    · rw [hL.balance k, hload k]
    · rw [← hload k]; exact hL.sat_cap k
  have hle : objRF I β lam μ μ0 ξ y ≤ objF I x y := by
    unfold objRF objF
    have hβ : ∑ k, ∑ i, β i k * ξ i k = ∑ k, ∑ l, x k l * ∑ i, aCoef l i * β i k := by
      apply Finset.sum_congr rfl; intro k _
      simp only [hξ, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro l _
      apply Finset.sum_congr rfl; intro i _
      ring
    have hbound : ∑ k, ∑ l, x k l * ∑ i, aCoef l i * β i k ≤
        ∑ k, ∑ l, x k l * (cost2 I k l - ∑ i, aCoef l i * lam i - μ k - μ0) := by
      apply Finset.sum_le_sum; intro k _
      apply Finset.sum_le_sum; intro l _
      exact mul_le_mul_of_nonneg_left (hdual k l) (hx0 k l)
    have hlam : ∑ k, ∑ l, x k l * ∑ i, aCoef l i * lam i = ∑ i, lam i := by
      have : ∑ k, ∑ l, x k l * ∑ i, aCoef l i * lam i = ∑ i, lam i * ∑ k, ξ i k := by
        calc ∑ k, ∑ l, x k l * ∑ i, aCoef l i * lam i
            = ∑ k, ∑ l, ∑ i, lam i * (aCoef l i * x k l) := by
              apply Finset.sum_congr rfl; intro k _
              apply Finset.sum_congr rfl; intro l _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl; intro i _
              ring
          _ = ∑ k, ∑ i, ∑ l, lam i * (aCoef l i * x k l) := by
              apply Finset.sum_congr rfl; intro k _
              exact Finset.sum_comm
          _ = ∑ i, ∑ k, ∑ l, lam i * (aCoef l i * x k l) := Finset.sum_comm
          _ = ∑ i, lam i * ∑ k, ξ i k := by
              apply Finset.sum_congr rfl; intro i _
              simp only [hξ, Finset.mul_sum]
      rw [this]
      simp [hcov]
    have e : ∑ k, ∑ l, x k l * (cost2 I k l - ∑ i, aCoef l i * lam i - μ k - μ0) =
        ∑ k, ∑ l, cost2 I k l * x k l - ∑ k, ∑ l, x k l * ∑ i, aCoef l i * lam i -
          ∑ k, μ k * ∑ l, x k l - μ0 * ∑ k, ∑ l, x k l := by
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro k _
      apply Finset.sum_congr rfl; intro l _
      rw [← Finset.mul_sum]
      ring
    have hf1 : ∑ k, (I.mSat k : ℝ) * μ k ≤ ∑ k, μ k * ∑ l, x k l := by
      apply Finset.sum_le_sum; intro k _
      rw [mul_comm]
      exact mul_le_mul_of_nonpos_left (hL.fleet_sat k) (hμ k)
    have hf2 : (I.m2 : ℝ) * μ0 ≤ μ0 * ∑ k, ∑ l, x k l := by
      rw [mul_comm]
      exact mul_le_mul_of_nonpos_left hL.fleet2 hμ0
    rw [hβ]
    linarith
  have h1 : zRF I β lam μ μ0 ≤ ((objRF I β lam μ μ0 ξ y : ℝ) : EReal) := by
    unfold zRF
    exact sInf_le ⟨_, ⟨ξ, y, qd, hRF, rfl⟩, rfl⟩
  exact h1.trans (EReal.coe_le_coe_iff.mpr hle)
