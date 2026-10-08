-- Prove2me | solution 1 for PrimalDualSubgrad.DA.eq_2_11
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T21:09:13.256972+00:00
-- url     : https://prove2.me/submissions/87771d7e-0f32-4e0e-bd01-beb3a6a2e0a7

import Definitions.Def_PrimalDualSubgrad_DA_DualAveraging
open PrimalDualSubgrad.DA

private theorem prox_quadratic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : ProxSetting E) {x : E} (hx : x ∈ P.Q) :
    P.σ / 4 * ‖x - P.x0‖ ^ 2 ≤ P.d x := by
  have hc : P.d ((1 / 2 : ℝ) • P.x0 + (1 / 2 : ℝ) • x) ≤
      (1 / 2 : ℝ) • P.d P.x0 + (1 / 2 : ℝ) • P.d x -
        (1 / 2 : ℝ) * (1 / 2 : ℝ) * (P.σ / 2 * ‖P.x0 - x‖ ^ 2) :=
    P.strongConvexOn_d.2 P.x0_mem hx (by norm_num) (by norm_num) (by norm_num)
  have hmem : (1 / 2 : ℝ) • P.x0 + (1 / 2 : ℝ) • x ∈ P.Q :=
    P.convex_Q P.x0_mem hx (by norm_num) (by norm_num) (by norm_num)
  have hm := P.x0_isMin _ hmem
  rw [P.d_x0] at hc hm
  simp only [smul_eq_mul, norm_sub_rev P.x0 x] at hc
  nlinarith

private theorem V_bdd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : ProxSetting E) {β : ℝ} (hβ : 0 < β) (s : StrongDual ℝ E) :
    BddAbove ((fun x => s (x - P.x0) - β * P.d x) '' P.Q) := by
  let k := β * P.σ / 4
  have hk : 0 < k := by dsimp [k]; positivity [P.σ_pos]
  refine ⟨‖s‖ ^ 2 / (4 * k), ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hd := mul_le_mul_of_nonneg_left (prox_quadratic P hx) hβ.le
  have hs : s (x - P.x0) ≤ ‖s‖ * ‖x - P.x0‖ :=
    (le_abs_self _).trans (s.le_opNorm _)
  have hsquare := mul_nonneg hk.le (sq_nonneg (‖x - P.x0‖ - ‖s‖ / (2 * k)))
  have heq : k * (‖x - P.x0‖ - ‖s‖ / (2 * k)) ^ 2 =
      k * ‖x - P.x0‖ ^ 2 - ‖s‖ * ‖x - P.x0‖ + ‖s‖ ^ 2 / (4 * k) := by
    field_simp
    <;> ring
  rw [heq] at hsquare
  dsimp [k] at *
  nlinarith

open Finset

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (P : ProxSetting E) (lam : ℕ → ℝ) (g : ℕ → StrongDual ℝ E) (x : ℕ → E)
    (k : ℕ) (D : ℝ) (hD : 0 ≤ D) :
    delta P lam g x k D =
      ∑ i ∈ range (k + 1), lam i * g i (x i - P.x0) + xi P D (-(sAgg lam g (k + 1))) := by
  classical
  let s := -(sAgg lam g (k + 1))
  let C := ∑ i ∈ range (k + 1), lam i * g i (x i - P.x0)
  have hne : (FD P D).Nonempty :=
    ⟨P.x0, P.x0_mem, by simpa [P.d_x0] using hD⟩
  have hb : BddAbove ((fun y => s (y - P.x0)) '' FD P D) := by
    obtain ⟨B, hB⟩ := V_bdd P (by norm_num : (0 : ℝ) < 1) s
    refine ⟨B + D, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    have hh := hB ⟨y, hy.1, rfl⟩
    dsimp at hh
    linarith [hy.2]
  have heq (y : E) :
      (∑ i ∈ range (k + 1), lam i * g i (x i - y)) = C + s (y - P.x0) := by
    dsimp [C, s, sAgg]
    simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_sub, map_sub, map_sub]
    ring
  change sSup ((fun y => ∑ i ∈ range (k + 1), lam i * g i (x i - y)) '' FD P D) =
    C + sSup ((fun y => s (y - P.x0)) '' FD P D)
  simp_rw [heq]
  rw [← Set.image_image]
  exact ((OrderIso.addLeft C).map_csSup' (hne.image _) hb).symm

#print axioms solution
