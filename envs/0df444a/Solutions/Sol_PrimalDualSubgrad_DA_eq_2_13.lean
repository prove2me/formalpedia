-- Prove2me | solution 1 for PrimalDualSubgrad.DA.eq_2_13
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T19:31:08.210477+00:00
-- url     : https://prove2.me/submissions/ab552d98-d125-43bf-a384-e49d9c124f2d

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

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (P : ProxSetting E) (lam : ℕ → ℝ) (g : ℕ → StrongDual ℝ E) (x : ℕ → E)
    (k : ℕ) (β D : ℝ) (hβ : 0 < β) (hD : 0 ≤ D) :
    delta P lam g x k D ≤ Delta P lam g x k β D := by
  apply csSup_le
    (show ((fun y => ∑ i ∈ Finset.range (k + 1), lam i * g i (x i - y)) '' FD P D).Nonempty from
      ⟨_, P.x0, ⟨P.x0_mem, by simpa [P.d_x0] using hD⟩, rfl⟩)
  rintro _ ⟨y, hy, rfl⟩
  have hv := le_csSup (V_bdd P hβ (-(sAgg lam g (k + 1)))) ⟨y, hy.1, rfl⟩
  have hm := mul_le_mul_of_nonneg_left hy.2 hβ.le
  have heq :
      (∑ i ∈ Finset.range (k + 1), lam i * g i (x i - y)) =
      (∑ i ∈ Finset.range (k + 1), lam i * g i (x i - P.x0)) +
        (-(sAgg lam g (k + 1))) (y - P.x0) := by
    simp only [sAgg, ContinuousLinearMap.neg_apply, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_sub, map_sub, map_sub]
    ring
  unfold Delta
  dsimp only at hv ⊢
  rw [heq]
  change _ ≤ V P β (-(sAgg lam g (k + 1))) at hv
  linarith

#print axioms solution
