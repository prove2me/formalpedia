-- Prove2me | solution 1 for PrimalDualSubgrad.DA.eq_2_2
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:42:36.152303+00:00
-- url     : https://prove2.me/submissions/28f80430-9c3f-4040-80cd-c9cc70766ca6

import Definitions.Def_PrimalDualSubgrad_DA_ProxSetting
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
    (P : ProxSetting E) (β₁ β₂ : ℝ) (hβ₁ : 0 < β₁) (hβ : β₁ ≤ β₂) (s : StrongDual ℝ E) :
    V P β₂ s ≤ V P β₁ s := by
  have hne : ((fun x => s (x - P.x0) - β₂ * P.d x) '' P.Q).Nonempty :=
    ⟨_, ⟨P.x0, P.x0_mem, rfl⟩⟩
  apply csSup_le hne
  rintro _ ⟨x, hx, rfl⟩
  have hd : 0 ≤ P.d x := by simpa [P.d_x0] using P.x0_isMin x hx
  have hmul := mul_le_mul_of_nonneg_right hβ hd
  exact (sub_le_sub_left hmul _).trans (le_csSup (V_bdd P hβ₁ s) ⟨x, hx, rfl⟩)

#print axioms solution
