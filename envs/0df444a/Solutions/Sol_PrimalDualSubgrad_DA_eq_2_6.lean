-- Prove2me | solution 1 for PrimalDualSubgrad.DA.eq_2_6
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T19:28:08.997584+00:00
-- url     : https://prove2.me/submissions/5b8a3fa5-0b55-4d1b-85a6-7ffa871f3bd0

import Definitions.Def_PrimalDualSubgrad_DA_ProxSetting
open PrimalDualSubgrad.DA

private theorem prox_quadratic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : ProxSetting E) {x : E} (hx : x ∈ P.Q) :
    P.σ / 2 * ‖x - P.x0‖ ^ 2 ≤ P.d x := by
  let A := P.σ / 2 * ‖x - P.x0‖ ^ 2
  have hd : 0 ≤ P.d x := by simpa [P.d_x0] using P.x0_isMin x hx
  change A ≤ P.d x
  by_contra hn
  have hlt : P.d x < A := lt_of_not_ge hn
  have hA : 0 < A := lt_of_le_of_lt hd hlt
  let t := (A - P.d x) / (2 * A)
  have ht : 0 < t := div_pos (sub_pos.mpr hlt) (by positivity)
  have ht1 : t ≤ 1 := by
    dsimp [t]
    apply (div_le_iff₀ (by positivity : 0 < 2 * A)).mpr
    linarith
  have hmul : t * (2 * A) = A - P.d x := by
    dsimp [t]
    field_simp
  have hm := P.x0_isMin _
    (P.convex_Q hx P.x0_mem ht.le (sub_nonneg.mpr ht1) (by ring : t + (1-t) = 1))
  have hc := P.strongConvexOn_d.2 hx P.x0_mem ht.le (sub_nonneg.mpr ht1)
    (by ring : t + (1-t) = 1)
  rw [P.d_x0] at hm hc
  simp only [smul_eq_mul, mul_zero, add_zero] at hc
  change P.d (t • x + (1-t) • P.x0) ≤ t * P.d x - t * (1-t) * A at hc
  have hineq : (1-t) * A ≤ P.d x := by nlinarith
  nlinarith

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (P : ProxSetting E) (β : ℝ) (hβ : 0 < β) (δ : StrongDual ℝ E) :
    V P β δ ≤ 1 / (2 * P.σ * β) * ‖δ‖ ^ 2 := by
  apply csSup_le (show ((fun x => δ (x - P.x0) - β * P.d x) '' P.Q).Nonempty from
    ⟨_, P.x0, P.x0_mem, rfl⟩)
  rintro _ ⟨x, hx, rfl⟩
  let k := β * P.σ / 2
  have hk : 0 < k := by dsimp [k]; positivity [P.σ_pos]
  have hd := mul_le_mul_of_nonneg_left (prox_quadratic P hx) hβ.le
  have hs : δ (x - P.x0) ≤ ‖δ‖ * ‖x - P.x0‖ :=
    (le_abs_self _).trans (δ.le_opNorm _)
  have hsquare := mul_nonneg hk.le (sq_nonneg (‖x - P.x0‖ - ‖δ‖ / (2 * k)))
  have heq : k * (‖x - P.x0‖ - ‖δ‖ / (2 * k)) ^ 2 =
      k * ‖x - P.x0‖ ^ 2 - ‖δ‖ * ‖x - P.x0‖ + ‖δ‖ ^ 2 / (4 * k) := by
    field_simp
    <;> ring
  rw [heq] at hsquare
  have heq2 : ‖δ‖ ^ 2 / (4 * k) = 1 / (2 * P.σ * β) * ‖δ‖ ^ 2 := by
    dsimp [k]
    field_simp
    <;> ring
  rw [heq2] at hsquare
  dsimp [k] at *
  nlinarith

#print axioms solution
