-- Prove2me | solution 1 for StableMSR.Recovery.parameterEnvelope_bound
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-13T14:32:33.053131+00:00
-- url     : https://prove2.me/submissions/48b89a9c-96a3-4fdc-ae82-68cc74dce6cc

import Definitions.Def_StableMSR_Recovery_Parameters

set_option autoImplicit false

namespace StableMSR.Recovery

/-- A concrete bound for the Table 2 envelope, retaining the inverse-fifth exponent. -/
theorem parameterEnvelope_le (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    (parameterEnvelope ε : ℝ) ≤ 30000000 / ε ^ 5 := by
  let u : ℝ := 1 / ε
  have hu : 1 ≤ u := by
    dsimp [u]
    apply (le_div_iff₀ hε).2
    linarith
  have hu0 : 0 ≤ u := by linarith
  have hu2 : 1 ≤ u ^ 2 := one_le_pow₀ hu
  have hu3 : 1 ≤ u ^ 3 := one_le_pow₀ hu
  have hu4 : 1 ≤ u ^ 4 := one_le_pow₀ hu
  have hu5 : 1 ≤ u ^ 5 := one_le_pow₀ hu
  have h23 : u ^ 2 ≤ u ^ 3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hu) (sq_nonneg u)]
  have h34 : u ^ 3 ≤ u ^ 4 := by nlinarith [mul_nonneg (sub_nonneg.mpr hu) (pow_nonneg hu0 3)]
  have h45 : u ^ 4 ≤ u ^ 5 := by nlinarith [mul_nonneg (sub_nonneg.mpr hu) (pow_nonneg hu0 4)]
  have h25 : u ^ 2 ≤ u ^ 5 := le_trans h23 (le_trans h34 h45)
  have h35 : u ^ 3 ≤ u ^ 5 := le_trans h34 h45
  have h12 : u ≤ u ^ 2 := by nlinarith
  have hfarg : 16 * sigma / ε ^ 2 = 8192 * u ^ 2 := by
    dsimp [sigma, u]
    ring
  have hfew : (fewBound ε : ℝ) ≤ 8193 * u ^ 2 := by
    unfold fewBound
    rw [hfarg]
    have h := Nat.ceil_lt_add_one (show 0 ≤ 8192 * u ^ 2 by positivity)
    linarith
  have hlarg : 1 + 12 * sigma / ε ^ 2 = 1 + 6144 * u ^ 2 := by
    dsimp [sigma, u]
    ring
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (x := (2 : ℝ)) (by norm_num)
    norm_num at h ⊢
    exact h
  have hlog2pos : 0 < Real.log 2 := by linarith
  have hx : 0 < 1 + 6144 * u ^ 2 := by positivity
  have hlower : 0 ≤ Real.logb 2 (1 + 6144 * u ^ 2) :=
    Real.logb_nonneg (by norm_num) (by nlinarith [sq_nonneg u])
  have hlog : Real.logb 2 (1 + 6144 * u ^ 2) ≤ 12288 * u ^ 2 := by
    rw [Real.logb]
    apply (div_le_iff₀ hlog2pos).2
    have hb := Real.log_le_sub_one_of_pos hx
    have hp := mul_nonneg (show 0 ≤ 6144 * u ^ 2 by positivity)
      (show 0 ≤ 2 * Real.log 2 - 1 by linarith)
    nlinarith
  have hlam : (lambda ε : ℝ) ≤ 12289 * u ^ 2 := by
    unfold lambda
    rw [hlarg]
    have h := Nat.ceil_lt_add_one hlower
    linarith
  have hsarg : 12 * chi * (lambda ε : ℝ) / ε =
      1152 * (lambda ε : ℝ) * u := by
    dsimp [chi, u]
    ring
  have hsplit : (splitBound ε : ℝ) ≤ 14156929 * u ^ 3 := by
    unfold splitBound
    rw [hsarg]
    have h := Nat.ceil_lt_add_one (show 0 ≤ 1152 * (lambda ε : ℝ) * u by positivity)
    have hm := mul_le_mul_of_nonneg_right hlam (show 0 ≤ 1152 * u by positivity)
    nlinarith
  have hcarg : growthConstant ε = 1 + 80 * u + 80 * u ^ 2 := by
    dsimp [growthConstant, u]
    ring
  have hc0 : 0 ≤ growthConstant ε := by rw [hcarg]; positivity
  have hc : growthConstant ε ≤ 161 * u ^ 2 := by rw [hcarg]; linarith
  have hcsq : growthConstant ε ^ 2 ≤ 25921 * u ^ 4 := by
    have h := mul_self_le_mul_self hc0 hc
    nlinarith
  have hw : (widthBound ε : ℝ) ≤ 1274960 * u ^ 4 := by
    unfold widthBound
    have h := Nat.ceil_lt_add_one
      (show 0 ≤ 49 * growthConstant ε ^ 2 + 30 * growthConstant ε by positivity)
    linarith
  have hoarg : 12 / ε = 12 * u := by dsimp [u]; ring
  have ho : (ownerBound ε : ℝ) ≤ 12 * u := by
    unfold ownerBound
    rw [hoarg]
    exact Nat.floor_le (by positivity)
  have hw1 : (widthBound ε : ℝ) + 1 ≤ 1274961 * u ^ 4 := by linarith
  have hm : (ownerBound ε : ℝ) * ((widthBound ε : ℝ) + 1) ≤
      15299532 * u ^ 5 := by
    have h := mul_le_mul ho hw1 (by positivity) (by positivity)
    nlinarith
  have henv : (parameterEnvelope ε : ℝ) ≤ 30000000 * u ^ 5 := by
    unfold parameterEnvelope
    push_cast
    linarith
  calc
    (parameterEnvelope ε : ℝ) ≤ 30000000 * u ^ 5 := henv
    _ = 30000000 / ε ^ 5 := by dsimp [u]; ring

end StableMSR.Recovery

open StableMSR.Recovery

theorem solution : ∃ K : ℝ, 0 < K ∧
    ∀ ε : ℝ, 0 < ε → ε < 1 → (parameterEnvelope ε : ℝ) ≤ K / ε ^ 5 := by
  exact ⟨30000000, by norm_num, parameterEnvelope_le⟩
