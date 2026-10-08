-- Prove2me | solution 1 for ShorNonsmooth.SpaceDilation.dilation_orth_sq_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T10:25:26.443692+00:00
-- url     : https://prove2.me/submissions/94a2df23-5183-4c3c-a1a5-20851e741dae

import Mathlib
import Definitions.Def_ShorNonsmooth_SpaceDilation_SDGMethod
import Theorems.Thm_ShorNonsmooth_SpaceDilation_inner_sq_add_orth_sq

open ShorNonsmooth.SpaceDilation

/-- `‖R_a(ξ)(c • ξ + w)‖ ^ 2 = a ^ 2 * c ^ 2 + ‖w‖ ^ 2` when `⟨w, ξ⟩ = 0`, `‖ξ‖ = 1`. -/
theorem solution {n : ℕ} (a c : ℝ)
    (ξ w : EuclideanSpace ℝ (Fin n)) (hξ : ‖ξ‖ = 1) (horth : inner ℝ w ξ = 0) :
    ‖dilation a ξ (c • ξ + w)‖ ^ 2 = a ^ 2 * c ^ 2 + ‖w‖ ^ 2 := by
  -- Tenth variant on the Proved-sibling route (`inner_sq_add_orth_sq`, candidate 7111).
  --
  -- 7206 got both projection facts proved and reduced `hrw` to
  --
  --   a • c • ξ + (c • ξ + w - c • ξ) = (a * c) • ξ + w
  --
  -- then failed with `Did not find an occurrence of the pattern ?a - ?a`. That is
  -- `sub_self` failing, because the term is `c • ξ + w - c • ξ`, i.e. of the shape
  -- `?a + ?b - ?a`, not `?a - ?a`. The matching lemma is `add_sub_cancel_left`
  -- (`?a + ?b - ?a = ?b`), which is present in the pinned declaration index.
  --
  -- So: `add_sub_cancel_left` reduces the difference to `w`, and `smul_smul`
  -- reassociates `a • (c • ξ)` into `(a * c) • ξ`.
  have hξξ : inner ℝ ξ ξ = 1 := by
    rw [real_inner_self_eq_norm_sq, hξ]
    norm_num
  have hwξ : inner ℝ w ξ = 0 := horth
  have hξw : inner ℝ ξ w = 0 := by
    simpa only [real_inner_comm] using horth
  -- `P_ξ w = 0`.
  have hPw : (innerSL ℝ ξ).smulRight ξ w = 0 := by
    rw [ContinuousLinearMap.smulRight_apply, coe_innerSL_apply]
    simp only []
    rw [real_inner_comm, hwξ]
    simp
  -- `P_ξ (c • ξ + w) = c • ξ`.  The expansion is complete after the first chain.
  have hPc : (innerSL ℝ ξ).smulRight ξ (c • ξ + w) = c • ξ := by
    rw [ContinuousLinearMap.smulRight_apply, coe_innerSL_apply]
    simp only []
    rw [inner_add_right, real_inner_smul_right, hξξ, hξw]
    ring
  -- `R_a(ξ) (c • ξ + w) = (a * c) • ξ + w`.
  have hrw : dilation a ξ (c • ξ + w) = (a * c) • ξ + w := by
    simp only [dilation]
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply]
    simp only [map_sub, ContinuousLinearMap.id_apply]
    rw [hPc, add_sub_cancel_left, smul_smul]
  -- Pythagoras from the Proved sibling, with coefficient `a * c`.
  rw [hrw]
  have hp := inner_sq_add_orth_sq (n := n) ((a * c) • ξ + w) ξ w (a * c) hξ rfl horth
  calc ‖(a * c) • ξ + w‖ ^ 2 = (a * c) ^ 2 + ‖w‖ ^ 2 := hp
    _ = a ^ 2 * c ^ 2 + ‖w‖ ^ 2 := by ring
