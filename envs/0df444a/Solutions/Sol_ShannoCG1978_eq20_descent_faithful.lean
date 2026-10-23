-- Prove2me | solution 1 for ShannoCG1978.eq20_descent_faithful
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T03:08:52.314296+00:00
-- url     : https://prove2.me/submissions/4a152799-0a27-4fa3-a150-99a9877ced09

import Mathlib
import Definitions.Def_ShannoCG_SCONB_bfgsUpdate

open Matrix ShannoCG.SCONB

theorem solution {n : ℕ} (p y g : Fin n → ℝ)
    (hpy : 0 < p ⬝ᵥ y) (hg : g ≠ 0) :
    g ⬝ᵥ (-(bfgsUpdate (1 : Matrix (Fin n) (Fin n) ℝ) p y *ᵥ g)) < 0 := by
  unfold bfgsUpdate
  simp only [add_mulVec, sub_mulVec, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul, one_mulVec, vecMul_one,
    dotProduct_neg, dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  set a := p ⬝ᵥ g
  set b := y ⬝ᵥ g
  set c := p ⬝ᵥ y
  set Y := y ⬝ᵥ y
  have hgy : g ⬝ᵥ y = b := dotProduct_comm _ _
  have hgp : g ⬝ᵥ p = a := dotProduct_comm _ _
  rw [hgy, hgp]
  -- ‖g - (a/c) y‖² ≥ 0
  have hsq : 0 ≤ (g - (a / c) • y) ⬝ᵥ (g - (a / c) • y) := by
    simp only [dotProduct]; exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have e : (g - (a / c) • y) ⬝ᵥ (g - (a / c) • y) = g ⬝ᵥ g - 2 * (a / c) * b + (a / c) ^ 2 * Y := by
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul, hgy]
    rw [dotProduct_comm y g, hgy]; ring
  rw [e] at hsq
  have hgg : 0 < g ⬝ᵥ g := by
    simp only [dotProduct]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hg
    exact Finset.sum_pos' (fun j _ => mul_self_nonneg _) ⟨i, Finset.mem_univ _, mul_self_pos.mpr hi⟩
  have key : g ⬝ᵥ g - 2 * a * b / c + (1 + Y / c) * a ^ 2 / c > 0 := by
    have e2 : g ⬝ᵥ g - 2 * a * b / c + (1 + Y / c) * a ^ 2 / c =
        (g ⬝ᵥ g - 2 * (a / c) * b + (a / c) ^ 2 * Y) + a ^ 2 / c := by
      field_simp; ring
    rw [e2]
    rcases eq_or_ne a 0 with ha | ha
    · rw [ha] at hsq ⊢; simp at hsq ⊢; linarith
    · have : 0 < a ^ 2 / c := by positivity
      linarith
  have e3 : -(g ⬝ᵥ g - 1 / c * (b * a + a * b) + (1 + Y / c) * (1 / c) * (a * a)) =
      -(g ⬝ᵥ g - 2 * a * b / c + (1 + Y / c) * a ^ 2 / c) := by ring
  linarith [e3]
