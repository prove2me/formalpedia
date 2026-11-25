-- Prove2me | solution 1 for QuarticPairing.eq_zero_of_isBigO
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:35:20.313373+00:00
-- url     : https://prove2.me/submissions/d15c39d8-8f07-41e8-9849-8045b791760a

module
public import Definitions.Def_QuarticPairing_Pairing
public import Definitions.Def_QuarticPairing_Inconsistency

set_option autoImplicit true
@[expose] public section
public section
open Complex Filter Asymptotics Finset
noncomputable section
open QuarticPairing
namespace QuarticPairing
theorem _root_.solution {b : ℂ}
    (h : (fun X : ℕ => b * ((((X : ℝ) ^ ((3 : ℝ) / 4) : ℝ)) : ℂ)) =O[atTop]
      (fun X : ℕ => (X : ℝ) ^ ((5 : ℝ) / 8))) : b = 0 := by
  by_contra hb
  obtain ⟨C, hC⟩ := h.bound
  have hb0 : 0 < ‖b‖ := norm_pos_iff.2 hb
  have ht : Tendsto (fun X : ℕ => ((X : ℝ) ^ ((1 : ℝ) / 8))) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := (hC.and ((ht.eventually_gt_atTop (C / ‖b‖)).and
    (eventually_gt_atTop 0))).exists_forall_of_atTop
  obtain ⟨h1, h2, h3⟩ := hN N le_rfl
  have hX : (0 : ℝ) < N := by exact_mod_cast h3
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hX _), abs_of_pos (Real.rpow_pos_of_pos hX _)] at h1
  have hsplit : (N : ℝ) ^ ((3 : ℝ) / 4) = (N : ℝ) ^ ((1 : ℝ) / 8) * (N : ℝ) ^ ((5 : ℝ) / 8) := by
    rw [← Real.rpow_add hX]; norm_num
  rw [hsplit] at h1
  have h58 : 0 < (N : ℝ) ^ ((5 : ℝ) / 8) := Real.rpow_pos_of_pos hX _
  have : C < ‖b‖ * (N : ℝ) ^ ((1 : ℝ) / 8) := by
    rw [div_lt_iff₀ hb0] at h2; linarith
  nlinarith
end QuarticPairing
