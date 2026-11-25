-- Prove2me | solution 1 for P2M_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_EtaPartialSums_norm_dterm_le__f583cacc7f6d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:45:07.141474+00:00
-- url     : https://prove2.me/submissions/9f681295-5a7e-4250-890e-eaee6fa88c3c

import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_LFunctionEqGOfOneLt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensLsA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex Filter Topology
noncomputable section
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums
open Formalism.FX.LFunctionPartialSum
variable (f : ℕ → ℂ)
private lemma natCast_cpow_neg_sub_succ_eq_mul_integral (s : ℂ) (hs : 0 < s.re) (n : ℕ) (hn : 1 ≤ n) :
    (n : ℂ) ^ (-s) - ((n : ℂ) + 1) ^ (-s) = s * ∫ t in (n : ℝ)..((n : ℝ) + 1), (t : ℂ) ^ (-s - 1) := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have h0 : (0 : ℝ) ∉ Set.uIcc (n : ℝ) ((n : ℝ) + 1) := by
    rw [Set.uIcc_of_le (by linarith)]
    intro h
    linarith [h.1]
  have hne : -s - 1 ≠ -1 := by
    intro h
    apply hs0
    linear_combination -h
  rw [integral_cpow (Or.inr ⟨hne, h0⟩)]
  have e : -s - 1 + 1 = -s := by ring
  rw [e]
  push_cast
  field_simp
  ring
private lemma norm_cpow_neg_sub_succ_le_telescoping (s : ℂ) (hs : 0 < s.re) (n : ℕ) (hn : 1 ≤ n) :
    ‖(n : ℂ) ^ (-s) - ((n : ℂ) + 1) ^ (-s)‖ ≤
      ‖s‖ / s.re * ((n : ℝ) ^ (-s.re) - ((n : ℝ) + 1) ^ (-s.re)) := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have h0 : (0 : ℝ) ∉ Set.uIcc (n : ℝ) ((n : ℝ) + 1) := by
    rw [Set.uIcc_of_le (by linarith)]
    intro h
    linarith [h.1]
  rw [natCast_cpow_neg_sub_succ_eq_mul_integral s hs n hn, norm_mul]
  have hI : ‖∫ t in (n : ℝ)..((n : ℝ) + 1), (t : ℂ) ^ (-s - 1)‖ ≤
      ∫ t in (n : ℝ)..((n : ℝ) + 1), t ^ (-s.re - 1) := by
    refine le_trans (intervalIntegral.norm_integral_le_integral_norm (by linarith)) (le_of_eq ?_)
    refine intervalIntegral.integral_congr ?_
    intro t ht
    rw [Set.uIcc_of_le (by linarith)] at ht
    have htp : 0 < t := lt_of_lt_of_le hnpos ht.1
    show ‖(t : ℂ) ^ (-s - 1)‖ = t ^ (-s.re - 1)
    rw [Complex.norm_cpow_eq_rpow_re_of_pos htp]
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
  have hval : ∫ t in (n : ℝ)..((n : ℝ) + 1), t ^ (-s.re - 1) =
      ((n : ℝ) ^ (-s.re) - ((n : ℝ) + 1) ^ (-s.re)) / s.re := by
    rw [integral_rpow (Or.inr ⟨(by linarith : -s.re - 1 < -1).ne, h0⟩)]
    have e : -s.re - 1 + 1 = -s.re := by ring
    rw [e, div_neg]
    ring
  calc ‖s‖ * ‖∫ t in (n : ℝ)..((n : ℝ) + 1), (t : ℂ) ^ (-s - 1)‖
        ≤ ‖s‖ * (((n : ℝ) ^ (-s.re) - ((n : ℝ) + 1) ^ (-s.re)) / s.re) := by
          rw [← hval]
          exact mul_le_mul_of_nonneg_left hI (norm_nonneg _)
    _ = ‖s‖ / s.re * ((n : ℝ) ^ (-s.re) - ((n : ℝ) + 1) ^ (-s.re)) := by ring
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums
end
end

set_option autoImplicit false
open Complex Filter Topology
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums
open Formalism.FX.LFunctionPartialSum
variable (f : ℕ → ℂ)
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums
theorem _root_.solution {B : ℝ} (hB : ∀ M, ‖Ap f M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) {n : ℕ}
    (hn : 1 ≤ n) :
    ‖dterm f s n‖ ≤ B * (‖s‖ / s.re * ((n : ℝ) ^ (-s.re) - ((n : ℝ) + 1) ^ (-s.re))) := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  rw [dterm, norm_mul]
  exact mul_le_mul (hB n) (norm_cpow_neg_sub_succ_le_telescoping s hs n hn) (norm_nonneg _) hB0
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums
