-- Prove2me | solution 1 for UpperTheory.Mu.numeric_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:11:35.192783+00:00
-- url     : https://prove2.me/submissions/a5d8eda0-1d56-4ead-9c6d-e8f7653e8bc1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LamLowNumericalEnd
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RootsOfUnity_MassNumeric
import Theorems.Thm_GlobalTheory_lamLow_numerical_end


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.Mu
namespace UpperTheory.Mu
theorem _root_.solution {ι : Type} [Fintype ι] {w : ℕ} (f n r : ℕ) (hcard : Fintype.card ι = f) (L' dmax mass dim idx nrm E dO dS : ℝ)
    (H dk J deg : ι → ℝ) (h8 : 8 ≤ n) (h2 : 2 * r ≤ n) (h1 : 1 ≤ r) (hf : 1 ≤ f) (hL : (5.5 : ℝ) ≤ L') (hn : Real.log n ≤ L')
    (hd0 : 0 ≤ dmax) (hd : Real.log (dmax + 2) ≤ 2 * L') (hw0 : 0 < w) (hw : w ≤ 8 * f ^ 2)
    (hm : 1 / ((w : ℝ) ^ n * (n.factorial : ℝ)) ≤ mass) (hdim : 1 ≤ dim)
    (hidx : idx * nrm = dS⁻¹) (hE : Real.exp (-(r * (2 * f))) ≤ E) (hO : 0 < dO ∧ dO ≤ Real.exp (2 * (r * (2 * f))))
    (hS : 0 < dS ∧ dS ≤ Real.exp (2 * (r * (2 * f)))) (hH : ∀ ρ, 0 < H ρ) (hk : ∀ ρ, 1 ≤ dk ρ) (hJ : ∀ ρ, 0 < J ρ)
    (hdeg : ∀ ρ, 0 ≤ deg ρ ∧ deg ρ ≤ dmax)
    (hJb : ∀ ρ, Real.log (J ρ)⁻¹ ≤ 2 + (r : ℝ) ^ 2 * Real.log (2 * Real.sqrt 2 * (r : ℝ) ^ 2 * n * (deg ρ + 2))) :
    0 < (∏ ρ, dk ρ) * dim * (idx * mass) * (∏ ρ, H ρ) * nrm / dO * (∏ ρ, J ρ) * E ∧
      ∑ ρ, Real.log (H ρ) - 8 * f * (n : ℝ) ^ 2 * L' ≤
        Real.log ((∏ ρ, dk ρ) * dim * (idx * mass) * (∏ ρ, H ρ) * nrm / dO * (∏ ρ, J ρ) * E) := by
  obtain ⟨e⟩ : Nonempty (Fin f ≃ ι) := ⟨(Fintype.equivFinOfCardEq hcard).symm⟩
  have hw1 : (0 : ℝ) < w := by exact_mod_cast hw0
  have hc : 0 < ((w : ℝ) / 2) ^ n := by positivity
  have hm' : 1 / ((2 : ℝ) ^ n * (n.factorial : ℝ)) ≤ ((w : ℝ) / 2) ^ n * mass := by
    refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left hm hc.le)
    have : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
    rw [div_pow]
    field_simp
  have hm0 : 0 < mass := lt_of_lt_of_le (by positivity) hm
  have hE0 : 0 < E := lt_of_lt_of_le (Real.exp_pos _) hE
  have hr : (1 : ℝ) ≤ r := by exact_mod_cast h1
  have hn8 : (8 : ℝ) ≤ n := by exact_mod_cast h8
  have hrn : 2 * (r : ℝ) ≤ n := by exact_mod_cast h2
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hs : Real.sqrt 2 ≤ 3 / 2 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  have key := GlobalTheory.lamLow_numerical_end f n r L' dmax (((w : ℝ) / 2) ^ n * mass * dim) 1 _ (fun a => H (e a)) (fun _ => 1) (fun a => dk (e a))
    (fun a => (J (e a))⁻¹) h8 h2 h1 hf hL hn hd0 hd (hm'.trans (le_mul_of_one_le_right (mul_pos hc hm0).le hdim)) one_pos
    (by rw [Real.log_one, abs_zero]; positivity)
    (fun a => ⟨hH _, le_rfl, hk _, inv_pos.2 (hJ _), (hJb _).trans (by
      have := (hdeg (e a)).1
      have := (hdeg (e a)).2
      gcongr
      linarith)⟩) rfl
  rw [e.sum_comp fun ρ => Real.log (H ρ), e.prod_comp fun ρ => H ρ * 1 * dk ρ / (J ρ)⁻¹] at key
  have hP : 0 < mass * dim * 1 * ∏ ρ, H ρ * 1 * dk ρ / (J ρ)⁻¹ := by
    refine mul_pos (by positivity) (Finset.prod_pos fun ρ _ => ?_)
    have := hH ρ; have := hk ρ; have := hJ ρ
    positivity
  have hlw : Real.log (((w : ℝ) / 2) ^ n) ≤ 4 * (n * f) := by
    have b0 : (w : ℝ) / 2 ≤ (2 * f) ^ 2 := by
      have : (w : ℝ) ≤ 8 * (f : ℝ) ^ 2 := by exact_mod_cast hw
      linarith
    have b1 := Real.log_le_log (by positivity) b0
    have b2 := Real.log_le_sub_one_of_pos (x := 2 * (f : ℝ)) (by positivity)
    rw [Real.log_pow] at b1 ⊢
    push_cast at b1
    have : Real.log ((w : ℝ) / 2) ≤ 4 * f := by linarith only [b1, b2]
    linarith only [mul_le_mul_of_nonneg_left this (Nat.cast_nonneg (α := ℝ) n)]
  rw [show ((w : ℝ) / 2) ^ n * mass * dim * 1 * ∏ ρ, H ρ * 1 * dk ρ / (J ρ)⁻¹ =
    ((w : ℝ) / 2) ^ n * (mass * dim * 1 * ∏ ρ, H ρ * 1 * dk ρ / (J ρ)⁻¹) by ring, Real.log_mul hc.ne' hP.ne'] at key
  have e1 : (∏ ρ, dk ρ) * dim * (idx * mass) * (∏ ρ, H ρ) * nrm / dO * (∏ ρ, J ρ) * E =
      (mass * dim * 1 * ∏ ρ, H ρ * 1 * dk ρ / (J ρ)⁻¹) * (E / (dO * dS)) := by
    simp only [div_inv_eq_mul, mul_one, Finset.prod_mul_distrib]
    have : idx * nrm * dS = 1 := by rw [hidx, inv_mul_cancel₀ hS.1.ne']
    have h3 := hO.1.ne'
    have h4 := hS.1.ne'
    field_simp
    linear_combination ((∏ ρ, dk ρ) * (∏ ρ, H ρ) * (∏ ρ, J ρ)) * this
  have hq : 0 < E / (dO * dS) := div_pos hE0 (mul_pos hO.1 hS.1)
  rw [e1]
  refine ⟨mul_pos hP hq, ?_⟩
  rw [Real.log_mul hP.ne' hq.ne', Real.log_div hE0.ne' (mul_pos hO.1 hS.1).ne', Real.log_mul hO.1.ne' hS.1.ne']
  have a1 := (Real.le_log_iff_exp_le hE0).2 hE
  have a2 := (Real.log_le_iff_le_exp hO.1).2 hO.2
  have a3 := (Real.log_le_iff_le_exp hS.1).2 hS.2
  have a4 : 10 * ((r : ℝ) * f) + 4 * (n * f) ≤ 6 * (f * (n : ℝ) ^ 2 * L') := by
    have b0 : (0 : ℝ) ≤ f := Nat.cast_nonneg _
    have b1 : (r : ℝ) * f ≤ n * f := mul_le_mul_of_nonneg_right (by linarith only [hrn, hr]) b0
    have b2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith only [hn8]
    have b3 : (n : ℝ) * f ≤ (n : ℝ) ^ 2 * f := mul_le_mul_of_nonneg_right b2 b0
    have b4 : (n : ℝ) ^ 2 * f * 5.5 ≤ (n : ℝ) ^ 2 * f * L' := mul_le_mul_of_nonneg_left hL (by positivity)
    have b5 : (0 : ℝ) ≤ (n : ℝ) ^ 2 * f := by positivity
    linarith only [b1, b3, b4, b5]
  linarith only [key, hlw, a1, a2, a3, a4]
end UpperTheory.Mu
