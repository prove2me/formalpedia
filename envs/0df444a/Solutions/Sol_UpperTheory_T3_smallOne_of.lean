-- Prove2me | solution 1 for UpperTheory.T3.smallOne_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:46:50.709714+00:00
-- url     : https://prove2.me/submissions/cde16ab9-4062-4b35-b4ea-ec68b4a453e6

import Definitions.Def_Development_AutomorphicArithmetic_ShortNorms_ShortNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_PrimesAPIntervalOfPrimesRel
import Definitions.Def_Development_AutomorphicArithmetic_ShortNorms_SmallOneOf
import Theorems.Thm_GlobalTheory_Lin_primesAPInterval_of_primesRel


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.Mem.An
open UpperTheory UpperTheory.T3
namespace UpperTheory.T3
theorem _root_.solution :
    GlobalTheory.Lin.PrimesRel → SmallOne := by
  intro hP
  obtain ⟨C₀, Cr, cr, c, hC₀, hCr, hcr, hc, hI⟩ := GlobalTheory.Lin.primesAPInterval_of_primesRel hP
  obtain ⟨N, hN⟩ := exists_nat_ge (max (max C₀ 21) (Real.log (200 * Cr) / cr))
  have hN21 : (21:ℝ) ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNC : C₀ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNl : Real.log (200 * Cr) / cr ≤ N := le_trans (le_max_right _ _) hN
  set K : ℝ := (N:ℝ) ^ 2 with hK
  have hNK : (N:ℝ) ≤ K := by nlinarith
  have hK0 : 0 ≤ K := by positivity
  refine ⟨3 * K + 1, by linarith, ?_⟩
  intro M hM
  rcases Nat.lt_or_ge M 3 with hM3 | hM3
  · have hM2 : M = 2 := by omega
    subst hM2
    refine ⟨3, Nat.prime_three, by norm_num, ?_⟩
    have h1 : ((2:ℕ):ℝ) ^ (2:ℝ) ≤ ((2:ℕ):ℝ) ^ (3 * K + 1) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
    have h2 : ((2:ℕ):ℝ) ^ (2:ℝ) = 4 := by norm_num
    push_cast at h1 h2 ⊢
    linarith
  · have hMr : (3:ℝ) ≤ M := by exact_mod_cast hM3
    set B : ℝ := 4 * (M:ℝ) with hB
    have hB12 : (12:ℝ) ≤ B := by linarith
    have hB0 : 0 < B := by linarith
    have hlogB : 1 ≤ Real.log B := by
      rw [Real.le_log_iff_exp_le hB0]
      have := Real.exp_one_lt_d9
      linarith
    set Y : ℝ := B ^ K with hY
    have hY0 : 0 < Y := Real.rpow_pos_of_pos hB0 _
    have hlogY : Real.log Y = K * Real.log B := Real.log_rpow hB0 K
    have hlogY0 : 0 < Real.log Y := by rw [hlogY]; nlinarith
    have hexp : Real.exp (-cr * N) ≤ 1 / (200 * Cr) := by
      have h1 : Real.log (200 * Cr) ≤ cr * N := by
        rw [div_le_iff₀ hcr] at hNl; linarith
      have h2 : Real.exp (Real.log (200 * Cr)) ≤ Real.exp (cr * N) := Real.exp_le_exp.mpr h1
      rw [Real.exp_log (by positivity)] at h2
      rw [show -cr * (N:ℝ) = -(cr * N) by ring, Real.exp_neg, one_div]
      exact inv_anti₀ (by positivity) h2
    have hρ : Formalism.HermitianLattices.GL2PrimeSums.rhoErr Cr cr B Y ≤ 1 / 100 := by
      unfold Formalism.HermitianLattices.GL2PrimeSums.rhoErr
      have e1 : Real.exp (-cr * Real.log Y / Real.log B) ≤ Real.exp (-cr * N) := by
        apply Real.exp_le_exp.mpr
        rw [hlogY, show -cr * (K * Real.log B) / Real.log B = -cr * K by field_simp]
        nlinarith
      have e2 : Real.exp (-cr * √(Real.log Y)) ≤ Real.exp (-cr * N) := by
        apply Real.exp_le_exp.mpr
        have : (N:ℝ) ≤ √(Real.log Y) := by
          rw [show (N:ℝ) = √K by rw [hK, Real.sqrt_sq (by positivity)]]
          apply Real.sqrt_le_sqrt
          rw [hlogY]; nlinarith
        nlinarith
      have e3 : Cr * Real.exp (-cr * N) ≤ 1 / 200 := by
        have := mul_le_mul_of_nonneg_left hexp hCr.le
        rw [show Cr * (1 / (200 * Cr)) = 1 / 200 by field_simp] at this
        exact this
      nlinarith [mul_le_mul_of_nonneg_left e1 hCr.le, mul_le_mul_of_nonneg_left e2 hCr.le]
    have hc1 : B ^ C₀ ≤ Y := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have hc3 : B ^ (7:ℝ) ≤ 1 * Y ^ ((1:ℝ) / 3) := by
      rw [one_mul, hY, ← Real.rpow_mul hB0.le]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by nlinarith)
    have hmain := hI M 1 hM3 (Nat.coprime_one_left M) Y 1 hc1 le_rfl (by simpa using hρ) hc3
    have hpos : 0 < c * 1 * B ^ (-6:ℝ) * Y / Real.log Y := by
      have := Real.rpow_pos_of_pos hB0 (-6:ℝ)
      positivity
    have hcard : 0 < ({p ∈ Finset.Ioc ⌊Y⌋₊ ⌊Y * (1 + 1)⌋₊ | Nat.Prime p ∧ p ≡ 1 [MOD M]}).card := by
      have := lt_of_lt_of_le hpos hmain
      exact_mod_cast this
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hcard
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    obtain ⟨⟨_, hpY⟩, hpp, hpm⟩ := hp
    refine ⟨p, hpp, ?_, ?_⟩
    · have : 1 % M = 1 := Nat.mod_eq_of_lt (by omega)
      rw [← this]; exact hpm
    · have hp2 : (p:ℝ) ≤ 2 * Y := by
        have := Nat.floor_le (show 0 ≤ Y * (1 + 1) by positivity)
        have h' : (p:ℝ) ≤ (⌊Y * (1 + 1)⌋₊ : ℝ) := by exact_mod_cast hpY
        linarith
      have hBM : B ≤ (M:ℝ) ^ (3:ℝ) := by
        rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast, hB]
        have h9 : (9:ℝ) ≤ (M:ℝ) ^ 2 := by nlinarith
        nlinarith
      have hM0 : (0:ℝ) < M := by linarith
      have hYM : Y ≤ (M:ℝ) ^ (3 * K) := by
        rw [hY, Real.rpow_mul hM0.le]
        exact Real.rpow_le_rpow hB0.le hBM hK0
      rw [Real.rpow_add hM0, Real.rpow_one]
      have : 0 < (M:ℝ) ^ (3 * K) := Real.rpow_pos_of_pos hM0 _
      nlinarith
end UpperTheory.T3
