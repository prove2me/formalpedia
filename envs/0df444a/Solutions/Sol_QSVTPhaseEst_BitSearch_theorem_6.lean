-- Prove2me | solution 1 for QSVTPhaseEst.BitSearch.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T15:03:30.442109+00:00
-- url     : https://prove2.me/submissions/3d89aadb-7477-400e-ac28-83eb2b1176da

import Mathlib
import Definitions.Def_QSVTPhaseEst_BitSearch_Procedure

namespace Aux_QSVT_T6

open QSVTPhaseEst.BitSearch

lemma step (n : ℕ) (b : ℕ → Bool) (j : ℕ) (hj : j < n) :
    thetaAfter n b j = thetaAfter n b (j + 1) / 2 + bitVal (b j) / 2 := by
  unfold thetaAfter
  have h1 : n - j = (n - (j + 1)) + 1 := by omega
  have h2 : n - 1 - (n - (j + 1)) = j := by omega
  rw [h1, thetaIter, h2]

lemma base (n : ℕ) (b : ℕ → Bool) : thetaAfter n b n = 0 := by
  unfold thetaAfter
  rw [Nat.sub_self, thetaIter]

end Aux_QSVT_T6

namespace Aux_QSVT_T6
open QSVTPhaseEst.BitSearch
theorem lemma11 (φ : ℝ) (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) (n : ℕ) (hn : 1 ≤ n)
    (hbits : ∃ k : ℕ, φ = (k : ℝ) / 2 ^ n) (b : ℕ → Bool) (hrun : IsLoopRun 0 φ n b) :
    ∀ j < n, thetaAfter n b j = Int.fract ((2 : ℝ) ^ j * φ) := by
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hss : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hinvpos : 0 < 1 / Real.sqrt 2 := by positivity
  have hinvlt : 1 / Real.sqrt 2 < 1 := by
    rw [div_lt_one hs2]; nlinarith [Real.sqrt_nonneg 2]
  have hπ := Real.pi_pos
  suffices H : ∀ i, i ≤ n → thetaAfter n b (n - i) = Int.fract ((2 : ℝ) ^ (n - i) * φ) by
    intro j hj
    have := H (n - j) (by omega)
    rwa [show n - (n - j) = j by omega] at this
  intro i
  induction i with
  | zero =>
    intro _
    rw [Nat.sub_zero, Aux_QSVT_T6.base]
    obtain ⟨k, hk⟩ := hbits
    have : (2 : ℝ) ^ n * φ = (k : ℝ) := by
      rw [hk]; field_simp
    rw [this, Int.fract_natCast]
  | succ i ih =>
    intro hi
    have ih' := ih (by omega)
    set j := n - (i + 1) with hjdef
    have hj1 : n - i = j + 1 := by omega
    rw [hj1] at ih'
    have hjn : j < n := by omega
    rw [Aux_QSVT_T6.step n b j hjn, ih']
    have hadm := hrun j hjn
    rw [ih'] at hadm
    unfold Admissible sigma at hadm
    simp only [zero_div, sub_zero, add_zero] at hadm
    set f := Int.fract ((2 : ℝ) ^ j * φ) with hf
    set m := ⌊(2 : ℝ) ^ j * φ⌋ with hm
    have hfm : (2 : ℝ) ^ j * φ = m + f := by rw [hf, hm]; exact (Int.floor_add_fract _).symm
    have hf0 : 0 ≤ f := Int.fract_nonneg _
    have hf1 : f < 1 := Int.fract_lt_one _
    have h2 : (2 : ℝ) ^ (j + 1) * φ = 2 * m + 2 * f := by rw [pow_succ]; linarith
    rcases lt_or_ge f (1 / 2) with hlt | hge
    · have hg : Int.fract ((2 : ℝ) ^ (j + 1) * φ) = 2 * f := by
        rw [Int.fract_eq_iff]
        refine ⟨by linarith, by linarith, 2 * m, ?_⟩
        rw [h2]; push_cast; ring
      rw [hg] at hadm ⊢
      have hc : |Real.cos (Real.pi * ((2 : ℝ) ^ j * φ - 2 * f / 2))| = 1 := by
        have : Real.pi * ((2 : ℝ) ^ j * φ - 2 * f / 2) = 0 + (m : ℝ) * Real.pi := by
          rw [hfm]; ring
        rw [this, Real.cos_add_int_mul_pi, Real.cos_zero, mul_one, abs_zpow, abs_neg,
          abs_one, one_zpow]
      rw [hc] at hadm
      have hb : b j = false := hadm.2 hinvlt
      rw [hb, bitVal]
      simp
    · have hg : Int.fract ((2 : ℝ) ^ (j + 1) * φ) = 2 * f - 1 := by
        rw [Int.fract_eq_iff]
        refine ⟨by linarith, by linarith, 2 * m + 1, ?_⟩
        rw [h2]; push_cast; ring
      rw [hg] at hadm ⊢
      have hc : |Real.cos (Real.pi * ((2 : ℝ) ^ j * φ - (2 * f - 1) / 2))| = 0 := by
        have : Real.pi * ((2 : ℝ) ^ j * φ - (2 * f - 1) / 2) =
            Real.pi / 2 + (m : ℝ) * Real.pi := by
          rw [hfm]; ring
        rw [this, Real.cos_add_int_mul_pi, Real.cos_pi_div_two, mul_zero, abs_zero]
      rw [hc] at hadm
      have hb : b j = true := hadm.1 hinvpos
      rw [hb, bitVal]
      simp
      ring

end Aux_QSVT_T6

open QSVTPhaseEst.BitSearch in
theorem solution (φ : ℝ) (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) (n : ℕ) (hn : 1 ≤ n)
    (hbits : ∃ k : ℕ, φ = (k : ℝ) / 2 ^ n) (b : ℕ → Bool) (hrun : IsLoopRun 0 φ n b) :
    thetaAfter n b 0 = φ := by
  rw [Aux_QSVT_T6.lemma11 φ hφ0 hφ1 n hn hbits b hrun 0 (by omega), pow_zero, one_mul]
  exact Int.fract_eq_self.mpr ⟨hφ0, hφ1⟩
