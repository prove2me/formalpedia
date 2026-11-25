-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_term_le_ddedda1072cb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:24:43.879372+00:00
-- url     : https://prove2.me/submissions/bf462704-7863-4daf-9ddd-a72050848f0b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropFiltSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropTermSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropHilbWSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionCountDrop
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_pow_add_le_abec59476fd6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_pow_add_le_mul_ff1e09ec03ee

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open Filter
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.SectionCount GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop
theorem _root_.solution (I C c n h : ℝ) (e d : ℕ) (hed : e ≤ d) (hc : 0 ≤ c) (hn : 1 ≤ n)
    (hh : |h - I * (n + c) ^ e / (e.factorial : ℝ)| ≤ C * (n + c) ^ e / (n + c)) :
    h ≤ (if e = d then I else 0) * n ^ d / (d.factorial : ℝ) +
      (|I| + |C|) * (1 + c) ^ e * (n ^ d / n) := by
  have hn0 : 0 < n := by linarith
  have hnc : n ≤ n + c := by linarith
  have hP : (n + c) ^ e ≤ (1 + c) ^ e * n ^ e := pow_add_le_mul c n hc hn e
  have hPe : 0 ≤ (n + c) ^ e := by positivity
  have hne : n ^ e ≤ n ^ d := pow_le_pow_right₀ hn hed
  have h1 := (abs_le.mp hh).2

  have hC : C * (n + c) ^ e / (n + c) ≤ |C| * (1 + c) ^ e * (n ^ d / n) := by
    calc C * (n + c) ^ e / (n + c) ≤ |C| * (n + c) ^ e / (n + c) := by
          gcongr; exact le_abs_self C
      _ ≤ |C| * (n + c) ^ e / n := by
          apply div_le_div_of_nonneg_left (by positivity) hn0 hnc
      _ ≤ |C| * ((1 + c) ^ e * n ^ e) / n := by gcongr
      _ ≤ |C| * ((1 + c) ^ e * n ^ d) / n := by gcongr
      _ = |C| * (1 + c) ^ e * (n ^ d / n) := by ring
  have hfac : (1 : ℝ) ≤ (e.factorial : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero e)

  have hM : I * (n + c) ^ e / (e.factorial : ℝ) ≤
      (if e = d then I else 0) * n ^ d / (d.factorial : ℝ) + |I| * (1 + c) ^ e * (n ^ d / n) := by
    split_ifs with hde
    · subst hde
      have hA := pow_add_le c n hc hn e
      have hlow : n ^ e ≤ (n + c) ^ e := pow_le_pow_left₀ hn0.le hnc e
      have hD : 0 ≤ (n + c) ^ e - n ^ e := by linarith
      have hq : 0 ≤ n ^ e / n := by positivity
      have hdiff : I * ((n + c) ^ e - n ^ e) ≤ |I| * (1 + c) ^ e * (n ^ e / n) := by
        calc I * ((n + c) ^ e - n ^ e) ≤ |I| * ((n + c) ^ e - n ^ e) :=
              mul_le_mul_of_nonneg_right (le_abs_self I) hD
          _ ≤ |I| * (((1 + c) ^ e - 1) * (n ^ e / n)) :=
              mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg I)
          _ ≤ |I| * (1 + c) ^ e * (n ^ e / n) := by
              rw [mul_assoc]
              exact mul_le_mul_of_nonneg_left (by nlinarith) (abs_nonneg I)
      have hpos : (0 : ℝ) < (e.factorial : ℝ) := by linarith
      have hR : 0 ≤ |I| * (1 + c) ^ e * (n ^ e / n) := by positivity
      rw [div_le_iff₀ hpos]
      have : I * (n + c) ^ e = I * n ^ e + I * ((n + c) ^ e - n ^ e) := by ring
      rw [this, add_mul, div_mul_cancel₀ _ hpos.ne']
      nlinarith
    · have hlt : e < d := lt_of_le_of_ne hed hde
      have hd1 : n ^ e ≤ n ^ d / n := by
        rw [le_div_iff₀ hn0, ← pow_succ]
        exact pow_le_pow_right₀ hn hlt
      have hpos : (0 : ℝ) < (e.factorial : ℝ) := by linarith
      calc I * (n + c) ^ e / (e.factorial : ℝ) ≤ |I| * (n + c) ^ e / (e.factorial : ℝ) := by
            gcongr; exact le_abs_self I
        _ ≤ |I| * (n + c) ^ e := div_le_self (by positivity) hfac
        _ ≤ |I| * ((1 + c) ^ e * n ^ e) := by gcongr
        _ ≤ |I| * ((1 + c) ^ e * (n ^ d / n)) := by gcongr
        _ = 0 * n ^ d / (d.factorial : ℝ) + |I| * (1 + c) ^ e * (n ^ d / n) := by ring
  have : (|I| + |C|) * (1 + c) ^ e * (n ^ d / n) =
      |I| * (1 + c) ^ e * (n ^ d / n) + |C| * (1 + c) ^ e * (n ^ d / n) := by ring
  rw [this]
  linarith
end GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop
