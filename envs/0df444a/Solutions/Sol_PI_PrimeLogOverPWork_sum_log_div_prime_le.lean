-- Prove2me | solution 1 for PI.PrimeLogOverPWork.sum_log_div_prime_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:31:35.274191+00:00
-- url     : https://prove2.me/submissions/4e988ba3-a7b5-4a91-91d0-11a1703603ff

import Definitions.Def_Formalism_PeriodIntegrals_PrimeSums
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_SLeOfBlock
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_PrimeLogOverPWork
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_PrimeLogOverPTop
import Theorems.Thm_PI_PrimeLogOverPWork_S_le_large
import Theorems.Thm_PI_PrimeLogOverPWork_S_le_small


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.PrimeLogOverPWork
open Finset
namespace PI.PrimeLogOverPWork
theorem _root_.solution : PI.PrimeLogOverP := by
  intro Y hY Q hQ
  have hN1 : 1 ≤ ⌊Y⌋₊ := Nat.le_floor (by simpa using hY.le)
  have hNY : ((⌊Y⌋₊ : ℕ) : ℝ) ≤ Y := Nat.floor_le (by linarith)
  have h1 : ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ≤ S ⌊Y⌋₊ := by
    unfold S
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hpp, hpY⟩ := hQ p hp
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨hpp.pos, Nat.le_floor hpY⟩, hpp⟩
    · intro p _ _
      exact div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
  have h2 : S ⌊Y⌋₊ ≤ Real.log ((⌊Y⌋₊ : ℕ) : ℝ) := by
    rcases Nat.lt_or_ge 63 ⌊Y⌋₊ with h | h
    · exact S_le_large _ (by omega)
    · exact S_le_small _ hN1 h
  have h3 : Real.log ((⌊Y⌋₊ : ℕ) : ℝ) ≤ Real.log Y := Real.log_le_log (Nat.cast_pos.mpr hN1) hNY
  linarith
end PI.PrimeLogOverPWork
