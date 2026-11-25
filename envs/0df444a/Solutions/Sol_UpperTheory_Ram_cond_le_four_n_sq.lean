-- Prove2me | solution 1 for UpperTheory.Ram.cond_le_four_n_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:57:29.434827+00:00
-- url     : https://prove2.me/submissions/0b04014a-171a-4bbb-8e49-13c4d506f6cb

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_OrdLeTotientQS
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_CondLam
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_UpperTheory_Ram_ord_le_totient_QS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open Formalism.BasicNotions
namespace UpperTheory.Ram
theorem _root_.solution :
    ∀ (R : Ranks) (H : Host R), (H.QS : ℝ) * H.q * H.d ≤ 4 * ((R.f : ℝ) / 2) ^ 2 * H.q * H.d ∧ 4 * ((R.f : ℝ) / 2) ^ 2 * H.q * H.d ≤ ((H.QS : ℝ) * H.q * H.d) ^ 2 ∧ (R.f : ℝ) ≤ H.QS := by
  intro R H
  have hQS : H.QS ≤ R.n ^ 2 := H.QS_le
  have h2 : 2 * R.ord ≤ H.QS := (UpperTheory.Ram.ord_le_totient_QS H.toHostAx).2
  have hf : (R.f : ℝ) = 2 * (R.n : ℝ) := by
    simp only [Ranks.f]
    push_cast
    ring
  have hn : (R.n : ℝ) = (R.ord : ℝ) := by simp [Ranks.n]
  have hq1 : (1 : ℝ) ≤ H.q := by
    have := H.qd_big.1
    exact_mod_cast (by omega : 1 ≤ H.q)
  have hd1 : (1 : ℝ) ≤ H.d := by
    have := H.qd_big.2
    exact_mod_cast (by omega : 1 ≤ H.d)
  have hQSr : (H.QS : ℝ) ≤ (R.n : ℝ) ^ 2 := by exact_mod_cast hQS
  have h2r : 2 * (R.n : ℝ) ≤ H.QS := by
    rw [hn]; exact_mod_cast h2
  have hn0 : (0 : ℝ) ≤ R.n := Nat.cast_nonneg _
  have hqd : (0 : ℝ) ≤ (H.q : ℝ) * H.d := by positivity
  have hqd1 : (1 : ℝ) ≤ (H.q : ℝ) * H.d := by nlinarith
  rw [hf]
  refine ⟨?_, ?_, h2r⟩
  · have : (H.QS : ℝ) ≤ 4 * (2 * (R.n : ℝ) / 2) ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_right this hqd
    nlinarith
  · have hsq : 4 * (2 * (R.n : ℝ) / 2) ^ 2 ≤ (H.QS : ℝ) ^ 2 := by nlinarith
    have hqq : (H.q : ℝ) * H.d ≤ ((H.q : ℝ) * H.d) ^ 2 := by nlinarith
    have hA : (0 : ℝ) ≤ 4 * (2 * (R.n : ℝ) / 2) ^ 2 := by positivity
    calc 4 * (2 * (R.n : ℝ) / 2) ^ 2 * H.q * H.d = 4 * (2 * (R.n : ℝ) / 2) ^ 2 * ((H.q : ℝ) * H.d) := by ring
      _ ≤ (H.QS : ℝ) ^ 2 * ((H.q : ℝ) * H.d) ^ 2 := mul_le_mul hsq hqq hqd (by positivity)
      _ = ((H.QS : ℝ) * H.q * H.d) ^ 2 := by ring
end UpperTheory.Ram
