-- Prove2me | solution 1 for ThreeSum.LightTernaryCarryCodes.table_covers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:46:51.569001+00:00
-- url     : https://prove2.me/submissions/5996826b-6417-443d-a8d1-8c5c0193c892

import Definitions.Def_Submission_ThreeSum_LightOutputDecodeDigits
import Definitions.Def_Submission_ThreeSum_TernaryCarryCode
import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_ThreeSum_LightTernaryCarryCodes
import Theorems.Thm_ThreeSum_LightTernaryCarryCodes_accepted_iff
import Theorems.Thm_ThreeSum_LightTernaryCarryCodes_row_carry_read
import Theorems.Thm_ThreeSum_TernaryCarryCode_carryFromCode_code
import Theorems.Thm_ThreeSum_TernaryCarryCode_codeOfCarry_initial
import Theorems.Thm_ThreeSum_TernaryCarryCode_codeOfCarry_lt


set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryCarryCodes
open Light TernarySignedDigits
set_option maxHeartbeats 2400000
set_option maxRecDepth 9000
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
namespace ThreeSum.LightTernaryCarryCodes
theorem _root_.solution {ν : ℕ → ℤ} {dst J : ℕ}
    (h : Table ν dst J (2^J)) {c : CarryWord J}
    (hc : ValidCarry c) :
    ∃ q<2^J, accepted J q=1 ∧ ∀ i : Fin (J+1),
      ν (dst+q*(J+1)+J-i.val)=((c i).val : ℤ) := by
  refine ⟨TernaryCarryCode.codeOfCarry c,TernaryCarryCode.codeOfCarry_lt c,?_,?_⟩
  · exact (accepted_iff (TernaryCarryCode.codeOfCarry_lt c)).mpr
      (TernaryCarryCode.codeOfCarry_initial hc)
  · intro i
    have hr := row_carry_read (h _ (TernaryCarryCode.codeOfCarry_lt c)) i
    rw [TernaryCarryCode.carryFromCode_code hc] at hr
    exact hr
end ThreeSum.LightTernaryCarryCodes
