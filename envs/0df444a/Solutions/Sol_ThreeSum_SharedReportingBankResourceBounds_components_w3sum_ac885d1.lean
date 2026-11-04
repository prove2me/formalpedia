-- Prove2me | solution 1 for ThreeSum.SharedReportingBankResourceBounds.components_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:36:26.146195+00:00
-- url     : https://prove2.me/submissions/12dbf334-2369-480e-b829-0ab2fd4df26b

import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBounds
import Definitions.Def_Submission_ThreeSum_LightLocalCoverMagnitude
import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBoundsScales
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_primitive_bounds
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_linear_le_magnitude
import Definitions.Def_WeightedCache3SUM_Alias_ec6f8129c3d22917
import Theorems.Thm_ThreeSum_LightLocalCoverMagnitude_succ_pow_bound
import Theorems.Thm_ThreeSum_LocalParameterBounds_prime_bound
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_levels_le


set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankResourceBounds
open Scales Light SubsetAddress SharedReportingBankLayout SharedReportingBankHeader
set_option maxHeartbeats 3000000
set_option maxRecDepth 14000
namespace ThreeSum.SharedReportingBankResourceBounds
theorem _root_.solution (n : ℕ) : Components n := by
  obtain ⟨hh,hJ,ht,hW⟩ := primitive_bounds n
  have hlin := linear_le_magnitude n
  have hk := levels_le (blocks n)
  have hprod : half n*blocks n ≤ inputBits n := by nlinarith
  have raise (e : ℕ) (he : e ≤ 2048*(inputBits n+1)) : 2^e ≤ magnitude n :=
    Nat.pow_le_pow_right (by decide) he
  refine ⟨by exact Nat.two_pow_pos _,by omega,by omega,by omega,by omega,?_,?_,?_,?_,?_,?_,?_,?_,?_,by omega,?_⟩
  · unfold prefixCount
    apply raise
    have he : 2*((blocks n+1)*(512*half n))=
        2*width (half n) (blocks n)+2*(512*half n) := by unfold width localWidth; ring
    rw [he]
    omega
  · exact raise _ (by omega)
  · exact raise _ (by omega)
  · exact raise _ (by omega)
  · exact raise _ (by omega)
  · have hs := LightLocalCoverMagnitude.rounds_bound (half n)
    calc
      _ ≤ (2^(1029*half n+16))^(blocks n) := Nat.pow_le_pow_left hs _
      _ = 2^((1029*half n+16)*blocks n) := by rw [pow_mul]
      _ ≤ _ := raise _ (by nlinarith)
  · exact (LocalParameterBounds.prime_bound (half n)).trans (raise _ (by omega))
  · rw [← pow_succ]
    calc
      _ ≤ (2^(514*half n+2))^(blocks n+1) := Nat.pow_le_pow_left (LocalParameterBounds.prime_bound (half n)) _
      _ = 2^((514*half n+2)*(blocks n+1)) := by rw [pow_mul]
      _ ≤ _ := raise _ (by nlinarith)
  · calc
      _ ≤ (2^(512*half n+1))^(blocks n) :=
        Nat.pow_le_pow_left (LightLocalCoverMagnitude.succ_pow_bound le_rfl) _
      _ = 2^((512*half n+1)*blocks n) := by rw [pow_mul]
      _ ≤ _ := raise _ (by
        have he : (512*half n+1)*blocks n=width (half n) (blocks n)+blocks n := by unfold width localWidth; ring
        rw [he]
        omega)
  · unfold LightSwitchDepth.word
    omega
end ThreeSum.SharedReportingBankResourceBounds
