-- Prove2me | solution 1 for ThreeSum.LightMomentZeroDetector.moment_abs_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:51:32.908722+00:00
-- url     : https://prove2.me/submissions/6002c9e9-9d1e-40c5-96d9-5bbc5bb3ec93

import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_Submission_ThreeSum_LightMomentZeroDetector
import Theorems.Thm_List_abs_sum_le_sum_abs


set_option autoImplicit false
open ThreeSum ThreeSum.LightMomentZeroDetector
open Light ThreeSum.LightMomentDeterminant ThreeSum.LightFixedArithmetic
open FiniteMomentZeroDetector
open scoped BigOperators
namespace ThreeSum.LightMomentZeroDetector
theorem _root_.solution {t H k : ℕ} (v w : Fin t → ℤ) (V : ℤ)
    (hV : 1≤V) (hv : ∀ s, |v s|≤V) (hk : k≤2*H) :
    |moment v w k|≤(∑ s, |w s|)*V^(2*H) := by
  unfold moment
  calc
    |∑ s, w s*v s^k|≤∑ s, |w s*v s^k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s, |w s| *V^(2*H) := by
      apply Finset.sum_le_sum
      intro s hs
      rw [abs_mul,abs_pow]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact (pow_le_pow_left₀ (abs_nonneg _) (hv s) k).trans (pow_le_pow_right₀ hV hk)
    _ = _ := by rw [Finset.sum_mul]
end ThreeSum.LightMomentZeroDetector
