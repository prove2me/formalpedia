-- Prove2me | solution 1 for ThreeSumApsp.IsPowLittleO.comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:07:06.579868+00:00
-- url     : https://prove2.me/submissions/d4538aff-b029-4d4a-9c38-b97987c67399

import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowLittleO
import Theorems.Thm_ThreeSumApsp_isPowLittleO_iff
import Theorems.Thm_ThreeSumApsp_IsPowLittleO_mono
import Theorems.Thm_ThreeSumApsp_Dominated_comp
import Theorems.Thm_ThreeSumApsp_IsBigOPow_comp
import Theorems.Thm_ThreeSumApsp_IsBigOPow_mono
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_comp
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_mono

section
open Filter Asymptotics
namespace ThreeSumApsp
variable {f g T : ℕ → ℝ} {size : ℕ → ℕ} {a b c d η : ℝ}
private theorem exists_pos_add_mul_add_le (hc : 0 ≤ c) (hd : 0 ≤ d) (hη : 0 < η) :
    ∃ t : ℝ, 0 < t ∧ (c + t) * (d + t) ≤ c * d + η := by
  have hcd : 0 < c + d + 1 := by linarith
  have ht : 0 < min 1 (η / (c + d + 1)) := lt_min one_pos (div_pos hη hcd)
  refine ⟨min 1 (η / (c + d + 1)), ht, ?_⟩
  set t := min 1 (η / (c + d + 1))
  have hsq : t * t ≤ t * 1 := mul_le_mul_of_nonneg_left (min_le_left _ _) ht.le
  have hlin : t * (c + d + 1) ≤ η := (le_div_iff₀ hcd).1 (min_le_right _ _)
  -- `(c + t)(d + t) = cd + t(c + d) + t² ≤ cd + t(c + d + 1) ≤ cd + η`
  linarith [hsq, hlin]
end ThreeSumApsp
set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g T : ℕ → ℝ} {size : ℕ → ℕ} {a b c d η : ℝ}
namespace ThreeSumApsp
namespace IsPowLittleO
theorem _root_.solution (hT : IsPowLittleO T c)
    (hs : IsPowLittleO (fun n => (size n : ℝ)) d) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    IsPowLittleO (fun n => T (size n)) (c * d) := by
  refine isPowLittleO_iff.2 fun η hη => ?_
  obtain ⟨t, ht, hexp⟩ := exists_pos_add_mul_add_le hc hd hη
  exact ((isPowLittleO_iff.1 hT t ht).comp (isPowLittleO_iff.1 hs t ht) (by linarith)
    (by linarith)).mono hexp
end IsPowLittleO
end ThreeSumApsp
