-- Prove2me | solution 1 for ThreeSum.LightReportingFilter.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:57:08.426281+00:00
-- url     : https://prove2.me/submissions/3fead35d-4958-4057-9f7f-f041612dde5a

import Definitions.Def_Submission_ThreeSum_LightReportingAffine
import Definitions.Def_Submission_ThreeSum_LightReportingFilter
import Definitions.Def_WeightedCache3SUM_Alias_62113581f113eb47
import Theorems.Thm_ThreeSum_LightReportingAffine_meets


set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingFilter
open Light
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightReportingFilter
theorem _root_.solution {n src dst d : ℕ} {μ : ℕ → ℤ} (count : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+n ≤ lim.space) (hdst : dst+n ≤ lim.space)
    (hsep : Apart src n dst n)
    (hword : ∀ i < n, (count i : ℤ) ≤ lim.word)
    (hread : ∀ i < n, μ (src+i) = (count i : ℤ)) :
    Meets lim program 0 d [n,src,dst] μ (time n)
      (fun r μ' => r = ((selected count n).length : ℤ) ∧
        SegN μ' dst (selected count n) ∧ SameOutside μ μ' dst n) :=
  meets count rfl hw hsrc hdst hsep hword hread
end ThreeSum.LightReportingFilter
