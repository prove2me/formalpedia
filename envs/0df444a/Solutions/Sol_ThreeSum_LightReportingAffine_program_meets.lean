-- Prove2me | solution 1 for ThreeSum.LightReportingAffine.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:34:07.218351+00:00
-- url     : https://prove2.me/submissions/51705749-e5a3-4d2a-b5a1-2d8a9818fcb1

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightReportingAffine
import Theorems.Thm_ThreeSum_LightReportingAffine_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingAffine
open Light ThreeSum.LightArray
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightReportingAffine
theorem _root_.solution {src dst n : ℕ} {b c : ℤ} {μ : ℕ → ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+n ≤ lim.space) (hdst : dst+n ≤ lim.space)
    (hsep : SourceSafe src dst n)
    (hmul : ∀ i < n, |c*μ (src+i)| ≤ lim.word)
    (hsum : ∀ i < n, |b+c*μ (src+i)| ≤ lim.word) :
    Meets lim program 0 d [src,dst,n,b,c] μ (time n)
      (fun _ μ' => (∀ i < n, μ' (dst+i) = b+c*μ (src+i)) ∧ SameOutside μ μ' dst n) :=
  meets rfl hw hsrc hdst hsep hmul hsum
end ThreeSum.LightReportingAffine
