-- Prove2me | solution 1 for ThreeSum.LightScaleArray.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:34:09.375206+00:00
-- url     : https://prove2.me/submissions/a8797736-0d95-4185-ad20-04d38cab2566

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightScaleArray
import Theorems.Thm_ThreeSum_LightScaleArray_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightScaleArray
open Light ThreeSum.LightArray
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightScaleArray
theorem _root_.solution {src dst n : ℕ} {c : ℤ} {μ : ℕ → ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+n ≤ lim.space) (hdst : dst+n ≤ lim.space)
    (hsep : SourceSafe src dst n)
    (hword : ∀ i < n, |c*μ (src+i)| ≤ lim.word) :
    Meets lim program 0 d [src,dst,n,c] μ (time n)
      (fun _ μ' => (∀ i < n, μ' (dst+i) = c*μ (src+i)) ∧ SameOutside μ μ' dst n) :=
  meets rfl hw hsrc hdst hsep hword
end ThreeSum.LightScaleArray
