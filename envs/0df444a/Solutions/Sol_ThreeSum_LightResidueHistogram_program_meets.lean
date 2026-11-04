-- Prove2me | solution 1 for ThreeSum.LightResidueHistogram.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:48:05.565842+00:00
-- url     : https://prove2.me/submissions/4c13bc8d-66ba-47d0-9577-9129f5b5e8b7

import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_LightHistogram
import Definitions.Def_Submission_ThreeSum_CyclicFold
import Definitions.Def_Submission_ThreeSum_LightResidueHistogram
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e

set_option autoImplicit false
open ThreeSum ThreeSum.LightResidueHistogram
open Light Finset ThreeSum.LightResidues ThreeSum.LightHistogram
open ThreeSum.CyclicFold ThreeSum.Karatsuba
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightResidueHistogram
theorem _root_.solution
    {μ : ℕ → ℤ} {src dst n p cap codes work U : ℕ} {c : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d + 1 < lim.depth)
    (hp : 0 < p) (hcap : p ≤ cap)
    (hsrc : src + n ≤ codes) (hdst : dst + cap ≤ codes)
    (hcodes : codes + n ≤ work)
    (hspace : work + (Nat.log 2 (U + 1) + 2) ≤ lim.space)
    (hc : |c| ≤ 1) (hword : (4 * U + 4 * p + 16 : ℤ) ≤ lim.word)
    (hvalues : ∀ i < n, |μ (src + i)| ≤ (U : ℤ)) :
    Meets lim program 0 d [src, dst, n, p, cap, codes, work, c] μ (time n cap U)
      (fun _ μ' =>
        Seg μ' dst (padTo cap (vector p (signedHistogram p c (fun i => μ (src+i)) n))) ∧
          KeptBut μ μ' codes dst cap) := by
  exact meets rfl rfl rfl rfl rfl hw hd hp hcap hsrc hdst hcodes hspace hc hword hvalues
end ThreeSum.LightResidueHistogram
