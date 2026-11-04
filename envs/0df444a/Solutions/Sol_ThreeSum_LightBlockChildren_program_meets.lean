-- Prove2me | solution 1 for ThreeSum.LightBlockChildren.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:35:02.700486+00:00
-- url     : https://prove2.me/submissions/bc5cfd64-e067-4654-88e8-a102be34b7a9

import Definitions.Def_Submission_ThreeSum_ReportingHostMasks
import Definitions.Def_Submission_ThreeSum_LightQueryEnumeration
import Definitions.Def_Submission_ThreeSum_LightReportingAffine
import Definitions.Def_Submission_ThreeSum_LightBlockChildren
import Definitions.Def_WeightedCache3SUM_Alias_ced581dbf41e1ce0
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_daea56ef26e5693b
import Definitions.Def_WeightedCache3SUM_Alias_874c626a95c648fa
import Theorems.Thm_ThreeSum_LightReportingAffine_meets
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Definitions.Def_WeightedCache3SUM_Alias_faf0bf412734022a


set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockChildren
open Light Finset ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
open QueryCoordinates ReportingHostMasks
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightBlockChildren
theorem _root_.solution {μ : ℕ → ℤ} {W h masks dstL dstR work d : ℕ}
    (A B Q R : Finset (Fin W))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hAQ : Disjoint A Q) (hBQ : Disjoint B Q) (hQR : Q ⊆ R)
    (hh : h ≤ Q.card+1)
    (hmasks : masks+Q.card.choose h ≤ dstL)
    (hleft : dstL+Q.card.choose h ≤ dstR)
    (hright : dstR+Q.card.choose h ≤ work)
    (hspace : work+(2*W+2) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hd : d+W+3 ≤ lim.depth) :
    Meets lim program 0 d
      [W,h,subsetMask Q,subsetMask A,subsetMask B,subsetMask R,masks,dstL,dstR,work]
      μ (time W Q.card h)
      (fun r μ' =>
        r = (subsetMask (R \ Q) : ℤ) ∧
        SegN μ' masks ((missingSets Q h).map subsetMask) ∧
        SegN μ' dstL (leftMasks A Q h) ∧
        SegN μ' dstR (rightMasks B Q h) ∧ Kept μ μ' masks) :=
  meets rfl procs A B Q R hw hAQ hBQ hQR hh hmasks hleft hright hspace hword hd
end ThreeSum.LightBlockChildren
