-- Prove2me | solution 1 for ThreeSum.LightRadixRows.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:27:52.635054+00:00
-- url     : https://prove2.me/submissions/bef1f9a4-d738-4acc-ac5d-1e30c27215fe

import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Definitions.Def_Submission_ThreeSum_LightReportingAffine
import Definitions.Def_Submission_ThreeSum_LightRadixRows
import Definitions.Def_WeightedCache3SUM_Alias_32e47c9a32bb047b
import Theorems.Thm_ThreeSum_LightReportingAffine_meets


set_option autoImplicit false
open ThreeSum ThreeSum.LightRadixRows
open Light RadixKeyLists
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightRadixRows
theorem _root_.solution {srcBase srcPrev dst p U V : ℕ} {μ : ℕ → ℤ}
    (base prev : List ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hbaseEnd : srcBase+base.length ≤ dst) (hprevEnd : srcPrev+prev.length ≤ dst)
    (hspace : dst+base.length*prev.length ≤ lim.space)
    (hword : (word p U V : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hbaseRead : Seg μ srcBase base) (hprevRead : Seg μ srcPrev prev)
    (hbaseBound : ∀ x ∈ base, |x| ≤ (U : ℤ))
    (hprevBound : ∀ y ∈ prev, |y| ≤ (V : ℤ)) :
    Meets lim program 0 d [srcBase,srcPrev,dst,base.length,prev.length,p] μ
      (time base.length prev.length)
      (fun _ ν => Seg ν dst (step (p : ℤ) base prev) ∧
        SameOutside μ ν dst (base.length*prev.length)) :=
  meets rfl rfl base prev hw hbaseEnd hprevEnd hspace hword hd hbaseRead hprevRead
    hbaseBound hprevBound
end ThreeSum.LightRadixRows
