-- Prove2me | solution 1 for ThreeSum.LightWeightRow.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:44:45.814165+00:00
-- url     : https://prove2.me/submissions/a4adaa69-d998-4c6e-a155-5bd04471ee0b

import Definitions.Def_Submission_ThreeSum_LightRadixDigit
import Definitions.Def_Submission_ThreeSum_WeightEnumeration
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_PowTable
import Definitions.Def_Submission_ThreeSum_LightWeightRow
import Definitions.Def_WeightedCache3SUM_Alias_b5410f4bcc10d599
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab


set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightRow
open Light
set_option maxHeartbeats 1200000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightWeightRow
theorem _root_.solution
    {μ : ℕ → ℤ} {W p k powers start stride dst n : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth) (hp : 1 ≤ p)
    (hspace : dst+n ≤ lim.space) (hpowers : powers+(W+1) ≤ lim.space)
    (hsep : Apart powers (W+1) dst n)
    (hword : (word W p k start stride : ℤ) ≤ lim.word)
    (hcoords : ∀ i < n, start+stride*i < W)
    (hread : ∀ e ≤ W, μ (powers+e) = ((p^e : ℕ) : ℤ)) :
    Meets lim program 0 d [W,p,k,powers,start,stride,dst,n] μ (time n k)
      (fun _ μ' =>
        (∀ i < n, μ' (dst+i) = (WeightEnumeration.digit p W k (start+stride*i) : ℤ)) ∧
        SameOutside μ μ' dst n) :=
  meets rfl rfl rfl hw hd hp hspace hpowers hsep hword hcoords hread
end ThreeSum.LightWeightRow
