-- Prove2me | solution 1 for ThreeSum.LightSourceGather.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:58:23.179146+00:00
-- url     : https://prove2.me/submissions/bb7843d2-e4d7-4310-a8e1-8c71facd9a96

import Definitions.Def_Submission_ThreeSum_BlockSourceEncoding
import Definitions.Def_Submission_ThreeSum_LightSourceGather
import Definitions.Def_WeightedCache3SUM_Alias_27f79aa230fbddf9
import Definitions.Def_WeightedCache3SUM_Alias_5b14bc7229a63f1e
import Theorems.Thm_ThreeSum_LightSourceResidues_meets


set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceGather
open Light
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceGather
theorem _root_.solution
    {μ : ℕ → ℤ} {raw flags table dst n m work U B : ℕ}
    (endpoint : ℕ → ℤ) (flag hist : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth) (hm : 0 < m)
    (hraw : raw+n ≤ dst) (hflags : flags+n ≤ dst) (htable : table+m ≤ dst)
    (hdst : dst+n ≤ work) (hspace : work+(Nat.log 2 (U+1)+2) ≤ lim.space)
    (hword : (4*U+4*m+16 : ℤ) ≤ lim.word) (hcountWord : (B : ℤ) ≤ lim.word)
    (hrawRead : ∀ i < n, μ (raw+i) = endpoint i)
    (hrawBound : ∀ i < n, |endpoint i| ≤ (U : ℤ))
    (hflagRead : ∀ i < n, μ (flags+i) = (flag i : ℤ))
    (hflagBound : ∀ i < n, flag i ≤ 1)
    (hhistRead : ∀ r < m, μ (table+r) = (hist r : ℤ))
    (hhistBound : ∀ r < m, hist r ≤ B) :
    Meets lim program 0 d [raw,flags,table,dst,n,m,work] μ (time n U)
      (fun _ ν => (∀ i < n, ν (dst+i) = (value m endpoint flag hist i : ℤ)) ∧
        KeptBut μ ν work dst n) := by
  exact meets rfl rfl endpoint flag hist hw hd hm hraw hflags htable hdst hspace
    hword hcountWord hrawRead hrawBound hflagRead hflagBound hhistRead hhistBound
end ThreeSum.LightSourceGather
