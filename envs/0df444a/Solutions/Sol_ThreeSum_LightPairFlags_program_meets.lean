-- Prove2me | solution 1 for ThreeSum.LightPairFlags.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:07:28.106753+00:00
-- url     : https://prove2.me/submissions/2f1384ee-0a86-411e-8faa-02baf2fadf5e

import Definitions.Def_Submission_ThreeSum_LightBooleanDot
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSum_LightTrimTest
import Definitions.Def_Submission_ThreeSum_LightPairFlags
import Definitions.Def_WeightedCache3SUM_Alias_9176929b72776235
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Definitions.Def_WeightedCache3SUM_Alias_cdc5e7727f35fd80


set_option autoImplicit false
open ThreeSum ThreeSum.LightPairFlags
open Light
set_option maxHeartbeats 1500000
set_option maxRecDepth 5000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightPairFlags
theorem _root_.solution
    {μ : ℕ → ℤ} {bitPtr leftPtr rightPtr leftHist rightHist dst n L p cap : ℕ}
    (bits : ℕ → ℕ → ℕ) (left right leftCount rightCount : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth) (hn : 0 < n) (hp : 0 < p)
    (hbits : bitPtr+n*L ≤ dst) (hleft : leftPtr+n ≤ dst) (hright : rightPtr+n ≤ dst)
    (hleftHist : leftHist+p ≤ dst) (hrightHist : rightHist+p ≤ dst)
    (hspace : dst+2*(n*n) ≤ lim.space) (hword : (word L n p cap : ℤ) ≤ lim.word)
    (hbitsRead : ∀ i < n, ∀ j < L, μ (bitPtr+i*L+j) = (bits i j : ℤ))
    (hbitsValue : ∀ i < n, ∀ j < L, bits i j ≤ 1)
    (hleftRead : ∀ i < n, μ (leftPtr+i) = (left i : ℤ))
    (hrightRead : ∀ i < n, μ (rightPtr+i) = (right i : ℤ))
    (hleftLt : ∀ i < n, left i < p) (hrightLt : ∀ i < n, right i < p)
    (hleftCount : ∀ r < p, μ (leftHist+r) = (leftCount r : ℤ))
    (hrightCount : ∀ r < p, μ (rightHist+r) = (rightCount r : ℤ))
    (hleftBound : ∀ r < p, leftCount r ≤ n) (hrightBound : ∀ r < p, rightCount r ≤ n) :
    Meets lim program 0 d [bitPtr,leftPtr,rightPtr,leftHist,rightHist,dst,n,L,p,cap] μ (time L n)
      (fun _ μ' =>
        (∀ i < n*n, μ' (dst+i) = (pairKey n p left right i : ℤ)) ∧
        (∀ i < n*n, μ' (dst+n*n+i) = (pairFlag L n cap bits left right leftCount rightCount i : ℤ)) ∧
        SameOutside μ μ' dst (2*(n*n))) :=
  meets rfl rfl rfl rfl bits left right leftCount rightCount hw hd hn hp
    hbits hleft hright hleftHist hrightHist hspace hword hbitsRead hbitsValue
    hleftRead hrightRead hleftLt hrightLt hleftCount hrightCount hleftBound hrightBound
end ThreeSum.LightPairFlags
