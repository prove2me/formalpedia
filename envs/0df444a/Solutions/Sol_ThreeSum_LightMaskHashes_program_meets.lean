-- Prove2me | solution 1 for ThreeSum.LightMaskHashes.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:51:47.663406+00:00
-- url     : https://prove2.me/submissions/8f925bd4-5818-4fcc-a84a-b24d275627c2

import Definitions.Def_Submission_ThreeSum_LightOneHot
import Definitions.Def_Submission_ThreeSum_LightMaskHashes
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55


set_option autoImplicit false
open ThreeSum ThreeSum.LightMaskHashes
open Light LightSubsetAddress
set_option maxHeartbeats 1000000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightMaskHashes
theorem _root_.solution
    {μ : ℕ → ℤ} {L masks dst n src0 src1 work U : ℕ}
    (mask w0 w1 : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+L+1 ≤ lim.depth)
    (hspace : work+(L+1) ≤ lim.space)
    (hmasks : masks+n ≤ dst) (hsrc0 : src0+L ≤ dst) (hsrc1 : src1+L ≤ dst)
    (hdst : dst+n ≤ work)
    (hword : (LightOneHot.word L U : ℤ) ≤ lim.word)
    (hmaskRead : ∀ i < n, μ (masks+i) = (mask i : ℤ))
    (hmaskLt : ∀ i < n, mask i < 2^L)
    (hread0 : ∀ i < L, μ (src0+i) = (w0 i : ℤ))
    (hread1 : ∀ i < L, μ (src1+i) = (w1 i : ℤ))
    (hbound0 : ∀ i < L, w0 i ≤ U) (hbound1 : ∀ i < L, w1 i ≤ U) :
    Meets lim program 0 d [L,masks,dst,n,src0,src1,work] μ (time L n)
      (fun _ μ' => (∀ i < n, μ' (dst+i) = (OneHotMask.eval w0 w1 L (mask i) : ℤ)) ∧
        Powers μ' work L ∧ KeptBut μ μ' work dst n) :=
  meets rfl rfl rfl mask w0 w1 hw hd hspace hmasks hsrc0 hsrc1 hdst hword
    hmaskRead hmaskLt hread0 hread1 hbound0 hbound1
end ThreeSum.LightMaskHashes
