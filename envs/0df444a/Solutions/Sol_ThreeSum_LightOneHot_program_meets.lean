-- Prove2me | solution 1 for ThreeSum.LightOneHot.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:43:27.480734+00:00
-- url     : https://prove2.me/submissions/1be8dcd5-623a-45bb-b879-0ab7b6677b5a

import Definitions.Def_Submission_ThreeSum_OneHotMask
import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_LightOneHot
import Theorems.Thm_ThreeSum_LightOneHot_setup_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightOneHot
open Light ThreeSum.OneHotMask ThreeSum.LightSubsetAddress
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightOneHot
theorem _root_.solution {μ : ℕ → ℤ} {L m src0 src1 work U d : ℕ} (w0 w1 : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : work+(L+1) ≤ lim.space)
    (hsrc0 : src0+L ≤ work) (hsrc1 : src1+L ≤ work)
    (hword : (word L U : ℤ) ≤ lim.word)
    (hm : m < 2^L) (hd : d+L+1 ≤ lim.depth)
    (hread0 : ∀ i < L, μ (src0+i) = (w0 i : ℤ))
    (hread1 : ∀ i < L, μ (src1+i) = (w1 i : ℤ))
    (hbound0 : ∀ i < L, w0 i ≤ U) (hbound1 : ∀ i < L, w1 i ≤ U) :
    Meets lim program 0 d [L,m,src0,src1,work] μ (setupTime L)
      (fun r μ' => r = (OneHotMask.eval w0 w1 L m : ℤ) ∧
        Powers μ' work L ∧ SameOutside μ μ' work (L+1)) :=
  setup_meets rfl rfl rfl w0 w1 hw hspace hsrc0 hsrc1 hword hm hd
    hread0 hread1 hbound0 hbound1
end ThreeSum.LightOneHot
