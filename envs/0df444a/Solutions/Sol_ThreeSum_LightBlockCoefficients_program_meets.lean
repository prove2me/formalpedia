-- Prove2me | solution 1 for ThreeSum.LightBlockCoefficients.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:38:22.207423+00:00
-- url     : https://prove2.me/submissions/8d107f72-0110-4dd3-bf42-5b17e53dd357

import Definitions.Def_Submission_ThreeSum_LightScaleArray
import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_BlockIndex
import Definitions.Def_Submission_ThreeSum_LightBlockCoefficients
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Theorems.Thm_ThreeSum_LightScaleArray_meets


set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockCoefficients
open Light
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightBlockCoefficients
theorem _root_.solution {μ : ℕ → ℤ} {J L p occ maps dst0 dst1 work U M d : ℕ}
    (sel : ℕ → ℕ) (w0 w1 : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hp : 1 ≤ p)
    (hocc : occ+J ≤ dst0) (hmaps : maps+2*L*M ≤ dst0)
    (hdst0 : dst0+J*L ≤ dst1) (hdst1 : dst1+J*L ≤ work)
    (hspace : work+(J+1) ≤ lim.space)
    (hword : (word J p U : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hsel : ∀ j < J, sel j < M)
    (hselRead : ∀ j < J, μ (occ+j) = (sel j : ℤ))
    (hread0 : ∀ s < M, ∀ i < L, μ (maps+2*L*s+i) = (w0 s i : ℤ))
    (hread1 : ∀ s < M, ∀ i < L, μ (maps+2*L*s+L+i) = (w1 s i : ℤ))
    (hbound0 : ∀ s < M, ∀ i < L, w0 s i ≤ U)
    (hbound1 : ∀ s < M, ∀ i < L, w1 s i ≤ U) :
    Meets lim program 0 d [J,L,p,occ,maps,dst0,dst1,work] μ (time J L)
      (fun _ ν => Rows ν dst0 dst1 L p sel w0 w1 J ∧
        Kept μ ν dst0 ∧ Powers ν work J p) :=
  meets rfl rfl rfl sel w0 w1 hw hp hocc hmaps hdst0 hdst1 hspace hword hd
    hsel hselRead hread0 hread1 hbound0 hbound1
end ThreeSum.LightBlockCoefficients
