-- Prove2me | solution 1 for ThreeSum.LightEncodedColorPrimeHost.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T20:51:09.732929+00:00
-- url     : https://prove2.me/submissions/c12fbc7a-ea7c-426d-894c-907eb4491899

import Definitions.Def_Submission_ThreeSum_LightEncodedColorNormalize
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeReadyData
import Definitions.Def_Submission_ThreeSum_LightEncodedColorPrimeHost
import Definitions.Def_WeightedCache3SUM_Alias_748452ca177f4ae1
import Theorems.Thm_Light_Meets_mono_time
import Theorems.Thm_ThreeSum_EncodedColorPrimeCosts_time_le_budget
import Theorems.Thm_ThreeSum_LightOutputDecodeDivide_time_le_budget


set_option autoImplicit false
open ThreeSum ThreeSum.LightEncodedColorPrimeHost
open Light Scales BandScales ArithmeticStageBounds ColorClassLists EncodedColorLayout
set_option maxHeartbeats 3200000
set_option maxRecDepth 15000
variable {lim : Limits} {d : ℕ}
namespace ThreeSum.LightEncodedColorPrimeHost
theorem _root_.solution {μ : ℕ → ℤ} {src n params row free k : ℕ}
    (color : Coloring.Parameter (inputBits n+1)) (x : Fin n → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hn : 0 < n) (hR : 4 ≤ radix n)
    (hsrc : src+n ≤ free) (hparams : params+19 ≤ free) (hrow : row+6 ≤ free)
    (hspace : space free k n ≤ lim.space) (hword : (word k n : ℤ) ≤ lim.word)
    (hd : d+depth n ≤ lim.depth)
    (hread : Seg μ src (List.ofFn x)) (hbound : ∀ i, |x i| ≤ (n^k : ℕ))
    (hparameters : Seg μ params (LightParameterInit.values n))
    (hcolor : Seg μ row (ColorParameters.fields color)) :
    Meets lim program 71 d [src,n,params,row,free] μ (time k n)
      (fun r ν => r=(prime free n (bandSize n) : ℤ) ∧
        EncodedColorPrimeReadyData.Output ν free n color x ∧ Kept μ ν free) := by
  have ht := EncodedColorPrimeCosts.time_le_budget (nA := n) (nB := n) (nC := n) k hn le_rfl le_rfl le_rfl
  exact (program_meets_input color x hw hn hR hsrc hparams hrow hspace hword hd hread hbound
    hparameters hcolor).mono_time (by unfold inputTime time; omega)
end ThreeSum.LightEncodedColorPrimeHost
