-- Prove2me | solution 1 for ThreeSum.LightBandPartition.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:22:47.168401+00:00
-- url     : https://prove2.me/submissions/fdf0b029-6c84-4c52-892d-6f1b160bf479

import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Copy
import Definitions.Def_Submission_ThreeSum_LightBandPartition
import Definitions.Def_WeightedCache3SUM_Alias_fecb00c51dea7534
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab


set_option autoImplicit false
open ThreeSum ThreeSum.LightBandPartition
open Light ThreeSum.BandPartition
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightBandPartition
theorem _root_.solution {src dst n g d : ℕ} (μ : ℕ → ℤ) (f : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hg : 0 < g)
    (hsrc : src+n ≤ dst) (hspace : dst+2*n ≤ lim.space)
    (hword : ((n+g+2 : ℕ) : ℤ) ≤ lim.word)
    (hread : ∀ i < n, μ (src+i) = f i) (hd : d+1 ≤ lim.depth) :
    Meets lim program 0 d [src,n,g,dst] μ (time n g)
      (fun r μ' => r = (size n g : ℤ) ∧
        (∀ i < size n g, μ' (dst+i) = f (start g i)) ∧
        (∀ i < size n g, μ' (dst+n+i) = f (stop n g i-1)) ∧
        SameOutside μ μ' dst (2*n)) :=
  meets rfl rfl rfl rfl μ f hw hg hsrc hspace hword hread hd
end ThreeSum.LightBandPartition
