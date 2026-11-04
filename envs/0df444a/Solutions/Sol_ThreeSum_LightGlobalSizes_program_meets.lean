-- Prove2me | solution 1 for ThreeSum.LightGlobalSizes.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:58:45.995758+00:00
-- url     : https://prove2.me/submissions/9d40d125-6423-4bec-aeea-c27d442a62be

import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSum_BandScales
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Sqrt
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSum_LightGlobalSizes
import Definitions.Def_WeightedCache3SUM_Alias_3718d050d478b160
import Definitions.Def_WeightedCache3SUM_Alias_d92129e9a4741fac
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab


set_option autoImplicit false
open ThreeSum ThreeSum.LightGlobalSizes
set_option maxHeartbeats 1000000
open Light LocalCoverBounds
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightGlobalSizes
theorem _root_.solution {μ : ℕ → ℤ} {C p J mu dst : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hC : 1 ≤ C) (hp : 1 ≤ p) (hspace : dst+5 ≤ lim.space)
    (hword : (word C p J mu : ℤ) ≤ lim.word) :
    Meets lim program 0 d [C,p,J,mu,dst] μ (time C J mu)
      (fun r μ' => r = ((p^J : ℕ) : ℤ) ∧ Seg μ' dst (values C p J mu) ∧
        SameOutside μ μ' dst 5) := procs.meets hw hd hC hp hspace hword
end ThreeSum.LightGlobalSizes
