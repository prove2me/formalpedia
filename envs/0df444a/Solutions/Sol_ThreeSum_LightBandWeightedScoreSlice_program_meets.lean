-- Prove2me | solution 1 for ThreeSum.LightBandWeightedScoreSlice.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:36:02.237212+00:00
-- url     : https://prove2.me/submissions/33f4b911-717b-4ad4-a7e9-6147941fef05

import Definitions.Def_Submission_ThreeSum_BandWeightedScore
import Definitions.Def_Submission_ThreeSum_LightBandWeightedScoreSlice
import Definitions.Def_WeightedCache3SUM_Alias_0f0d845b38fcc358
import Definitions.Def_WeightedCache3SUM_Alias_4c62aff33317338c
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_f2e191e7f7b92ebc
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_e1d95931a2ead3e4
import Theorems.Thm_ThreeSum_LightModuloCounts_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_03cdb09d18890d4e
import Theorems.Thm_ThreeSum_LightPrimeChain_Procs_meets
import Theorems.Thm_ThreeSum_LightPrimeMinimum_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e
import Definitions.Def_WeightedCache3SUM_Alias_280261ae8ac7fab5


set_option autoImplicit false
open ThreeSum ThreeSum.LightBandWeightedScoreSlice
open Light
set_option maxHeartbeats 900000
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
namespace ThreeSum.LightBandWeightedScoreSlice
theorem _root_.solution {n g i : ℕ}
    (hg : 0 < g) (hi : i*g ≤ n) (hword : ((n+g+4 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim program 0 d [n,g,i] μ time
      (fun r ν => r=(BandWeightedScore.length n g i : ℤ) ∧ ν=μ) :=
  meets rfl hg hi hword
end ThreeSum.LightBandWeightedScoreSlice
