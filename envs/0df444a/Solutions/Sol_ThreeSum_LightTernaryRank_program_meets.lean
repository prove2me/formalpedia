-- Prove2me | solution 1 for ThreeSum.LightTernaryRank.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:51:52.669238+00:00
-- url     : https://prove2.me/submissions/9096ec2d-b386-4dff-bed7-a6458fdae8c9

import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_ThreeSum_LightTernaryRank
import Theorems.Thm_ThreeSum_LightTernaryRank_meets
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c


set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryRank
open Light Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryCodeSemantics ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryRank
theorem _root_.solution {N m powers d : ℕ} (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers+(2*N+1) ≤ lim.space)
    (hword : ((2^(2*N+1) : ℕ) : ℤ) ≤ lim.word)
    (hscalar : ((2*N+16 : ℕ) : ℤ) ≤ lim.word)
    (hpowers : Powers μ powers (2*N)) (hm : m < 2^(2*N))
    (hdepth : d+2*N+2 ≤ lim.depth) :
    Meets lim program 0 d [N,m,powers] μ (time N)
      (fun r ν => r=(partialRank N m N : ℤ) ∧ ν=μ) :=
  meets rfl rfl rfl μ hw hspace hword hscalar hpowers hm hdepth
end ThreeSum.LightTernaryRank
