-- Prove2me | solution 1 for ThreeSum.LightQueryWeights.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:01:57.98738+00:00
-- url     : https://prove2.me/submissions/74dbb47e-36b8-4d76-adcb-93a6ba8b80f7

import Definitions.Def_Submission_ThreeSum_QueryCoordinates
import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Definitions.Def_Submission_ThreeSum_LightQueryWeights
import Definitions.Def_WeightedCache3SUM_Alias_874c626a95c648fa
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Definitions.Def_WeightedCache3SUM_Alias_faf0bf412734022a


set_option autoImplicit false
open ThreeSum ThreeSum.LightQueryWeights
open Light ThreeSum.SubsetAddress ThreeSum.MaskErase ThreeSum.LightSubsetAddress
open QueryCoordinates
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightQueryWeights
theorem _root_.solution {μ : ℕ → ℤ} {W dst work d : ℕ}
    (Q : Finset (Fin W))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hdst : dst+W ≤ work)
    (hspace : work+(W+1) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hd : d+W+1 ≤ lim.depth) :
    Meets lim program 0 d [W,subsetMask Q,dst,work] μ (time W)
      (fun r μ' => r = (Q.card : ℤ) ∧
        SegN μ' dst (selectedPowers Q W) ∧ Powers μ' work W ∧
        KeptBut μ μ' work dst W) :=
  meets rfl rfl rfl Q hw hdst hspace hword hd
end ThreeSum.LightQueryWeights
