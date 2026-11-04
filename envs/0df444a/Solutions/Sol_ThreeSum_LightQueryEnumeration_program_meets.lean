-- Prove2me | solution 1 for ThreeSum.LightQueryEnumeration.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:23:41.88989+00:00
-- url     : https://prove2.me/submissions/475089b7-c09e-42a0-892e-2a76929f7dbb

import Definitions.Def_Submission_ThreeSum_LightQueryWeights
import Definitions.Def_Submission_ThreeSum_LightQueryEnumeration
import Definitions.Def_WeightedCache3SUM_Alias_daea56ef26e5693b
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_874c626a95c648fa
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Definitions.Def_WeightedCache3SUM_Alias_faf0bf412734022a


set_option autoImplicit false
open ThreeSum ThreeSum.LightQueryEnumeration
open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress QueryCoordinates
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightQueryEnumeration
theorem _root_.solution {μ : ℕ → ℤ} {W t dst work d : ℕ}
    (Q : Finset (Fin W))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : work+(2*W+2) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (ht : t ≤ Q.card+1)
    (hdst : dst+Q.card.choose t ≤ work)
    (hd : d+W+2 ≤ lim.depth) :
    Meets lim program 0 d [W,subsetMask Q,t,dst,work] μ (time W Q.card t)
      (fun r μ' => r = (Q.card.choose t : ℤ) ∧
        SegN μ' dst ((missingSets Q t).map subsetMask) ∧
        LightWeightedEnumeration.Weights μ' work Q.card (weights Q) ∧
        KeptBut μ μ' work dst (Q.card.choose t)) :=
  meets rfl rfl rfl rfl rfl Q hw hspace hword ht hdst hd
end ThreeSum.LightQueryEnumeration
