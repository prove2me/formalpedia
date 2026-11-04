-- Prove2me | solution 1 for ThreeSum.LightSubsetAddress.rankProgram_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:18:04.395667+00:00
-- url     : https://prove2.me/submissions/9e3aaf88-e834-45c8-bb61-be660f9c24f5

import Definitions.Def_Submission_ThreeSum_LightPascal
import Definitions.Def_Submission_ThreeSum_SubsetAddress
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_PowTable
import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_WeightedCache3SUM_Alias_9a3b2d25906ae04a

set_option autoImplicit false
open ThreeSum ThreeSum.LightSubsetAddress
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightSubsetAddress
theorem _root_.solution {W table powers L k m d : ℕ} (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (htspace : table+tableSize W ≤ lim.space)
    (hpspace : powers+(W+1) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (htable : Table μ table W) (hpowers : Powers μ powers W)
    (hL : L ≤ W) (hm : IsMask L k m) (hd : d+L ≤ lim.depth) :
    Meets lim rankProgram 0 d [L,k,m,W,table,powers] μ (rankTime L)
      (fun r μ' => r = (layerRank L k m : ℤ) ∧ μ' = μ) :=
  rank_meets rfl μ hw htspace hpspace hword htable hpowers L k m hL hm d hd
end ThreeSum.LightSubsetAddress
