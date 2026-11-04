-- Prove2me | solution 1 for ThreeSum.LightColorIndex.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:37:23.280101+00:00
-- url     : https://prove2.me/submissions/fae6932b-7cf7-4515-a86d-7a173ce4bd18

import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Definitions.Def_Submission_ThreeSum_Coloring
import Definitions.Def_Submission_ThreeSum_LightColorIndex
import Definitions.Def_WeightedCache3SUM_Alias_5d83a00a3f301eb9
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c


set_option autoImplicit false
open ThreeSum ThreeSum.LightColorIndex
open Light LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightColorIndex
theorem _root_.solution {W m powers d : ℕ} (μ : ℕ → ℤ) (p : Coloring.Parameter W)
    (hw : (lim.space : ℤ) ≤ lim.word) (hspace : powers+(W+1) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hpowers : Powers μ powers W) (hm : m < 2^W) (hd : d+W+1 ≤ lim.depth) :
    Meets lim program 0 d [W,m,p.1.1.val,p.1.2.val,
      (p.2 (false,false)).val,(p.2 (false,true)).val,
      (p.2 (true,false)).val,(p.2 (true,true)).val,powers] μ (time W)
      (fun r μ' => r = (color p m : ℤ) ∧ μ' = μ) :=
  meets rfl rfl μ p hw hspace hword hpowers hm hd
end ThreeSum.LightColorIndex
