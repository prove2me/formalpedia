-- Prove2me | solution 1 for ThreeSum.LightMaskMinimum.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:44:00.925229+00:00
-- url     : https://prove2.me/submissions/679dd631-9f98-4047-a09a-d8c12f576df8

import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Mathlib.Data.Finset.Max
import Definitions.Def_Submission_ThreeSum_LightMaskMinimum
import Definitions.Def_WeightedCache3SUM_Alias_2ab790e73b946b9f
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c


set_option autoImplicit false
open ThreeSum ThreeSum.LightMaskMinimum
open Light ThreeSum.SubsetAddress ThreeSum.MaskErase ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightMaskMinimum
theorem _root_.solution {μ : ℕ → ℤ} {L work d : ℕ}
    (S : Finset (Fin L)) (hS : S.Nonempty)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : work+(L+1) ≤ lim.space)
    (hword : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hd : d+L+1 ≤ lim.depth) :
    Meets lim program 0 d [L,subsetMask S,work] μ (time L)
      (fun r μ' => r = ((S.min' hS).val : ℤ) ∧ Kept μ μ' work) :=
  meets rfl rfl rfl S hS hw hspace hword hd
end ThreeSum.LightMaskMinimum
