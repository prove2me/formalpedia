-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedEnumerationSetup.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:25:17.744867+00:00
-- url     : https://prove2.me/submissions/9b2a7222-8a15-41fc-b60e-39bb2d27a31e

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_LightEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_EnumerationSetup
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedEnumerationSetup_meets
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightCacheEnumeration_meets


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedEnumerationSetup
open Light ThreeSum.LightSubsetAddress ThreeSum.WeightedAddresses
variable {lim : Limits} {P : Program}
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedEnumerationSetup
theorem _root_.solution {μ : ℕ → ℤ} {N T dst work d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : work+(2*N+1) ≤ lim.space)
    (hword : ((4^(N+1) : ℕ) : ℤ) ≤ lim.word)
    (hcontrol : ((2740*N+3000 : ℕ) : ℤ)≤lim.word)
    (hcut : T ≤ 2740*N) (hdst : dst+(codes N T).length ≤ work)
    (hd : d+N+2 ≤ lim.depth) :
    Meets lim program 0 d [N,T,dst,work] μ (time N T)
      (fun r μ' => r = ((codes N T).length : ℤ) ∧
        Seg μ' dst ((codes N T).map (fun (a : ℕ) => (a : ℤ))) ∧
        Powers μ' work (2*N) ∧ KeptBut μ μ' work dst (codes N T).length) :=
  meets rfl rfl rfl hw hspace hword hcontrol hcut hdst hd
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedEnumerationSetup
