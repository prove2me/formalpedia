-- Prove2me | solution 1 for ThreeSum.LightResidues.residues_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:41:07.623691+00:00
-- url     : https://prove2.me/submissions/b43d9a78-bd99-413b-88ea-27d787878a2f

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Emod
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_WeightedCache3SUM_Alias_ee451be6d9f91457
import Theorems.Thm_Light_Meets_of_body


set_option autoImplicit false
open ThreeSum ThreeSum.LightResidues
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightResidues
theorem _root_.solution {pResidues pEmod : ℕ}
    (hres : P[pResidues]? = some (residuesBody pEmod))
    (hem : P[pEmod]? = some emodBody)
    {μ : ℕ → ℤ} {src dst n p work U : ℕ} {c : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hp : 0 < p) (hsrc : src + n ≤ work) (hdst : dst + n ≤ work)
    (hspace : work + (Nat.log 2 (U + 1) + 2) ≤ lim.space)
    (hsep : Apart src n dst n) (hc : |c| ≤ 1)
    (hword : (4 * U + 4 * p + 16 : ℤ) ≤ lim.word)
    (hvalues : ∀ i < n, |μ (src + i)| ≤ (U : ℤ)) :
    Meets lim P pResidues d [src, dst, n, p, work, c] μ (residuesTime n U)
      fun _ μ' =>
        (∀ i < n, μ' (dst + i) = (residue p c (μ (src + i)) : ℤ)) ∧
          KeptBut μ μ' work dst n := by
  exact Meets.of_body hres (residues_ends hem hw hd hp hsrc hdst hspace hsep hc hword hvalues)
end ThreeSum.LightResidues
