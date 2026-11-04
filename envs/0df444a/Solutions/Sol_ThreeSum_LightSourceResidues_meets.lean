-- Prove2me | solution 1 for ThreeSum.LightSourceResidues.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:40:14.444882+00:00
-- url     : https://prove2.me/submissions/2c0a7ce3-b1d4-465e-a2d3-cf04db569413

import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_LightSourceResidues
import Definitions.Def_WeightedCache3SUM_Alias_2355ab610500aa6c
import Theorems.Thm_Light_Meets_of_body


set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceResidues
open Light
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceResidues
theorem _root_.solution {pMain pEmod : ℕ}
    (hmain : P[pMain]? = some (body pEmod)) (hem : P[pEmod]? = some emodBody)
    {μ : ℕ → ℤ} {src dst n p m work U D : ℕ} {shift : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hp : 0 < p) (hm : 0 < m) (hsrc : src+n ≤ work) (hdst : dst+n ≤ work)
    (hspace : space work p U D ≤ lim.space) (hsep : Apart src n dst n)
    (hshift : |shift| ≤ (D : ℤ)) (hword : (word p m U D : ℤ) ≤ lim.word)
    (hvalues : ∀ i < n, |μ (src+i)| ≤ (U : ℤ)) :
    Meets lim P pMain d [src,dst,n,p,m,work,shift] μ (time n p U D) (fun _ ν =>
      (∀ i < n, ν (dst+i) = (key p m shift (μ (src+i)) : ℤ)) ∧
      KeptBut μ ν work dst n) := by
  exact Meets.of_body hmain (ends hem hw hd hp hm hsrc hdst hspace hsep hshift hword hvalues)
end ThreeSum.LightSourceResidues
