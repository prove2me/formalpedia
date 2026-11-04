-- Prove2me | solution 1 for ThreeSum.LightSourceResidues.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:43:27.037088+00:00
-- url     : https://prove2.me/submissions/d39cd108-f82c-41a4-b17d-671953f7b34d

import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_LightSourceResidues
import Theorems.Thm_ThreeSum_LightSourceResidues_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceResidues
open Light
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceResidues
theorem _root_.solution
    {μ : ℕ → ℤ} {src dst n p m work U D : ℕ} {shift : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hp : 0 < p) (hm : 0 < m) (hsrc : src+n ≤ work) (hdst : dst+n ≤ work)
    (hspace : space work p U D ≤ lim.space) (hsep : Apart src n dst n)
    (hshift : |shift| ≤ (D : ℤ)) (hword : (word p m U D : ℤ) ≤ lim.word)
    (hvalues : ∀ i < n, |μ (src+i)| ≤ (U : ℤ)) :
    Meets lim program 0 d [src,dst,n,p,m,work,shift] μ (time n p U D) (fun _ ν =>
      (∀ i < n, ν (dst+i) = (key p m shift (μ (src+i)) : ℤ)) ∧
      KeptBut μ ν work dst n) := by
  exact meets rfl rfl hw hd hp hm hsrc hdst hspace hsep hshift hword hvalues
end ThreeSum.LightSourceResidues
