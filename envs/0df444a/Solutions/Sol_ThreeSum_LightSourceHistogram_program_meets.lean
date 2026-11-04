-- Prove2me | solution 1 for ThreeSum.LightSourceHistogram.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:50:15.487306+00:00
-- url     : https://prove2.me/submissions/1e7d78a0-bb3c-4762-ad9e-71ff59460614

import Definitions.Def_Submission_ThreeSum_LightSourceResidues
import Definitions.Def_Submission_ThreeSum_LightHistogram
import Definitions.Def_Submission_ThreeSum_LightSourceHistogram
import Definitions.Def_WeightedCache3SUM_Alias_5b14bc7229a63f1e
import Theorems.Thm_ThreeSum_LightSourceResidues_meets


set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceHistogram
open Light
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceHistogram
theorem _root_.solution
    {μ : ℕ → ℤ} {src hist n p m codes work U D : ℕ} {shift : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth)
    (hp : 0 < p) (hm : 0 < m)
    (hsrc : src+n ≤ codes) (hhist : hist+m ≤ codes) (hcodes : codes+n ≤ work)
    (hspace : LightSourceResidues.space work p U D ≤ lim.space)
    (hshift : |shift| ≤ (D : ℤ))
    (hword : (LightSourceResidues.word p m U D : ℤ) ≤ lim.word)
    (hvalues : ∀ i < n, |μ (src+i)| ≤ (U : ℤ)) :
    Meets lim program 0 d [src,hist,n,p,m,codes,work,shift] μ (time n p m U D)
      (fun _ ν =>
        (∀ i < n, ν (codes+i) =
          (LightSourceResidues.key p m shift (μ (src+i)) : ℤ)) ∧
        (∀ r < m, ν (hist+r) = (LightHistogram.count
          (fun i => LightSourceResidues.key p m shift (μ (src+i))) r n : ℤ)) ∧
        KeptBut μ ν codes hist m) := by
  exact programProcs.meets hw hd hp hm hsrc hhist hcodes hspace hshift hword hvalues
end ThreeSum.LightSourceHistogram
