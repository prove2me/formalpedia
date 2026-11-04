-- Prove2me | solution 1 for ThreeSum.LightSourceBuild.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:05:43.856972+00:00
-- url     : https://prove2.me/submissions/2c8519f2-cbce-479a-8783-40b2fb6ecca0

import Definitions.Def_Submission_ThreeSum_LightSourceGather
import Definitions.Def_Submission_ThreeSum_LightSourceBuild
import Theorems.Thm_ThreeSum_LightSourceBuild_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_27f79aa230fbddf9
import Definitions.Def_WeightedCache3SUM_Alias_5b14bc7229a63f1e
import Theorems.Thm_ThreeSum_LightSourceResidues_meets


set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceBuild
open Light
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceBuild
theorem _root_.solution
    {μ : ℕ → ℤ} {src N raw flags n p m hist dst codes work U D E : ℕ} {shift : ℤ}
    (endpoint : ℕ → ℤ) (flag : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth)
    (hp : 0 < p) (hm : 0 < m)
    (hsrc : src+N ≤ hist) (hraw : raw+n ≤ hist) (hflags : flags+n ≤ hist)
    (hhist : hist+m ≤ dst) (hdst : dst+n ≤ codes) (hcodes : codes+N ≤ work)
    (hspace : space work p U D E ≤ lim.space)
    (hshift : |shift| ≤ (D : ℤ)) (hword : (word p m U D E : ℤ) ≤ lim.word)
    (hvalues : ∀ i < N, |μ (src+i)| ≤ (U : ℤ))
    (hrawRead : ∀ i < n, μ (raw+i) = endpoint i)
    (hrawBound : ∀ i < n, |endpoint i| ≤ (E : ℤ))
    (hflagRead : ∀ i < n, μ (flags+i) = (flag i : ℤ))
    (hflagBound : ∀ i < n, flag i ≤ 1) :
    Meets lim program 0 d [src,N,raw,flags,n,p,m,hist,dst,codes,work,shift]
      μ (time N n p m U D E) (fun _ ν =>
        (∀ i < n, ν (dst+i) = (LightSourceGather.value m endpoint flag
          (fun r => LightHistogram.count
            (fun j => LightSourceResidues.key p m shift (μ (src+j))) r N) i : ℤ)) ∧
        (∀ r < m, ν (hist+r) = (LightHistogram.count
          (fun j => LightSourceResidues.key p m shift (μ (src+j))) r N : ℤ)) ∧
        Kept μ ν hist) := by
  exact programProcs.meets endpoint flag hw hd hp hm hsrc hraw hflags hhist hdst hcodes
    hspace hshift hword hvalues hrawRead hrawBound hflagRead hflagBound
end ThreeSum.LightSourceBuild
