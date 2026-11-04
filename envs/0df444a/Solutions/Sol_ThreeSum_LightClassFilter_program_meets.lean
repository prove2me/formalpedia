-- Prove2me | solution 1 for ThreeSum.LightClassFilter.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:32:40.871208+00:00
-- url     : https://prove2.me/submissions/3394f247-edf4-435d-8b34-1e138b3896f7

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightClassFilter
import Definitions.Def_WeightedCache3SUM_Alias_98152438e5b788f3

set_option autoImplicit false
open ThreeSum ThreeSum.LightClassFilter
open Light
set_option maxHeartbeats 1200000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightClassFilter
theorem _root_.solution {src colors dst n want U : ℕ} {scale : ℤ} {μ : ℕ → ℤ}
    (x : ℕ → ℤ) (color : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (h3 : (3 : ℤ) ≤ lim.word)
    (hsrc : src+n ≤ dst) (hcolors : colors+n ≤ dst) (hspace : dst+(n+1) ≤ lim.space)
    (hwant : want < 3) (hscale : |scale| ≤ 1) (hU : (U : ℤ) ≤ lim.word)
    (hread : ∀ i < n, μ (src+i) = x i)
    (hcolorRead : ∀ i < n, μ (colors+i) = (color i : ℤ))
    (hcolorLt : ∀ i < n, color i < 3) (hbound : ∀ i < n, |x i| ≤ (U : ℤ)) :
    Meets lim program 0 d [src,colors,dst,n,want,scale] μ (time n)
      (fun r ν => r = ((items x color want scale n).length : ℤ) ∧
        ν dst = ((items x color want scale n).length : ℤ) ∧
        Seg ν (dst+1) (items x color want scale n) ∧ SameOutside μ ν dst (n+1)) :=
  meets rfl x color hw h3 hsrc hcolors hspace hwant hscale hU hread hcolorRead hcolorLt hbound
end ThreeSum.LightClassFilter
