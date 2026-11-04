-- Prove2me | solution 1 for ThreeSum.LightTernaryColorPrelude.witness_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:40:40.519786+00:00
-- url     : https://prove2.me/submissions/153b7736-5396-4acb-96c4-a80d6e6e154a

import Definitions.Def_Submission_ThreeSum_LightColorBands
import Definitions.Def_Submission_ThreeSum_LightColorParametersCosts
import Definitions.Def_Submission_ThreeSum_LightColorScanHost
import Definitions.Def_Submission_ThreeSum_LightTernaryColorPrelude
import Theorems.Thm_ThreeSum_Karatsuba_CoeffBound_mem


set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryColorPrelude
open Light ColorClassLists LightColorParametersCosts
set_option maxHeartbeats 7000000
set_option maxRecDepth 20000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryColorPrelude
theorem _root_.solution {n : ℕ} {p : Coloring.Parameter (width n)} {x : Fin n→ℤ}
    {μ : ℕ→ℤ} {ab bb cb : ℕ} {A B C : List ℤ}
    (hA : Normalized μ ab n (classList p x 0 1) A)
    (hB : Normalized μ bb n (classList p x 1 1) B)
    (hC : Normalized μ cb n (classList p x 2 (-1)) C) :
    witness A B C↔ColorClassLists.witness p x :=by
  unfold witness ColorClassLists.witness
  constructor
  · rintro ⟨a,ha,b,hb,c,hc,he⟩
    exact ⟨a,(hA.mem a).mp ha,b,(hB.mem b).mp hb,c,(hC.mem c).mp hc,by omega⟩
  · rintro ⟨a,ha,b,hb,c,hc,he⟩
    exact ⟨a,(hA.mem a).mpr ha,b,(hB.mem b).mpr hb,c,(hC.mem c).mpr hc,by omega⟩
end ThreeSum.LightTernaryColorPrelude
