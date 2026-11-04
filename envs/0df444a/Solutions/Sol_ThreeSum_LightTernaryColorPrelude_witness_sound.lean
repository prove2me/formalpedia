-- Prove2me | solution 1 for ThreeSum.LightTernaryColorPrelude.witness_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:53:12.656293+00:00
-- url     : https://prove2.me/submissions/192d8aac-a43e-4540-a0ae-294d0aad13fb

import Definitions.Def_Submission_ThreeSum_LightColorBands
import Definitions.Def_Submission_ThreeSum_LightColorParametersCosts
import Definitions.Def_Submission_ThreeSum_LightColorScanHost
import Definitions.Def_Submission_ThreeSum_LightTernaryColorPrelude
import Theorems.Thm_ThreeSum_LightTernaryColorPrelude_witness_positions

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
    (hC : Normalized μ cb n (classList p x 2 (-1)) C)
    (H : witness A B C) : Coloring.DistinctZeroSum x :=by
  obtain ⟨a,ha,b,hb,c,hc,he⟩:=H
  obtain ⟨i,j,k,hij,hik,hjk,_,_,_,hsum⟩:=witness_positions hA hB hC ha hb hc he
  exact ⟨i,j,k,hij,hik,hjk,hsum⟩
end ThreeSum.LightTernaryColorPrelude
