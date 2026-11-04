-- Prove2me | solution 1 for ThreeSum.ColorScan.hit_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:43:24.375954+00:00
-- url     : https://prove2.me/submissions/61520730-60f5-4fd0-8312-4c934bc226cc

import Definitions.Def_Submission_ThreeSum_ColorParameters
import Definitions.Def_Submission_ThreeSum_ColorScan
import Definitions.Def_WeightedCache3SUM_Alias_a2077ae4d725396c
import Theorems.Thm_ThreeSum_ColorParameters_reduction_correct
import Theorems.Thm_ThreeSum_Coloring_reduction_correct


set_option autoImplicit false
open ThreeSum ThreeSum.ColorScan
open ColorParameters
namespace ThreeSum.ColorScan
theorem _root_.solution {n W : ℕ} (x : Fin n → ℤ) (hn : n ≤ 2^W) :
    Hit x W (count W) ↔ Coloring.DistinctZeroSum x := by
  rw [ColorParameters.reduction_correct x hn]
  constructor
  · rintro ⟨i,hi,_,hx⟩
    exact ⟨i,hi,hx⟩
  · rintro ⟨i,hi,hx⟩
    exact ⟨i,hi,hi,hx⟩
end ThreeSum.ColorScan
