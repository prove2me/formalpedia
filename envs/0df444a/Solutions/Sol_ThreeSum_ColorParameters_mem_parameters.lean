-- Prove2me | solution 1 for ThreeSum.ColorParameters.mem_parameters
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:48:48.202294+00:00
-- url     : https://prove2.me/submissions/01bf91b2-669b-47bf-a399-0f0457ab18cf

import Definitions.Def_Submission_ThreeSum_ColorClassLists
import Mathlib.Data.List.FinRange
import Definitions.Def_Submission_ThreeSum_ColorParameters
import Theorems.Thm_ThreeSum_ColorParameters_parameter_index

set_option autoImplicit false
open ThreeSum ThreeSum.ColorParameters
namespace ThreeSum.ColorParameters
theorem _root_.solution {W : ℕ} (p : Coloring.Parameter W) : p ∈ parameters W := by
  apply List.mem_ofFn.mpr
  exact ⟨⟨index p,index_lt p⟩,parameter_index p⟩
end ThreeSum.ColorParameters
