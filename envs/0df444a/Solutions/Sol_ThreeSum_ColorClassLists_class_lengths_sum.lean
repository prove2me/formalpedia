-- Prove2me | solution 1 for ThreeSum.ColorClassLists.class_lengths_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:31:09.595289+00:00
-- url     : https://prove2.me/submissions/a2204075-743a-4c12-b930-c4b00a749eb3

import Definitions.Def_Submission_ThreeSum_LightClassFilter
import Definitions.Def_Submission_ThreeSum_LightColorIndex
import Definitions.Def_Submission_ThreeSum_ColorClassLists
import Theorems.Thm_ThreeSum_ColorClassLists_items_lengths_sum
import Theorems.Thm_ThreeSum_LightColorIndex_color_lt


set_option autoImplicit false
open ThreeSum ThreeSum.ColorClassLists
open LightClassFilter
namespace ThreeSum.ColorClassLists
theorem _root_.solution {n W : ℕ} (p : Coloring.Parameter W) (x : Fin n → ℤ) :
    (classList p x 0 1).length + (classList p x 1 1).length +
      (classList p x 2 (-1)).length = n :=
  items_lengths_sum _ _ (LightColorIndex.color_lt p) n
end ThreeSum.ColorClassLists
