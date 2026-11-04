-- Prove2me | solution 1 for ThreeSum.ColorClassLists.length_classList_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:41:10.430953+00:00
-- url     : https://prove2.me/submissions/b8540c11-7c56-405a-afc1-cf3883e09fe3

import Definitions.Def_Submission_ThreeSum_LightClassFilter
import Definitions.Def_Submission_ThreeSum_LightColorIndex
import Definitions.Def_Submission_ThreeSum_ColorClassLists
import Theorems.Thm_ThreeSum_LightClassFilter_items_length_le


set_option autoImplicit false
open ThreeSum ThreeSum.ColorClassLists
open LightClassFilter
namespace ThreeSum.ColorClassLists
theorem _root_.solution {n W : ℕ} (p : Coloring.Parameter W) (x : Fin n → ℤ)
    (c : ℕ) (scale : ℤ) : (classList p x c scale).length ≤ n :=
  items_length_le ..
end ThreeSum.ColorClassLists
