-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.greenPoint_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:34:21.287813+00:00
-- url     : https://prove2.me/submissions/24793083-0d47-49b6-ab91-deedbff8a037

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenPolar
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LeviOneEqLaplacianThm
import Theorems.Thm_ReciprocityTheory_AnForm_A_exists_R_of_compact
import Theorems.Thm_ReciprocityTheory_AnForm_A_GreenFunction_green_at


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Filter Topology InnerProductSpace
open scoped Laplacian
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open GreenFunction
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution : GreenPointStatement := by
  intro u a hu hc
  obtain ⟨R, hR0, hR⟩ := exists_R_of_compact hc
  exact green_at hu a (R := ‖a‖ + R + 1) (by positivity) (fun z hz =>
    image_eq_zero_of_notMem_tsupport fun hm => by
      have := hR z hm
      have := norm_sub_le z a
      linarith)
end ReciprocityTheory.AnForm.A
