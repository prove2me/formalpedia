-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.greenParamFiber_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:33:30.788155+00:00
-- url     : https://prove2.me/submissions/3af10655-afcd-4ffb-ad09-4d44c4dcdc80

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
theorem _root_.solution : GreenParamFiberStatement := by
  intro E _ _ _ u hu hc p
  obtain ⟨R, hR0, hR⟩ := exists_R_of_compact hc
  have hv : ContDiff ℝ 2 (fun w : ℂ => u (w, p)) := hu.comp (contDiff_id.prodMk contDiff_const)
  have h := green_at hv 0 (R := R + 1) (by linarith) (fun z hz =>
    image_eq_zero_of_notMem_tsupport fun hm => by
      have := hR _ hm
      have := norm_fst_le (z, p)
      simp only [sub_zero] at hz
      linarith)
  simpa using h
end ReciprocityTheory.AnForm.A
