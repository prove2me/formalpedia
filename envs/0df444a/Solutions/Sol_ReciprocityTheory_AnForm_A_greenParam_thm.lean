-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.greenParam_thm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:49:34.343122+00:00
-- url     : https://prove2.me/submissions/b665d0ee-58a8-4aa8-8d8e-d82932facbea

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenPolar
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LeviOneEqLaplacianThm
import Theorems.Thm_ReciprocityTheory_AnForm_A_greenParam_main

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
theorem _root_.solution : GreenParamStatement := greenParam_main
end ReciprocityTheory.AnForm.A
