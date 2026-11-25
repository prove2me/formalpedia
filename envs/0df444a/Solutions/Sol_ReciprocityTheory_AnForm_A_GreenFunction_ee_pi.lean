-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.GreenFunction.ee_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:04:24.880811+00:00
-- url     : https://prove2.me/submissions/36857789-e28e-4860-ad48-a3677dd59ce8

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenPolar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Filter Topology InnerProductSpace intervalIntegral
open scoped Laplacian
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.GreenFunction
noncomputable section
namespace ReciprocityTheory.AnForm.A.GreenFunction
theorem _root_.solution : ee Real.pi = ee (-Real.pi) := by
  unfold ee; rw [Real.cos_neg, Real.sin_neg, Real.sin_pi]; simp
end ReciprocityTheory.AnForm.A.GreenFunction
