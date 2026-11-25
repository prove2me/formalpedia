-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.dz_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:04:13.915765+00:00
-- url     : https://prove2.me/submissions/fad30767-450d-4196-ba4a-0cabbd8fb5c2

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsCalc
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm Matrix Filter Topology
noncomputable section
variable {D : ℕ} {j : Fin D} {f g : (Fin D → ℂ) → ℂ} {z : Fin D → ℂ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    dz j (fun y => f y + g y) z = dz j f z + dz j g z := by
  have e : fderiv ℝ (fun y => f y + g y) z = fderiv ℝ f z + fderiv ℝ g z := by
    first
    | (exact (hf.hasFDerivAt.add hg.hasFDerivAt).fderiv)
    | (exact (hf.hasFDerivAt.fun_add hg.hasFDerivAt).fderiv)
    | (exact fderiv_add hf hg)
    | (exact fderiv_fun_add hf hg)
  unfold dz
  rw [e, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply]
  ring
end ReciprocityTheory.AnForm.A
