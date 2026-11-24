-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.dz_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:34.128485+00:00
-- url     : https://prove2.me/submissions/91105681-0568-4d56-99af-ea9bcd89d6f7

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
    dz j (fun y => f y * g y) z = dz j f z * g z + f z * dz j g z := by
  have e : fderiv ℝ (fun y => f y * g y) z = f z • fderiv ℝ g z + g z • fderiv ℝ f z := by
    first
    | (exact (hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv)
    | (exact (hf.hasFDerivAt.fun_mul hg.hasFDerivAt).fderiv)
    | (exact fderiv_mul hf hg)
    | (exact fderiv_fun_mul hf hg)
  unfold dz
  rw [e]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring
end ReciprocityTheory.AnForm.A
