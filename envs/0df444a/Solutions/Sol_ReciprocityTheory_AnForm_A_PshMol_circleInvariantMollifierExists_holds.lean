-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PshMol.circleInvariantMollifierExists_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:19:16.769461+00:00
-- url     : https://prove2.me/submissions/265d02ee-8089-43f4-b0f9-ff322b8de540

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMean
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshMol_radialBump_contDiff
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshMol_radialBump_nonneg
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshMol_radialBump_support
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshMol_radialBump_smul
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshMol_integral_radialBump_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set Filter Topology Real
open MeasureTheory Metric Set Filter Topology Real
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PshMol
noncomputable section
namespace ReciprocityTheory.AnForm.A.PshMol
theorem _root_.solution : MollifierInhabitStatement := fun D =>
  ⟨{ toFun := fun w => (∫ v, g0 D v)⁻¹ * g0 D w
     contDiff := contDiff_const.mul (radialBump_contDiff D)
     nonneg := fun w => mul_nonneg (inv_nonneg.2 (integral_radialBump_pos D).le) (radialBump_nonneg D w)
     support_subset := fun w hw => radialBump_support D (fun h => hw (by simp [h]))
     integral_eq_one := by
       rw [integral_const_mul, inv_mul_cancel₀ (integral_radialBump_pos D).ne']
     circle_inv := fun c w hc => by simp only [radialBump_smul D c w hc] }⟩
end ReciprocityTheory.AnForm.A.PshMol
