-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_leviForm_gbPot_one_f3b2116693be
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:53:20.557687+00:00
-- url     : https://prove2.me/submissions/eec7a366-eb53-44cd-923e-5e7f3e79a4dd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMassStA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviFormGbPotOne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_fderiv_fderiv_gbPot_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_gbBil_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
open MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo
open scoped ENNReal ComplexOrder
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
theorem _root_.solution (z w : Fin 1 → ℂ) :
    leviForm (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbPot (D := 1)) z w =
      ((w 0).re ^ 2 + (w 0).im ^ 2) / (2 * (1 + (z 0).re ^ 2 + (z 0).im ^ 2) ^ 2) := by
  have hG : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbG z = 1 + (z 0).re ^ 2 + (z 0).im ^ 2 := by
    simp [ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbG, Complex.sq_norm, Complex.normSq_apply]; ring
  have hpos : 0 < 1 + (z 0).re ^ 2 + (z 0).im ^ 2 := by positivity
  simp only [leviForm, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.fderiv_fderiv_gbPot_apply, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbBil_apply,
    hG, Fin.sum_univ_one, Pi.smul_apply, smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im]
  field_simp
  ring
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
