-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_incl_y_mul_279e0f8187fe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:30:41.674714+00:00
-- url     : https://prove2.me/submissions/75cfc456-5a14-4b3f-b8b8-5d7ee9995895

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsSmoothPts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_Xk_ne_zero_a1d1c3274004
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.y_zero
attribute [local simp] GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.y_one

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine
theorem _root_.solution (p : Ix (Fin 2)) : incl (y p) * Xk 0 = algebraMap _ Kfr (X p : MRing (GlobalTheory (Fin 2))) := by
  obtain ⟨⟨⟩, i⟩ := p
  fin_cases i
  · simp [y]
  · simp only [y, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    change u * Xk 0 = Xk 1
    rw [u, div_mul_cancel₀ _ (Xk_ne_zero 0)]
end GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine
