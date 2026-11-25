-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PtsAddFirst_mixedDisc_cons_add_c2f52a1c9aba
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:14:28.094291+00:00
-- url     : https://prove2.me/submissions/f465af27-bbe9-4423-b580-9675f16d89da

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StPtsAddFirst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPtsAddFirst
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_update_add


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
namespace GroundTheory.Heights₂.Heights.Inter
namespace PtsAddFirst
theorem _root_.solution {D : ℕ} (A B : Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ)
    (C : Fin D → Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ) :
    mixedDisc (Fin.cons (A + B) C : Fin (D + 1) → _) =
      mixedDisc (Fin.cons A C : Fin (D + 1) → _) + mixedDisc (Fin.cons B C : Fin (D + 1) → _) := by
  have h := ReciprocityTheory.AnForm.A.mdisc_update_add (Fin.cons A C : Fin (D + 1) → _) 0 A B
  simp only [Fin.update_cons_zero] at h
  exact h
end PtsAddFirst
end GroundTheory.Heights₂.Heights.Inter
