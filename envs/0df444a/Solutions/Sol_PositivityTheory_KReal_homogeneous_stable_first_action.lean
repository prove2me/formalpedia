-- Prove2me | solution 1 for PositivityTheory.KReal.homogeneous_stable_first_action
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:07:59.238425+00:00
-- url     : https://prove2.me/submissions/dbf20758-18e3-49fd-a232-b6ab6fa40c7a

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreLie
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreHarm
import Theorems.Thm_PositivityTheory_KReal_Harm_homogComponent_comm_first_action

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal
open Harm
variable {p q r s : ℕ}
namespace PositivityTheory.KReal
theorem _root_.solution (d : ℕ) : KSt (units (fockAct1 p q r s)) (homog (Ix p q × Ix r s) d) := by
  unfold KSt units
  intro a b hab P hP
  have hP' : P = homogeneousComponent d P := by rw [homogeneousComponent_of_mem hP, if_pos rfl]
  rw [hP', ← homogComponent_comm_first_action hab]
  exact homogeneousComponent_mem _ _
end PositivityTheory.KReal
