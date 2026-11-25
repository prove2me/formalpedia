-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_homogeneousComponent_aeval_coordPlaneSubst_6be6f2ef863d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:32:02.791301+00:00
-- url     : https://prove2.me/submissions/b8001f72-b2a0-4f5f-a77f-6816b96584e5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeFibreAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPointLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeMassOfFibre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Module
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (m k d : ℕ) (f : MvPolynomial (Fin (m + k)) ℂ) :
    homogeneousComponent d (aeval (coordPlaneSubst m k) f) =
      aeval (coordPlaneSubst m k) (homogeneousComponent d f) := by
  have hg : ∀ i, (coordPlaneSubst m k i).IsHomogeneous 1 := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [coordPlaneSubst, Fin.append_left]
      exact isHomogeneous_X ℂ i
    · simp only [coordPlaneSubst, Fin.append_right]
      exact isHomogeneous_zero _ _ _
  have hterm : ∀ e, homogeneousComponent d (aeval (coordPlaneSubst m k) (homogeneousComponent e f)) =
      if e = d then aeval (coordPlaneSubst m k) (homogeneousComponent e f) else 0 := by
    intro e
    have he := (homogeneousComponent_isHomogeneous e f).aeval _ hg
    rw [one_mul] at he
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 he)]
    exact if_congr eq_comm rfl rfl
  conv_lhs => rw [← sum_homogeneousComponent f]
  rw [map_sum, map_sum]
  simp_rw [hterm]
  rw [Finset.sum_ite_eq']
  split_ifs with hd
  · rfl
  · rw [Finset.mem_range, not_lt] at hd
    rw [homogeneousComponent_eq_zero _ _ (by omega), map_zero]
end GroundTheory.Heights₂.Heights
