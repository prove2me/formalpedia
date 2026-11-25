-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_isChowForm_point_e29c8ba3cc02
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:55:43.761937+00:00
-- url     : https://prove2.me/submissions/fe2280ce-f100-499e-bb27-466ba1830fc6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LatticePointLogCount
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_finIdeal_bot_609cd897da2d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_mem_conePts_bot_8cd7c8de083b

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ArithBezout
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Matrix
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ArithBezout
theorem _root_.solution :
    IsChowForm (Int.castRingHom ℂ) (finIdeal (⊥ : Ideal (MRing (PBlk 1)))) 0 1
      (X (0, 0) : MvPolynomial (Fin (0 + 1) × Fin 1) ℂ) := by
  classical
  refine ⟨fun m hm k => ?_, (X_prime).squarefree, fun u => ?_⟩
  · rw [support_X, Finset.mem_singleton] at hm
    subst hm
    fin_cases k
    simp
  · rw [finIdeal_bot]
    simp only [eval_X]
    constructor
    · intro h
      refine ⟨1, (mem_conePts_bot _).mpr one_ne_zero, fun j => ?_⟩
      fin_cases j
      simpa using h
    · rintro ⟨z, hz, hj⟩
      have hz0 : z 0 ≠ 0 := by
        intro h0
        apply (mem_conePts_bot z).mp hz
        ext i
        fin_cases i
        simpa using h0
      have h := hj 0
      simp only [Fin.sum_univ_one] at h
      exact (mul_eq_zero.mp h).resolve_right hz0
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ArithBezout
