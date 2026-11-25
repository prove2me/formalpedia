-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_P1_linearIndependent_alt_363dd652fbe0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:56:54.266425+00:00
-- url     : https://prove2.me/submissions/984c32e6-f97a-408b-8d05-98582ab31d0a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_FderivFderivLogRho
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemCone
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_FirstPointNeSecondPoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_P1_twoPoint_cases_497451a37eee
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_P1_sum_twoPoint_84780d96d978

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.P1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.P1
theorem _root_.solution : LinearIndependent ℤ x := by
  rw [Fintype.linearIndependent_iff]
  intro g hg q
  rw [sum_twoPoint] at hg
  have h : algebraMap (Polynomial ℤ) Fld (Polynomial.C (g p0) + Polynomial.C (g p1) * Polynomial.X) =
      0 := by
    rw [← hg]
    simp [x, val, p0, p1, zsmul_eq_mul]
  have hp : Polynomial.C (g p0) + Polynomial.C (g p1) * Polynomial.X = 0 :=
    IsFractionRing.injective (Polynomial ℤ) Fld (by rw [h, map_zero])
  have h0 := congrArg (Polynomial.coeff · 0) hp
  have h1 := congrArg (Polynomial.coeff · 1) hp
  simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X] at h0 h1
  simp at h0 h1
  rcases twoPoint_cases q with rfl | rfl
  · exact h0
  · exact h1
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.P1
