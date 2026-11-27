-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_linearIndependent_y_af19704e976b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:57:22.74+00:00
-- url     : https://prove2.me/submissions/84580301-8a96-4194-809f-aed1dbf83656

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsSmoothPts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_incl_y_mul_279e0f8187fe
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
theorem _root_.solution : LinearIndependent ℤ y := by
  rw [Fintype.linearIndependent_iff]
  intro g hg p
  have hs : (g ⟨(), 0⟩ : FnField) + (g ⟨(), 1⟩ : FnField) * uF = 0 := by
    rw [Fintype.sum_sigma] at hg
    simpa [Fin.sum_univ_two, zsmul_eq_mul] using hg
  have hK : algebraMap (MRing (GlobalTheory (Fin 2))) Kfr (C (g ⟨(), 0⟩) * X ⟨(), 0⟩ + C (g ⟨(), 1⟩) * X ⟨(), 1⟩) = 0 := by
    have := congrArg (fun t => incl t * Xk 0) hs
    simp only [map_add, map_mul, map_intCast, map_zero, zero_mul] at this
    rw [map_add, map_mul, map_mul, ← this]
    have hu : incl uF * Xk 0 = Xk 1 := incl_y_mul ⟨(), 1⟩
    simp only [map_intCast, eq_intCast]
    rw [add_mul, mul_assoc, hu]
  have hP : C (g ⟨(), 0⟩) * X ⟨(), 0⟩ + C (g ⟨(), 1⟩) * (X ⟨(), 1⟩ : MRing (GlobalTheory (Fin 2))) = 0 :=
    (IsFractionRing.injective (MRing (GlobalTheory (Fin 2))) Kfr) (by rw [hK, map_zero])
  obtain ⟨⟨⟩, i⟩ := p
  fin_cases i
  · have := congrArg (eval (fun q : Ix (Fin 2) => ![(1 : ℤ), 0] q.2)) hP
    simpa using this
  · have := congrArg (eval (fun q : Ix (Fin 2) => ![(0 : ℤ), 1] q.2)) hP
    simpa using this
end GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine
