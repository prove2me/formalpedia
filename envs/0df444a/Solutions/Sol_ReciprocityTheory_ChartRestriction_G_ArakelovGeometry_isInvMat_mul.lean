-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isInvMat_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:44:58.395494+00:00
-- url     : https://prove2.me/submissions/783ceafd-fb28-45ec-bde5-71df3bacb250

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_HSClosing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemCone
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_StepTStA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {J : Type} [Fintype J] [DecidableEq J]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {A : Matrix J J ℚ} (hA : IsInvMat A) :
    ∃ B : Matrix J J ℚ, A * B = 1 ∧ B * A = 1 := by
  obtain ⟨B, hB⟩ := hA
  refine ⟨B, ?_, ?_⟩
  · refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, Matrix.one_mulVec]
    exact (hB v).1
  · refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, Matrix.one_mulVec]
    exact (hB v).2
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
