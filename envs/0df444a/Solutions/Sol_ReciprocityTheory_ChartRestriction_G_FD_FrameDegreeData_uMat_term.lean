-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.uMat_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:54:46.585725+00:00
-- url     : https://prove2.me/submissions/225b2580-7fcd-4efe-abf3-1218040f8d42

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DetSubUpper
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UMatUpper

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open NumberField Complex Matrix
open scoped ComplexConjugate
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
theorem _root_.solution (G : Matrix (Fin n) (Fin n) ℂ) (c m j : Fin n) :
    uMat G j c * G j m = (if j = c then G c m else 0) +
      (if h : j < c then -(Matrix.vecMul (rowc G c) (blk G c)⁻¹) ⟨j, h⟩ * G j m else 0) := by
  simp only [uMat, Matrix.of_apply]
  by_cases h1 : j = c
  · subst h1
    simp
  · by_cases h2 : j < c
    · simp [h1, h2]
    · simp [h1, h2]
end ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
