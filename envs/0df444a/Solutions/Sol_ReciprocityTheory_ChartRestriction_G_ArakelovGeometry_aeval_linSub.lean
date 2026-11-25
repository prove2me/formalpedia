-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.aeval_linSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:40:21.827831+00:00
-- url     : https://prove2.me/submissions/65b710a9-4f76-443c-9ded-bce381e28668

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
variable {Ω : Type*} [Field Ω] [CharZero Ω]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (A : Matrix J J ℚ) (v : J → Ω) (g : MvPolynomial J ℚ) :
    aeval v (linSub A g) = aeval (matAct A v) g := by
  simp only [linSub, aeval_bind₁]
  congr 2
  funext i
  simp [matAct, eq_ratCast]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
