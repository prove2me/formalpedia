-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.aeval_int_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:40:16.705928+00:00
-- url     : https://prove2.me/submissions/97c9a3e3-187c-4d86-aed6-8f2e2bef1fa6

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
variable {J : Type} [Fintype J] {Ω : Type*} [Field Ω] [CharZero Ω]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (z : J → ℂ) (f : MvPolynomial J ℤ) :
    eval z (map (Int.castRingHom ℂ) f) = aeval z f := by
  rw [eval_map, aeval_def, algebraMap_int_eq]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
