-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isHomogeneous_linSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:44:43.084552+00:00
-- url     : https://prove2.me/submissions/2d05622d-3525-4372-beee-a54ddf422c92

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
theorem _root_.solution (A : Matrix J J ℚ) {g : MvPolynomial J ℚ} {n : ℕ}
    (hg : g.IsHomogeneous n) : (linSub A g).IsHomogeneous n := by
  have h := hg.eval₂ (algebraMap ℚ (MvPolynomial J ℚ)) (fun i => ∑ j, C (A i j) * X j)
    (fun r => by rw [MvPolynomial.algebraMap_eq]; exact isHomogeneous_C _ _)
    (fun i => IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_C_mul_X _ _)
  rw [one_mul] at h
  exact h
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
