-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.coneMap_eq_zero_of_mem_pts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:37:30.006349+00:00
-- url     : https://prove2.me/submissions/80483241-b467-41a7-a4da-2dd03054790d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsSmoothPts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemCone
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_coeff_coneMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
noncomputable section
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
theorem _root_.solution {J : Type} [Fintype J] {P : Ideal (MvPolynomial J ℤ)}
    (hP : IsHomogIdeal ℤ P) {z : J → ℂ} (hz : z ∈ pts P) {f : MvPolynomial J ℤ} (hf : f ∈ P) :
    coneMap ℤ z f = 0 := by
  ext d
  rw [coeff_coneMap, Polynomial.coeff_zero]
  have h := hz.2 _ (hP f hf d)
  rw [eval_map] at h
  rw [aeval_def, show algebraMap ℤ ℂ = Int.castRingHom ℂ from Subsingleton.elim _ _]
  exact h
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
