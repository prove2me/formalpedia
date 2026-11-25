-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_measurableSet_pts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:40:07.564798+00:00
-- url     : https://prove2.me/submissions/08f084d9-a0d7-42dc-b037-2c645752450a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStA

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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory Filter Topology
variable {J : Type} [Fintype J] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (P : Ideal (MvPolynomial J ℤ)) : MeasurableSet (pts P) := by
  have h1 : IsClosed {z : J → ℂ | ∀ f ∈ P, MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) f) = 0} := by
    have hset : {z : J → ℂ | ∀ f ∈ P, MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) f) = 0} =
        ⋂ f ∈ P, {z : J → ℂ | MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) f) = 0} := by
      ext z
      simp
    rw [hset]
    exact isClosed_biInter fun f _ => isClosed_eq (MvPolynomial.continuous_eval _) continuous_const
  have h2 : MeasurableSet {z : J → ℂ | z ≠ 0} := (measurableSet_singleton (0 : J → ℂ)).compl
  exact h2.inter h1.measurableSet
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
