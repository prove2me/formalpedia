-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gaap_measurableSet_pts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:52:11.091718+00:00
-- url     : https://prove2.me/submissions/b6991567-a6e0-4659-a3bd-a69a5e39c20d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsBergDensity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamStB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamSt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder
variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {J : Type} [Fintype J] (P : Ideal (MvPolynomial J ℤ)) :
    MeasurableSet (pts P) := by
  have : pts P = ({0}ᶜ : Set (J → ℂ)) ∩
      ⋂ f ∈ P, {z : J → ℂ | eval z (map (Int.castRingHom ℂ) f) = 0} := by
    ext z
    simp [pts, conePts]
  rw [this]
  refine (measurableSet_singleton 0).compl.inter (IsClosed.measurableSet ?_)
  exact isClosed_biInter fun f _ => isClosed_eq (MvPolynomial.continuous_eval _) continuous_const
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
