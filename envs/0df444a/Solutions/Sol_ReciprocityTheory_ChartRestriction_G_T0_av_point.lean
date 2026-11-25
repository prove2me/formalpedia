-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.av_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:03:31.188644+00:00
-- url     : https://prove2.me/submissions/fbcedff4-5113-411d-9520-752e8c4c0a96

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_DiscreteValuationPoint
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_RegAVpt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_DiscreteValuationPoint_exists_dvr_point_flat_algebra


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open IsLocalRing
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {O B : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CharZero O]
    [CommRing B] [IsDomain B] [Algebra O B] [Algebra.FiniteType O B] [Module.Flat O B]
    (hsp : Ideal.map (algebraMap O B) (maximalIdeal O) ≠ ⊤) (e : B) (he : e ≠ 0) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Algebra O V)
      (_ : Module.Finite O V) (φ : B →ₐ[O] V), φ e ≠ 0 :=
  DiscreteValuationPoint.exists_dvr_point_flat_algebra hsp e he
end ReciprocityTheory.ChartRestriction.G.T0
