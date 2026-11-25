-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.HDiscLat.trace_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:57:46.360294+00:00
-- url     : https://prove2.me/submissions/426aaa3f-da07-496c-a0ef-9f638ee9a47f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_HDiscLat_trace_algebraMap_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open ReciprocityTheory.ChartRestriction.G.T0.HDiscLat
open Module
variable {R F : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field F]
  [Algebra R F] [IsFractionRing R F]
  {ι : Type} [Fintype ι] [DecidableEq ι] {L : ι → Type} [∀ c, Field (L c)] [∀ c, Algebra F (L c)]
  [∀ c, FiniteDimensional F (L c)] [∀ c, Algebra.IsSeparable F (L c)] [∀ c, Algebra R (L c)]
  [∀ c, IsScalarTower R F (L c)]
omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R F] [Fintype ι] [DecidableEq ι]
  [∀ c, FiniteDimensional F (L c)] [∀ c, Algebra.IsSeparable F (L c)]
namespace ReciprocityTheory.ChartRestriction.G.T0.HDiscLat
theorem _root_.solution (c : ι) (r r' : R) (h x y : L c) :
    Algebra.trace F (L c) (algebraMap R (L c) r * (h * x) * (algebraMap R (L c) r' * (h * y))) =
      algebraMap R F r * Algebra.trace F (L c) (h * h * x * y) * algebraMap R F r' := by
  have e : algebraMap R (L c) r * (h * x) * (algebraMap R (L c) r' * (h * y)) =
      algebraMap R (L c) r * (algebraMap R (L c) r' * (h * h * x * y)) := by ring
  rw [e, trace_algebraMap_mul, trace_algebraMap_mul]
  ring
end ReciprocityTheory.ChartRestriction.G.T0.HDiscLat
