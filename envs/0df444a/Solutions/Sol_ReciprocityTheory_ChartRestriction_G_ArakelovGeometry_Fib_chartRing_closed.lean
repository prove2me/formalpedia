-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.chartRing_closed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:38:05.385412+00:00
-- url     : https://prove2.me/submissions/c6c3fdff-9af1-41a7-bce6-643bb5d5c909

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_EqZeroOfSecTraceMulEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_chartGen_indep
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_chartGen_indep


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
theorem _root_.solution (y : Fin (D + 1) → Ω) (hfree : coordIdeal ℤ y = ⊥) :
    IsIntegrallyClosed (chartRing y) := by
  have hind := chartGen_indep y hfree
  haveI : UniqueFactorizationMonoid (chartRing y) :=
    MulEquiv.uniqueFactorizationMonoid hind.aevalEquiv.toRingEquiv.toMulEquiv inferInstance
  haveI : IsDomain (chartRing y) := Subalgebra.isDomain _
  exact UniqueFactorizationMonoid.instIsIntegrallyClosed
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
