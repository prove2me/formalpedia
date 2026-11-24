-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds.chartRing_closed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:49.261497+00:00
-- url     : https://prove2.me/submissions/f59c0f41-51b8-4e8e-8003-bfbbe99a708f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ProjectiveFrameCoordNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_BasisOfLinearIndependentOfCardEqFinrank
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
theorem _root_.solution (x : κ → Ω) (e : Fin (D + 1) → κ) (hfree : coordIdeal ℤ (x ∘ e) = ⊥)
    (l : Fin (D + 1)) : IsIntegrallyClosed (chartRing x e l) := by
  unfold chartRing
  haveI : UniqueFactorizationMonoid (Algebra.adjoin ℤ (Set.range (chartGen x e l))) :=
    (chartGen_indep x e hfree l).aevalEquiv.toMulEquiv.uniqueFactorizationMonoid inferInstance
  exact UniqueFactorizationMonoid.instIsIntegrallyClosed
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
