-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.SCPf.side_inl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:13:33.841714+00:00
-- url     : https://prove2.me/submissions/967bbf25-7903-487e-a20d-535a22576943

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GermSC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantTheorems_WickFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LiftXHasSubst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_sideE_symm_inl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.SCPf
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]
namespace ReciprocityTheory.ChartRestriction.G.TB.SCPf
theorem _root_.solution {ι : Type} [Fintype ι] (s : ι → Bool) (i : Fin (Fintype.card {l // s l = true})) :
    s ((sideE s).symm (Sum.inl i)) = true := by
  rw [sideE_symm_inl]
  exact ((Fintype.equivFin {l // s l = true}).symm i).2
end ReciprocityTheory.ChartRestriction.G.TB.SCPf
