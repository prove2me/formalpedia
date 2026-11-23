-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.SCPf.nablaL_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:13:49.488909+00:00
-- url     : https://prove2.me/submissions/d80b9ed0-abe5-4432-8b29-3d03ae63739a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GermSC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantTheorems_WickFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LiftXHasSubst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_nablaL_bracket

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
theorem _root_.solution (hN2 : ConnectionCommutator) (B : FB R d O) (h : PS k 2 d) (m : ℕ) (ξ η : (Fin d → k) × (Fin d → k))
    (hb : betaH k ξ η = 0) : Commute (nablaL B h m ξ.1 ξ.2) (nablaL B h m η.1 η.2) := by
  have hbr := nablaL_bracket hN2 B h m ξ η
  rw [hb, mul_zero, map_zero, sub_eq_zero] at hbr
  exact hbr
end ReciprocityTheory.ChartRestriction.G.TB.SCPf
