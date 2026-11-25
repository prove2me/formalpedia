-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.SCPf.prod_perm_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:44:18.594897+00:00
-- url     : https://prove2.me/submissions/84401f7a-c1dc-4af7-9c48-9b3a99e5dcd2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GermSC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantTheorems_WickFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LiftXHasSubst

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
variable {ι : Type} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.TB.SCPf
theorem _root_.solution {A : Type} [Monoid A] {L L' : List A} (hp : L.Perm L')
    (hc : ∀ x ∈ L, ∀ y ∈ L, Commute x y) : L.prod = L'.prod := hp.prod_eq' (List.pairwise_of_forall_mem_list hc)
end ReciprocityTheory.ChartRestriction.G.TB.SCPf
