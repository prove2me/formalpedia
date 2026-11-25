-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.dual_top_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:10:57.166354+00:00
-- url     : https://prove2.me/submissions/3d71e18d-59a2-4473-82c6-0402278d2ca2

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OpenRowsFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnChartX
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_ExpRowsPf

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows
open AlgebraicGeometry CategoryTheory Opposite NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped MonObj
variable {g : ℕ} {Y : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows
theorem _root_.solution (W : (Spec (CommRingCat.of (DualNumber ℂ))).Opens)
    (hW : IsLocalRing.closedPoint (DualNumber ℂ) ∈ W) : ⊤ ≤ W := by
  intro x _
  have hs : (x : PrimeSpectrum (DualNumber ℂ)) ⤳ IsLocalRing.closedPoint (DualNumber ℂ) := by
    first
    | exact IsLocalRing.specializes_closedPoint _
    | exact (PrimeSpectrum.le_iff_specializes _ _).1
        (IsLocalRing.le_maximalIdeal (x : PrimeSpectrum (DualNumber ℂ)).2.ne_top)
  exact hs.mem_open W.isOpen hW
end ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows
