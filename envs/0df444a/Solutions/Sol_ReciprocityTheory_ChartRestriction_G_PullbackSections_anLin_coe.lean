-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.anLin_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:50:45.841683+00:00
-- url     : https://prove2.me/submissions/2fc42080-1676-4a9a-9d78-747f80a7439f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnHolFamOfHolTo

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
variable {g g' : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution (A : (Fin g' → ℂ) →L[ℂ] (Fin g → ℂ)) (p : Fin 1 × Fin g) :
    ((anLin A p : MvPolynomial (Fin 1 × Fin g') ℂ) : MvPowerSeries (Fin 1 × Fin g') ℂ) =
      ∑ k : Fin g', MvPowerSeries.C (A (Pi.single k 1) p.2) * MvPowerSeries.X ((0 : Fin 1), k) := by
  have h := map_sum (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin 1 × Fin g') (R := ℂ))
    (fun k => MvPolynomial.C (A (Pi.single k 1) p.2) * MvPolynomial.X ((0 : Fin 1), k)) Finset.univ
  unfold anLin
  refine h.trans ?_
  simp
end ReciprocityTheory.ChartRestriction.G.PullbackSections
