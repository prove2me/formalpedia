-- Prove2me | solution 1 for PositivityTheory.PrwZar.QiP.pt_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:22:26.372804+00:00
-- url     : https://prove2.me/submissions/50b9dc0f-acf8-48eb-8cd2-08743d94321c

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_CommutativeAlgebra_IsFinFlatSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasChartsOfForallIsAffineOpen
import Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_ZarhinTrick_QiPtsA
import Theorems.Thm_GlobalTheory_NatFun_HasCharts_mono


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
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open GlobalTheory.CompanionTheory.Ar.GR
open PositivityTheory PositivityTheory.PrwZar PositivityTheory.PrwZar.QiP
variable {R : Type} [CommRing R] {F : Type} [CommRing F] [Algebra R F]
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {h : sp (R₀ := R) F ⟶ G}
namespace PositivityTheory.PrwZar.QiP
theorem _root_.solution (hs : IsFinFlatSub G F h) {S : Type} [CommRing S] [Algebra R S] {φ φ' : F →ₐ[R] S}
    (e : spMap φ ≫ h = spMap φ' ≫ h) : φ = φ' :=
  hs.mono S φ φ' e
end PositivityTheory.PrwZar.QiP
