-- Prove2me | solution 1 for PositivityTheory.PrwZar.QiP.powPt_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:21:04.64088+00:00
-- url     : https://prove2.me/submissions/4ed70090-37d7-4ac6-96c0-786510949acc

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_CommutativeAlgebra_IsFinFlatSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasChartsOfForallIsAffineOpen
import Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_ZarhinTrick_QiPtsA
import Theorems.Thm_PositivityTheory_PrwZar_QiP_pt_ext
import Theorems.Thm_PositivityTheory_PrwZar_QiP_powPt_spec

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
variable {S T : Type} [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]
namespace PositivityTheory.PrwZar.QiP
theorem _root_.solution (hs : IsFinFlatSub G F h) (φ : F →ₐ[R] S) (a b : ℕ) :
    powPt hs φ (a * b) = powPt hs (powPt hs φ a) b := by
  apply pt_ext hs
  rw [powPt_spec, powPt_spec, powPt_spec, pow_mul]
end PositivityTheory.PrwZar.QiP
