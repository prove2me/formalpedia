-- Prove2me | solution 1 for P2M_PositivityTheory_PrwZar_QiP_mulPt_onePt__33bd4a53f6db
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:19:34.790809+00:00
-- url     : https://prove2.me/submissions/5e489c17-a9a6-42a5-a8e4-68a982e64c4a

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_CommutativeAlgebra_IsFinFlatSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasChartsOfForallIsAffineOpen
import Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_ZarhinTrick_QiPtsA
import Theorems.Thm_PositivityTheory_PrwZar_QiP_mulPt_spec
import Theorems.Thm_PositivityTheory_PrwZar_QiP_onePt_spec
import Theorems.Thm_PositivityTheory_PrwZar_QiP_pt_ext

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
theorem _root_.solution (hs : IsFinFlatSub G F h) (φ : F →ₐ[R] S) : mulPt hs φ (onePt hs S) = φ := by
  apply pt_ext hs
  rw [mulPt_spec, onePt_spec, _root_.mul_one]
end PositivityTheory.PrwZar.QiP
