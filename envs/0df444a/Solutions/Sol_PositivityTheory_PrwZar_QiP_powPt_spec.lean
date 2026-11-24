-- Prove2me | solution 1 for PositivityTheory.PrwZar.QiP.powPt_spec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:09:59.166273+00:00
-- url     : https://prove2.me/submissions/8541b1bb-d96e-41c0-929e-99fcc8a57024

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_CommutativeAlgebra_IsFinFlatSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasChartsOfForallIsAffineOpen
import Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_ZarhinTrick_QiPtsA
import Theorems.Thm_PositivityTheory_PrwZar_QiP_mulPt_spec
import Theorems.Thm_PositivityTheory_PrwZar_QiP_onePt_spec

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
theorem _root_.solution (hs : IsFinFlatSub G F h) {S : Type} [CommRing S] [Algebra R S] (φ : F →ₐ[R] S) (n : ℕ) :
    spMap (powPt hs φ n) ≫ h = (spMap φ ≫ h) ^ n := by
  induction n with
  | zero => rw [pow_zero]; exact onePt_spec hs S
  | succ n ih => rw [pow_succ, ← ih]; exact mulPt_spec hs _ _
end PositivityTheory.PrwZar.QiP
