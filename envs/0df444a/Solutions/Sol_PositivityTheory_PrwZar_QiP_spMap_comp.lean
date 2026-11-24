-- Prove2me | solution 1 for PositivityTheory.PrwZar.QiP.spMap_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:19.545036+00:00
-- url     : https://prove2.me/submissions/22062742-86b3-4aaa-8450-ccf4fa4c76de

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_CommutativeAlgebra_IsFinFlatSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasChartsOfForallIsAffineOpen
import Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_ZarhinTrick_QiPtsA
import Theorems.Thm_GlobalTheory_NatFun_familyEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.NatFun.familyEquiv_apply



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
namespace PositivityTheory.PrwZar.QiP
theorem _root_.solution {S T : Type} [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]
    (φ : F →ₐ[R] S) (ψ : S →ₐ[R] T) : spMap ψ ≫ spMap φ = spMap (ψ.comp φ) := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left]
  simp [spMap, ← Spec.map_comp]
  rfl
end PositivityTheory.PrwZar.QiP
