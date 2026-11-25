-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_HodgeLow_mk__comp_78527bb5975f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:52:37.393468+00:00
-- url     : https://prove2.me/submissions/795ec355-00d6-43d7-8622-2d9fa098aa89

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PullbackZeroCochainsAlgebraMap
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeLow
variable {R : Type} [CommRing R] {C C' : Type} [Category.{0} C] [Category.{0} C']
  {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R}
namespace GlobalTheory.CompanionTheory.HodgeLow
theorem _root_.solution (G : C' ⥤ C) {T T' T'' : C'} (φ : T ⟶ T') (ψ : T' ⟶ T'') :
    ComposableArrows.mk₂ φ ψ ⋙ G = ComposableArrows.mk₂ (G.map φ) (G.map ψ) :=
  ComposableArrows.ext (fun i ↦ by fin_cases i <;> rfl) (fun i hi ↦ by
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · change G.map φ = 𝟙 _ ≫ G.map φ ≫ 𝟙 _
      simp
    · change G.map ψ = 𝟙 _ ≫ G.map ψ ≫ 𝟙 _
      simp)
end GlobalTheory.CompanionTheory.HodgeLow
