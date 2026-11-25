-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.specMap_comp_appLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:49:30.907642+00:00
-- url     : https://prove2.me/submissions/274f45c6-a0b3-4245-8eb0-5c2c79235574

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetF

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
open AlgebraicGeometry CategoryTheory Opposite Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff
variable {Y : Scheme.{0}}
set_option backward.isDefEq.respectTransparency false
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution {A B : CommRingCat.{0}} (χ : A ⟶ B) (q : Spec A ⟶ Y) (U : Y.Opens)
    (h : ⊤ ≤ (Spec.map χ ≫ q) ⁻¹ᵁ U) (hq : ⊤ ≤ q ⁻¹ᵁ U) :
    (Spec.map χ ≫ q).appLE U ⊤ h ≫ (Scheme.ΓSpecIso B).hom =
      q.appLE U ⊤ hq ≫ (Scheme.ΓSpecIso A).hom ≫ χ := by
  have e0 : (Spec.map χ ≫ q).appLE U ⊤ h = q.app U ≫ (Spec.map χ).appLE (q ⁻¹ᵁ U) ⊤ h := by
    first
    | exact Scheme.Hom.comp_appLE _ _ _ _ _
    | (simp only [Scheme.Hom.appLE, Scheme.comp_app, Category.assoc]; rfl)
    | (simp only [Scheme.Hom.appLE, Scheme.Hom.comp_app, Category.assoc]; rfl)
    | (unfold Scheme.Hom.appLE; simp [Category.assoc])
  rw [e0]
  have e1 : (Spec.map χ).appLE (q ⁻¹ᵁ U) ⊤ h =
      (Spec A).presheaf.map (homOfLE hq).op ≫ (Spec.map χ).app ⊤ := by
    rw [Scheme.Hom.naturality]
    rfl
  rw [e1]
  simp only [Scheme.Hom.appLE, Category.assoc]
  congr 2
  exact Scheme.ΓSpecIso_naturality χ
end ReciprocityTheory.ChartRestriction.G.PullbackSections
