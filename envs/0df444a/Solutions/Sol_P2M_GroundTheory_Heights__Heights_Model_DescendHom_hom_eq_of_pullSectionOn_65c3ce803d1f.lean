-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_DescendHom_hom_eq_of_pullSectionOn_65c3ce803d1f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:10:24.406803+00:00
-- url     : https://prove2.me/submissions/55665b27-611a-4ba4-9b38-7b2273bf13c4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsDescendHom
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PClearDenominators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PDescendHom
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_DescendHom_res_injective_of_eq_88f22234c1ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_pullSectionOn_res_5fd6dfc3c9f5


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
open GroundTheory.Heights₂.Heights.Model.DescendHom
variable {T Y Z : Scheme.{0}}
namespace GroundTheory.Heights₂.Heights.Model.DescendHom
theorem _root_.solution (g : T ⟶ Y) (R : Y.Opens) (hR : g ⁻¹ᵁ R = ⊤) {F G : Y.Modules}
    (χ₁ χ₂ : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback g).obj G)
    (h : ∀ V : Y.Opens, V ≤ R → ∀ s : Γ(F, V),
      χ₁.app (g ⁻¹ᵁ V) (pullSectionOn g F V s) = χ₂.app (g ⁻¹ᵁ V) (pullSectionOn g F V s)) :
    χ₁ = χ₂ := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).injective
  ext V s
  simp only [Adjunction.homEquiv_unit, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.pushforward_map_app]
  change χ₁.app (g ⁻¹ᵁ V) (pullSectionOn g F V s) = χ₂.app (g ⁻¹ᵁ V) (pullSectionOn g F V s)
  have hE : g ⁻¹ᵁ (V ⊓ R) = g ⁻¹ᵁ V := le_antisymm ((Opens.map g.base).monotone inf_le_left)
    (fun x hx => ⟨hx, by
      have : x ∈ g ⁻¹ᵁ R := by rw [hR]; trivial
      exact this⟩)
  apply res_injective_of_eq _ hE (homOfLE hE.le)
  rw [← hom_app_res, ← hom_app_res]
  rw [← pullSectionOn_res g F (inf_le_left : V ⊓ R ≤ V) (homOfLE hE.le) s]
  exact h _ inf_le_right _
end GroundTheory.Heights₂.Heights.Model.DescendHom
