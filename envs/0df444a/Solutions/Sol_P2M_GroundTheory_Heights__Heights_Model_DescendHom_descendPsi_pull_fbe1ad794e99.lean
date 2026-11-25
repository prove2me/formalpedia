-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_DescendHom_descendPsi_pull_fbe1ad794e99
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:10:21.896621+00:00
-- url     : https://prove2.me/submissions/c12e8458-7831-4c10-8e1d-e51b74761007

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsDescendHom
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PClearDenominators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PDescendHom
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_DescendHom_pullSectionOn_openImmersion_0ea89070b545

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
variable {T Y Z : Scheme.{0}} (ι : Z ⟶ Y) [IsOpenImmersion ι] (g' : T ⟶ Z) {F G : Y.Modules}
  (φ : (Scheme.Modules.pullback (g' ≫ ι)).obj F ⟶ (Scheme.Modules.pullback (g' ≫ ι)).obj G)
  (hinj : ∀ V : Y.Opens, V ≤ ι.opensRange → Function.Injective (pullSectionOn (g' ≫ ι) G V))
  (t : ∀ V : Y.Opens, V ≤ ι.opensRange → Γ(F, V) → Γ(G, V))
  (ht : ∀ (V : Y.Opens) (hV : V ≤ ι.opensRange) (s : Γ(F, V)),
    pullSectionOn (g' ≫ ι) G V (t V hV s) =
      φ.app ((g' ≫ ι) ⁻¹ᵁ V) (pullSectionOn (g' ≫ ι) F V s))
include hinj ht
namespace GroundTheory.Heights₂.Heights.Model.DescendHom
theorem _root_.solution (V : Y.Opens) (hV : V ≤ ι.opensRange) (s : Γ(F, V)) :
    (descendPsi ι g' φ hinj t ht).app (ι ⁻¹ᵁ V) (pullSectionOn ι F V s) =
      pullSectionOn ι G V (t V hV s) := by
  rw [pullSectionOn_openImmersion ι F, pullSectionOn_openImmersion ι G, descendPsi,
    ← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id_app_assoc,
    Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  congr 1
  exact t_res ι g' φ hinj t ht hV (ι.image_preimage_le V) s
end GroundTheory.Heights₂.Heights.Model.DescendHom
