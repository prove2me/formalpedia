-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_BasisIsoFree_proof_972f509e66a6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:14:21.601607+00:00
-- url     : https://prove2.me/submissions/aed7e5cb-9b81-4117-92ed-75dfdada3df7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsBasisIsoFree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PBasisIsoFree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_basisHom_app_stdSection_7f67ff63214e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_app_map_apply_e9534398254a


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
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
universe u
variable {Y : Scheme.{u}}
namespace GroundTheory.Heights₂.Heights.Model
namespace BasisIsoFree
theorem _root_.solution (h : FreeSheafBasis.Statement.{u}) : BasisIsoFree.Statement.{u} := by
  intro Y M n s hs
  let ψ := basisHom M s
  have key : ∀ V : Y.Opens, (ψ.app V).hom ∘
      (fun r : Fin n → Γ(Y, V) => ∑ i, r i •
        ((freeModule Y n).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom (stdSection Y n i)) =
      (fun r : Fin n → Γ(Y, V) => ∑ i, r i • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom (s i)) := by
    intro V
    funext r
    simp only [Function.comp_apply, map_sum, Scheme.Modules.Hom.app_smul, app_map_apply, ψ,
      basisHom_app_stdSection]
  have hV : ∀ V : Y.Opens, IsIso (ψ.app V) := fun V =>
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ((Function.Bijective.of_comp_iff _ (h Y n V le_top)).mp (by rw [key V]; exact hs V le_top))
  have : IsIso ψ := Scheme.Modules.Hom.isIso_iff_isIso_app.mpr hV
  exact ⟨(asIso ψ).symm⟩
end BasisIsoFree
end GroundTheory.Heights₂.Heights.Model
