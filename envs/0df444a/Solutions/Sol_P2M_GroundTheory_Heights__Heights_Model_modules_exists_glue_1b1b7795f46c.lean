-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_modules_exists_glue_1b1b7795f46c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:53.992512+00:00
-- url     : https://prove2.me/submissions/5b8e1321-9401-402c-a042-da03c344c689

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PullbackBasis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_RatLocalAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PVectorBundleRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PClearDenominators

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
variable {X : Scheme.{0}} (M : X.Modules)
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution {V : X.Opens} {ι : Type} (W : ι → X.Opens) (i : ∀ a, W a ≤ V)
    (hcov : ∀ x ∈ V, ∃ a, x ∈ W a) (sf : ∀ a, Γ(M, W a))
    (hsf : ∀ a b, (M.presheaf.map (homOfLE (inf_le_left : W a ⊓ W b ≤ W a)).op).hom (sf a) =
      (M.presheaf.map (homOfLE (inf_le_right : W a ⊓ W b ≤ W b)).op).hom (sf b)) :
    ∃ s : Γ(M, V), ∀ a, (M.presheaf.map (homOfLE (i a)).op).hom s = sf a := by
  let F : TopCat.Sheaf Ab X := ⟨M.presheaf, M.isSheaf⟩
  obtain ⟨s, hs, -⟩ := F.existsUnique_gluing' W V (fun a => homOfLE (i a))
    (fun x hxV => Opens.mem_iSup.2 (hcov x hxV)) sf hsf
  exact ⟨s, hs⟩
end GroundTheory.Heights₂.Heights.Model
