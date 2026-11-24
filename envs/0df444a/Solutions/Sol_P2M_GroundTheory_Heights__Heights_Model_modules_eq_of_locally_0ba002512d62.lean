-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_modules_eq_of_locally_0ba002512d62
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:04.30109+00:00
-- url     : https://prove2.me/submissions/b9b42d86-58b0-4df2-b763-105fed9497d4

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
theorem _root_.solution {V : X.Opens} (a b : Γ(M, V))
    (h : ∀ x ∈ V, ∃ (W : X.Opens) (i : W ≤ V), x ∈ W ∧
      (M.presheaf.map (homOfLE i).op).hom a = (M.presheaf.map (homOfLE i).op).hom b) : a = b := by
  let F : TopCat.Sheaf Ab X := ⟨M.presheaf, M.isSheaf⟩
  choose W i hx h using h
  refine F.eq_of_locally_eq' (U := fun x : V => W x.1 x.2) V (fun x => homOfLE (i _ _)) ?_ a b
    (fun x => h _ _)
  intro x hxV
  exact Opens.mem_iSup.2 ⟨⟨x, hxV⟩, hx _ _⟩
end GroundTheory.Heights₂.Heights.Model
