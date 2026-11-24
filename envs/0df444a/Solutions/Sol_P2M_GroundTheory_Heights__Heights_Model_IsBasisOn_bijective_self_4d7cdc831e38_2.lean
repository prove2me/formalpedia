-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Heights_Model_IsBasisOn_bijective_self_4d7cdc831e38
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:30:24.113893+00:00
-- url     : https://prove2.me/submissions/fbae7151-9f6a-4b67-82a7-628a2752380f

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
variable {M}
namespace GroundTheory.Heights₂.Heights.Model
namespace IsBasisOn
theorem _root_.solution {U : X.Opens} {n : ℕ} {s : Fin n → Γ(M, U)} (hs : IsBasisOn M U s) :
    Function.Bijective (fun r : Fin n → Γ(X, U) => ∑ i, r i • s i) := by
  have e : ∀ x : Γ(M, U), (M.presheaf.map (homOfLE (le_refl U)).op).hom x = x := by
    intro x
    rw [Subsingleton.elim (homOfLE (le_refl U)) (𝟙 U), op_id, CategoryTheory.Functor.map_id]
    rfl
  simpa only [e] using hs U le_rfl
end IsBasisOn
end GroundTheory.Heights₂.Heights.Model
