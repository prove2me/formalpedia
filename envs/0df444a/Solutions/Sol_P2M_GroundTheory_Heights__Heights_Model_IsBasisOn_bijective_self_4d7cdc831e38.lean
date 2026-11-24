-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_IsBasisOn_bijective_self_4d7cdc831e38
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T00:27:28.26365+00:00
-- url     : https://prove2.me/submissions/12ab1624-ead8-4bfa-8338-f20dff170974

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


theorem solution {U : X.Opens} {n : ℕ} {s : Fin n → Γ(M, U)} (hs : IsBasisOn M U s) :
    Function.Bijective (fun r : Fin n → Γ(X, U) => ∑ i, r i • s i) := by
  have h := hs U le_rfl
  simpa using h
