-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_isHomogeneous_multiset_prod_map_31e7246876ba
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:42:31.770476+00:00
-- url     : https://prove2.me/submissions/89dd4d8d-6f42-4fff-b163-7aa7a68cfcf7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependenceAlgebra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependence

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {σ : Type*} (φ : ℕ → MvPolynomial σ ℤ)
    (hφ : ∀ b, (φ b).IsHomogeneous b) (t : Multiset ℕ) : ((t.map φ).prod).IsHomogeneous t.sum := by
  induction t using Multiset.induction_on with
  | empty => simpa using isHomogeneous_one σ ℤ
  | cons a t ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    exact (hφ a).mul ih
end GroundTheory.Heights₂.Heights.NumbersDVR
