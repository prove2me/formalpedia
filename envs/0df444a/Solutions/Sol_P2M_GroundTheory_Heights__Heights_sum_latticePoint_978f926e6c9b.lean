-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_sum_latticePoint_978f926e6c9b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:58:17.662747+00:00
-- url     : https://prove2.me/submissions/ca0768c6-f8c0-4dd0-865b-a6e61f184bee

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable {r N : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {φ : Fin (N + 1) → Fin (r + 1) → K} (σ : K →+* ℂ) (w : Fin (r + 1) → ℂ)
    {D : ℤ} {c : Fin (N + 1) → ℤ} {v : Fin (r + 1) → K} (hc : ∑ b, c b • φ b = D • v) :
    ∑ b, (c b : ℂ) * latticePoint φ σ w () b = D * ∑ j, σ (v j) * w j := by
  have h : ∀ j, ∑ b, (c b : K) * φ b j = D * v j := fun j ↦ by
    simpa [Finset.sum_apply, zsmul_eq_mul] using congrFun hc j
  simp only [latticePoint, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have h' := congrArg σ (h j)
  simp only [map_sum, map_mul, map_intCast] at h'
  rw [← mul_assoc, ← h', Finset.sum_mul]
  exact Finset.sum_congr rfl fun b _ ↦ by ring
end GroundTheory.Heights₂.Heights
