-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_BlockAdjoinPrime_proof_5bce0e875870
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:38:16.29709+00:00
-- url     : https://prove2.me/submissions/15e643f8-4645-4720-92e7-89c1fc7dc33a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlockAdjoinPrime
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BlockAdjoinPrime_killB_X_of_not_mem_1f46edb8b2e2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BlockAdjoinPrime_sup_eq_comap_c789fdbae33b

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
open GroundTheory.Heights₂.Heights.NumbersDVR.BlockAdjoinPrime
variable {R : Type*} [CommRing R] {K : Type*} {ι : K → Type*}
variable [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.BlockAdjoinPrime
theorem _root_.solution : BlockAdjoinPrime.Statement := by
  intro R _ K _ _ ι Q B hP hQ
  have h := sup_eq_comap (R := R) hQ B
  change (Q ⊔ varIdeal B).IsPrime ∧ ∀ v : Σ k, ι k, v.1 ∉ B → (X v ∈ Q ⊔ varIdeal B ↔ X v ∈ Q)
  rw [h]
  refine ⟨Ideal.IsPrime.comap (killB B) (hK := hP), fun v hv => ?_⟩
  rw [Ideal.mem_comap, killB_X_of_not_mem B hv]
end GroundTheory.Heights₂.Heights.NumbersDVR.BlockAdjoinPrime
