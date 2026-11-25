-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualEmbeddingBijective_pairing_single_4a952709d21e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:01:08.573951+00:00
-- url     : https://prove2.me/submissions/bb8e6639-d24c-4c94-968d-9e202375d17a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegreeDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualEmbBijective

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
open NumberField Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.DualEmbeddingBijective
variable {K : Type} [Field K] [NumberField K] {i : ℕ}
namespace GroundTheory.Heights₂.Heights.DualEmbeddingBijective
theorem _root_.solution (w : (K →+* ℂ) × Fin i → ℂ) (j : Fin i) (x : K) :
    pairing w (Pi.single j x) = ∑ σ : K →+* ℂ, w (σ, j) * σ x := by
  classical
  simp only [pairing, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_eq_single j]
  · simp [mul_comm]
  · intro j' _ hj'
    simp [Pi.single_eq_of_ne hj']
  · simp
end GroundTheory.Heights₂.Heights.DualEmbeddingBijective
