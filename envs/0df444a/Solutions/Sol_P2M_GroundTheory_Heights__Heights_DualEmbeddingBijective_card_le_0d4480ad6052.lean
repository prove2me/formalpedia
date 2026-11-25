-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualEmbeddingBijective_card_le_0d4480ad6052
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:01:06.45099+00:00
-- url     : https://prove2.me/submissions/c6ff2865-d34f-466a-a705-b4e57d89ace9

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
theorem _root_.solution (F : HermLattice K i) {T : Type} [Fintype T]
    (b : Module.Basis T ℤ (dualLattice F)) :
    Fintype.card T ≤ Fintype.card ((K →+* ℂ) × Fin i) := by
  have h1 : LinearIndependent ℤ (fun t => (b t : Fin i → K)) :=
    b.linearIndependent.map' (dualLattice F).subtype (Submodule.ker_subtype _)
  have h2 : LinearIndependent ℚ (fun t => (b t : Fin i → K)) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).mp h1
  have h3 := h2.fintype_card_le_finrank
  rw [Module.finrank_pi_fintype] at h3
  rw [Fintype.card_prod, NumberField.Embeddings.card K ℂ, Fintype.card_fin]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h3
  rw [mul_comm]
  exact h3
end GroundTheory.Heights₂.Heights.DualEmbeddingBijective
