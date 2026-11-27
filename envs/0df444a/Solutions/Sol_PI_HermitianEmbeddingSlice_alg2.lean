-- Prove2me | solution 1 for PI.HermitianEmbeddingSlice.alg2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:24:24.477799+00:00
-- url     : https://prove2.me/submissions/f6396b58-4174-4951-8439-abdb01f166a6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BoundarySlices_WbPartBvecEI
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BoundarySlices_StarSingleOne
import Theorems.Thm_PI_HermitianEmbeddingSlice_Hb_eq
import Theorems.Thm_PI_HermitianEmbeddingSlice_dd_star


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.HermitianEmbeddingSlice
open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic
variable {k r : ℕ}
namespace PI.HermitianEmbeddingSlice
theorem _root_.solution (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (zb : Fin (k + 1) → ℂ) (j : Fin (k + 1)) :
    dd k j * star (star zb ⬝ᵥ (Hb k *ᵥ (μ *ᵥ Pi.single j 1))) = ((Hb k * μᴴ * Hb k) *ᵥ zb) j := by
  have h1 : ∀ v : Fin (k + 1) → ℂ, Hb k *ᵥ v = fun i => dd k i * v i :=
    fun v => funext fun i => by rw [Hb_eq, mulVec_diagonal]
  have h2 : μ *ᵥ Pi.single j 1 = fun i => μ i j :=
    funext fun i => by simp [Matrix.mulVec, dotProduct_single]
  rw [← mulVec_mulVec, ← mulVec_mulVec, h2]
  simp only [h1]
  simp only [dotProduct, Matrix.mulVec, conjTranspose_apply, star_sum, Pi.star_apply, star_mul', star_star]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [dd_star]
  ring
end PI.HermitianEmbeddingSlice
