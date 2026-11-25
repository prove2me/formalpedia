-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KAlt_prod_pow_add_single_6c948aa5d4ea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:00:31.441393+00:00
-- url     : https://prove2.me/submissions/2f3206fa-22fd-41fe-862e-45e56389acdf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AltRow

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
open MvPolynomial
open GroundTheory.Heights₂.Heights.KAlt
namespace GroundTheory.Heights₂.Heights.KAlt
theorem _root_.solution {r : ℕ} (q : ℕ) (μ : Fin r → ℕ) (σ : Equiv.Perm (Fin r)) (i : Fin r) :
    ∏ i', (X (σ i') : MvPolynomial (Fin r) ℚ) ^ ((μ + Pi.single i q : Fin r → ℕ) i') =
      X (σ i) ^ q * ∏ i', (X (σ i') : MvPolynomial (Fin r) ℚ) ^ μ i' := by
  simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
  rw [mul_comm]
  congr 1
  rw [Fintype.prod_eq_single i (fun i' hi' => by simp [Pi.single_apply, hi'])]
  simp
end GroundTheory.Heights₂.Heights.KAlt
