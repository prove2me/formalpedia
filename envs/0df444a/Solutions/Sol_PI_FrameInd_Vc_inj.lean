-- Prove2me | solution 1 for PI.FrameInd.Vc_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:22:49.136115+00:00
-- url     : https://prove2.me/submissions/612f5667-0e56-4e5c-9ee9-cd9514fd22cc

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_NegBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_FinrankUperpOfDet
import Theorems.Thm_PI_FrameInd_herm_Vc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
noncomputable section
open PI PI.FrameInd
namespace PI.FrameInd
theorem _root_.solution (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r)
    (hdet : (gramM k r z z' g).det ≠ 0) (c : Fin (r + 1) ⊕ Fin (r + 1) → ℂ)
    (hc : Vc k r z z' g *ᵥ c = 0) : c = 0 := by
  have h1 : gramM k r z z' g *ᵥ c = 0 := by
    funext j
    have h2 := herm_Vc k r z z' g c (Pi.single j 1)
    rw [hc] at h2
    simp only [herm, Matrix.mulVec_zero, dotProduct_zero] at h2
    rw [Pi.zero_apply]
    have h3 : star (Pi.single j (1 : ℂ)) ⬝ᵥ (gramM k r z z' g *ᵥ c) = (gramM k r z z' g *ᵥ c) j := by
      simp [dotProduct, Pi.single_apply]
    rw [← h3, ← h2]
  exact Matrix.eq_zero_of_mulVec_eq_zero hdet h1
end PI.FrameInd
