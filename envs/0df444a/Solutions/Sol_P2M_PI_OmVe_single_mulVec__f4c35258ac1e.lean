-- Prove2me | solution 1 for P2M_PI_OmVe_single_mulVec__f4c35258ac1e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:45:00.489803+00:00
-- url     : https://prove2.me/submissions/a34fafcd-e858-4b58-8dc2-1fa3d8bb8eb6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationLocalVolumes_SingleMulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmVe
open PI.VolStabSW Matrix
variable {K : Type} [CommRing K] (σ : K →+* K) {M : ℕ} (J : Matrix (Fin M) (Fin M) K)
namespace PI.OmVe
theorem _root_.solution {a : ℕ} (i₀ : Fin a) (v : Fin a → K) :
    (Matrix.single i₀ i₀ (1 : K)) *ᵥ v = Pi.single i₀ (v i₀) := by
  ext i
  by_cases h : i = i₀
  · subst h
    simp [Matrix.mulVec, dotProduct, Matrix.single_apply]
  · simp [Matrix.mulVec, dotProduct, Matrix.single_apply, h, Ne.symm h]
end PI.OmVe
