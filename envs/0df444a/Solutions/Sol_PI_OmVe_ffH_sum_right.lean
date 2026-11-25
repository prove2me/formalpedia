-- Prove2me | solution 1 for PI.OmVe.ffH_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:07:22.143779+00:00
-- url     : https://prove2.me/submissions/66d1a0fc-4737-4905-97c0-898996a1a8bc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationLocalVolumes_SingleMulVec
import Theorems.Thm_PI_OmVe_ffH_add_right
import Theorems.Thm_PI_OmVe_ffH_smul_right
import Theorems.Thm_PI_OmVe_ffH_zero_right

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
theorem _root_.solution {ι : Type} (s : Finset ι) (c : ι → K) (x : Fin M → K) (y : ι → Fin M → K) :
    ffH σ J x (∑ l ∈ s, c l • y l) = ∑ l ∈ s, c l * ffH σ J x (y l) := by
  classical
  refine Finset.induction_on s (by simp [ffH_zero_right]) ?_
  intro l s hl ih
  rw [Finset.sum_insert hl, Finset.sum_insert hl, ffH_add_right, ffH_smul_right, ih]
end PI.OmVe
