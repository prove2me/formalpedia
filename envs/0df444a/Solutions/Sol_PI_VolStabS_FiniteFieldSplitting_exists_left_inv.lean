-- Prove2me | solution 1 for PI.VolStabS.FiniteFieldSplitting.exists_left_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:50:26.587031+00:00
-- url     : https://prove2.me/submissions/df07b6a2-0efe-498e-bd3f-ec1c38d6313e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFS
import Theorems.Thm_PI_VolStabS_FiniteFieldSplitting_linInd_cols_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabS
open PI.VolStabS.FiniteFieldSplitting
open Matrix
variable {k : Type} [Field k] [Finite k]
namespace PI.VolStabS.FiniteFieldSplitting
theorem _root_.solution {M a : ℕ} (P : Matrix (Fin M) (Fin a) k)
    (hP : LinearIndependent k (cols P)) : ∃ L : Matrix (Fin a) (Fin M) k, L * P = 1 := by
  have hker : LinearMap.ker (Matrix.toLin' P) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    rw [Matrix.toLin'_apply] at hv
    exact (linInd_cols_iff P).1 hP v hv
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' P) hker
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have h1 := congrArg LinearMap.toMatrix' hg
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at h1
end PI.VolStabS.FiniteFieldSplitting
