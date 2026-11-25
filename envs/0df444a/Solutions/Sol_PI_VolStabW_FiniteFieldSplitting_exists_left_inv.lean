-- Prove2me | solution 1 for PI.VolStabW.FiniteFieldSplitting.exists_left_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:56:59.562785+00:00
-- url     : https://prove2.me/submissions/07efcfc1-f95d-4208-b72b-3f0a62a00112

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFS
import Theorems.Thm_PI_VolStabW_FiniteFieldSplitting_linInd_cols_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open PI.VolStabW.FiniteFieldSplitting
open Matrix
variable {k : Type} [Field k] [Finite k]
namespace PI.VolStabW.FiniteFieldSplitting
theorem _root_.solution {M a : ℕ} (P : Matrix (Fin M) (Fin a) k)
    (hP : LinearIndependent k (cols P)) : ∃ L : Matrix (Fin a) (Fin M) k, L * P = 1 := by
  have hker : LinearMap.ker (Matrix.mulVecLin P) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    exact (linInd_cols_iff P).mp hP v (by simpa using hv)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hker
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have : LinearMap.toMatrix' (g ∘ₗ Matrix.mulVecLin P) = LinearMap.toMatrix' g * P := by
    rw [LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']
  rw [← this, hg, LinearMap.toMatrix'_id]
end PI.VolStabW.FiniteFieldSplitting
