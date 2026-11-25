-- Prove2me | solution 1 for PI.FrameInd.NegB.negBound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:08:36.735378+00:00
-- url     : https://prove2.me/submissions/45bbbc7f-f998-452a-95e1-5b77465eec01

import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_EqZeroOfNegMap
import Theorems.Thm_PI_FrameInd_NegB_eq_zero_of_negMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic
noncomputable section
open PI PI.FrameInd PI.FrameInd.NegB
namespace PI.FrameInd.NegB
theorem _root_.solution (k r : ℕ) (W : Submodule ℂ (Fin (2 * r + k + 1) → ℂ))
    (hW : ∀ x ∈ W, (herm (Hpk k r) x x).re ≤ 0) : Module.finrank ℂ W ≤ r + 1 := by
  have hinj : Function.Injective ((negMap k r).comp W.subtype) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have h1 : (a : Fin (2 * r + k + 1) → ℂ) = 0 :=
      eq_zero_of_negMap k r a ha (hW a a.2)
    exact Subtype.ext h1
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_fin_fun] at h
  exact h
end PI.FrameInd.NegB
