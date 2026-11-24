-- Prove2me | solution 1 for PI.StabSplit.UnipW.m_perp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:49:50.496284+00:00
-- url     : https://prove2.me/submissions/2cfa971e-d657-45bf-bad3-70747f535563

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_SubFlag
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_NilpotentOrthogonalComplement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 Formalism.QuantumDeterminants.GBasic
noncomputable section
open PI PI.StabSplit PI.StabSplit.UnipW
namespace PI.StabSplit.UnipW
theorem _root_.solution {k r : ℕ} {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hm : Formalism.QuantumDeterminants.WeylGroupFacts.col k r m) {v : Fin (2 * r + k + 1) → ℂ} (hv : perpX k r v) :
    inX k r (m *ᵥ v - v) := by
  intro i hi
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single i (fun j _ hji => ?_) (fun h => absurd (Finset.mem_univ i) h), sub_eq_zero]
  · by_cases hik : i.val ≤ r + k
    · rw [hm i i hik (Or.inr hi), if_pos rfl, one_mul]
    · rw [hv i (by omega), mul_zero]
  · by_cases hjk : j.val ≤ r + k
    · rw [hm i j hjk (Or.inr hi), if_neg (Ne.symm hji), zero_mul]
    · rw [hv j (by omega), mul_zero]
end PI.StabSplit.UnipW
