-- Prove2me | solution 1 for PI.StabSplit.FixW.herm_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:54:03.115475+00:00
-- url     : https://prove2.me/submissions/9b4276be-45a6-408e-92df-cadbcacdb369

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_SubFlag
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_FixSub
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_eq


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
open PI PI.StabSplit PI.StabSplit.FixW
namespace PI.StabSplit.FixW
theorem _root_.solution {k r : ℕ} (A C : B.Mat k r) (i j : Fin (2 * r + k + 1)) :
    (Aᴴ * Hpk k r * C) i j = ∑ p, star (A p i) * sgn k r p * C (sig k r p) j := by
  rw [Matrix.mul_apply]
  simp_rw [Matrix.mul_apply, conjTranspose_apply, Hpk_eq, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  simp [mul_ite, ite_mul, Finset.sum_ite_eq']
end PI.StabSplit.FixW
