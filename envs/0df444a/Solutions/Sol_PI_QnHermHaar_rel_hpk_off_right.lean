-- Prove2me | solution 1 for PI.QnHermHaar.rel_hpk_off_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:08:42.389051+00:00
-- url     : https://prove2.me/submissions/b27d4f01-c06c-43b4-9c36-97dade8f541f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_Development
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_RestrictedGramHermitianInvolution

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.QnHermHaar
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
namespace PI.QnHermHaar
theorem _root_.solution (k r : ℕ) (p q : Fin (2 * r + k + 1)) (j : ℕ)
    (hp : j ≤ p.val ∧ p.val + j ≤ 2 * r + k) (hq : q.val < j ∨ 2 * r + k < q.val + j) :
    Hpk k r p q = 0 := by
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)
end PI.QnHermHaar
