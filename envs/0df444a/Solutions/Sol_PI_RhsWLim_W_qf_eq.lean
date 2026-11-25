-- Prove2me | solution 1 for PI.RhsWLim.W.qf_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:54:28.389953+00:00
-- url     : https://prove2.me/submissions/0e453044-ca5e-4b2d-81dc-68870c673684

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsTest
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushI

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim PI.RhsWLim.W.MB
variable {k r : ℕ}
namespace PI.RhsWLim.W
theorem _root_.solution (p : (Fin k → ℂ) × ℂ) : (qf k p : ℂ) = star (toW k p) ⬝ᵥ (Hb k *ᵥ toW k p) := by
  unfold qf
  rw [dotProduct]
  simp only [Hb, Matrix.mulVec_diagonal, Pi.star_apply]
  rw [Fin.sum_univ_castSucc]
  have h1 : ∀ i : Fin k, toW k p (Fin.castSucc i) = p.1 i := fun i => by
    unfold toW; rw [dif_pos (by simp)]; rfl
  have h2 : toW k p (Fin.last k) = p.2 := by
    unfold toW; rw [dif_neg (by simp)]
  have hz : ∀ z : ℂ, star z * z = (Complex.normSq z : ℂ) := fun z => by
    rw [Complex.normSq_eq_conj_mul_self]; rfl
  simp only [h1, h2, Fin.castSucc_ne_last, if_false, if_true, one_mul, neg_one_mul, mul_neg, hz]
  push_cast
  ring
end PI.RhsWLim.W
