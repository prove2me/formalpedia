-- Prove2me | solution 1 for PI.RhsWLim.W.conj_lieOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:19:39.959082+00:00
-- url     : https://prove2.me/submissions/c217bbf8-6aa7-49b4-ae69-9166efd73662

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_Unimod
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_UnimodS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_BallConj

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
open PI.RhsWLim HU
variable {m : ℕ}
namespace PI.RhsWLim.W
theorem _root_.solution {k r : ℕ} (q : Mat k r) (hq : q ∈ UWb k r) (X : Mat k r) (hX : X ∈ lieOf (UWb k r)) :
    q * X * q⁻¹ ∈ lieOf (UWb k r) := by
  intro t
  have hu := uwb_unit hq
  have e : (t : ℂ) • (q * X * q⁻¹) = q * ((t : ℂ) • X) * q⁻¹ := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [e, Matrix.exp_conj _ _ ((Matrix.isUnit_iff_isUnit_det q).2 hu)]
  exact uwb_mul (uwb_mul hq (hX t)) (uwb_inv hq)
end PI.RhsWLim.W
