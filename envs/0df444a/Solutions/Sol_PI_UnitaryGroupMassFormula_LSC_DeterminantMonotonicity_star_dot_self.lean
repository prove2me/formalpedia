-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LSC.DeterminantMonotonicity.star_dot_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:41:10.042522+00:00
-- url     : https://prove2.me/submissions/d10a5133-238a-47d3-863c-ad26c91fde76

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_LatSizeContOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_HermDefON
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_DetMono
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexOrder
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LSC PI.UnitaryGroupMassFormula.LSC.DeterminantMonotonicity
namespace PI.UnitaryGroupMassFormula.LSC.DeterminantMonotonicity
theorem _root_.solution {n : ℕ} (w : Fin n → ℂ) : star w ⬝ᵥ w = ((nsq w : ℝ) : ℂ) := by
  unfold nsq dotProduct
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.conj_mul']
end PI.UnitaryGroupMassFormula.LSC.DeterminantMonotonicity
