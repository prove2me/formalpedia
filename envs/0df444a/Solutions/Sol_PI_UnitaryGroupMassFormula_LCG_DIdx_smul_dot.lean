-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.DIdx.smul_dot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:41:46.069423+00:00
-- url     : https://prove2.me/submissions/606f265b-ff11-4501-8908-c005fc81f25d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexDual
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
open NumberField Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
open PI.UnitaryGroupMassFormula.LCG.DIdx
namespace PI.UnitaryGroupMassFormula.LCG.DIdx
theorem _root_.solution {K : Type} [Field K] [NumberField K] {k : ℕ} (c : 𝓞 K) (x t : Fin k → K) :
    (c • x) ⬝ᵥ t = algebraMap (𝓞 K) K c * (x ⬝ᵥ t) := by
  simp only [dotProduct, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring
end PI.UnitaryGroupMassFormula.LCG.DIdx
