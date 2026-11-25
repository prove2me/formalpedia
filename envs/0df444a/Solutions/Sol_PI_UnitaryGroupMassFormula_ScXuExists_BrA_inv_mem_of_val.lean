-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.BrA.inv_mem_of_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:00:24.27327+00:00
-- url     : https://prove2.me/submissions/f3a55d20-117d-4836-b936-0fef6aeedb29

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_SecondCoordinateVectorMemSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LocalDataSatisfyLinearHypotheses

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists PI.UnitaryGroupMassFormula.ScXuExists.BrA
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix PI.UnitaryGroupMassFormula.AdIndexEq PI.UnitaryGroupMassFormula.ScXuExists
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists
namespace PI.UnitaryGroupMassFormula.ScXuExists.BrA
theorem _root_.solution (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (c : ℕ)
    (hc : Valued.v ((c : v.adicCompletion I.F)) = 1) : ((c : KV I v))⁻¹ ∈ OV I v := by
  have h1 : Valued.v (((c : v.adicCompletion I.F))⁻¹) = 1 := by rw [map_inv₀, hc, inv_one]
  show ((c : v.adicCompletion I.F))⁻¹ ∈ v.adicCompletionIntegers I.F
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).2 h1.le
end PI.UnitaryGroupMassFormula.ScXuExists.BrA
