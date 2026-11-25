-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.v_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:43:30.039534+00:00
-- url     : https://prove2.me/submissions/8f308ad3-003f-4ac2-9fdf-de6a85aceb29

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LinLeg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LinMain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.UnitaryGroupMassFormula.ScXuExists
open Matrix
section Main
variable {K : Type} [Field K] (O : ValuationSubring K)
private theorem valuationSubring_valuation_le_one_of_mem {K : Type} [Field K] (O : ValuationSubring K) {x : K}
    (hx : x ∈ O) : O.valuation x ≤ 1 := by
  first
  | exact (O.valuation_le_one_iff x).mpr hx
  | exact O.valuation_le_one ⟨x, hx⟩
  | exact (ValuationSubring.valuation_le_one_iff O x).2 hx
end Main
end PI.UnitaryGroupMassFormula.ScXuExists
end
end

set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists
open Matrix
variable {K : Type} [Field K] (O : ValuationSubring K)
namespace PI.UnitaryGroupMassFormula.ScXuExists
theorem _root_.solution {g y : K} (hg : O.valuation g < 1) (hy : y ∈ O) : O.valuation (g * y) < 1 := by
  rw [map_mul]
  have h1 : O.valuation y ≤ 1 := valuationSubring_valuation_le_one_of_mem O hy
  calc O.valuation g * O.valuation y ≤ O.valuation g * 1 := by
        first
        | exact mul_le_mul_left' h1 _
        | exact mul_le_mul_of_nonneg_left h1 zero_le'
        | gcongr
    _ = O.valuation g := mul_one _
    _ < 1 := hg
end PI.UnitaryGroupMassFormula.ScXuExists
