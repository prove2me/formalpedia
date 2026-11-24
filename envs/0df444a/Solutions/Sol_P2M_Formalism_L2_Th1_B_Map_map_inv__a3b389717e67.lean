-- Prove2me | solution 1 for P2M_Formalism_L2_Th1_B_Map_map_inv__a3b389717e67
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:09:41.894319+00:00
-- url     : https://prove2.me/submissions/ba2c43ea-ed1b-48a2-a919-c8f2d7cfdb2c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_BaseChangeCompatible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.L2.Th1.B.Map
open Formalism.InvariantFactorPaths.G7 (at1 cob)
variable {K K' : Type} [Field K] [CharZero K] [Field K'] [CharZero K'] (j : K →+* K')
private theorem powerSeries_constantCoeff_map' (f : PowerSeries K) :
    PowerSeries.constantCoeff (PowerSeries.map j f) = j (PowerSeries.constantCoeff f) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_map]
end Formalism.L2.Th1.B.Map
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Map
open Formalism.InvariantFactorPaths.G7 (at1 cob)
variable {K K' : Type} [Field K] [CharZero K] [Field K'] [CharZero K'] (j : K →+* K')
namespace Formalism.L2.Th1.B.Map
theorem _root_.solution {f : PowerSeries K} (hf : PowerSeries.constantCoeff f ≠ 0) :
    PowerSeries.map j f⁻¹ = (PowerSeries.map j f)⁻¹ := by
  have h' : PowerSeries.constantCoeff (PowerSeries.map j f) ≠ 0 := by
    rw [powerSeries_constantCoeff_map']; exact (map_ne_zero j).mpr hf
  rw [PowerSeries.eq_inv_iff_mul_eq_one h', ← map_mul, PowerSeries.inv_mul_cancel _ hf, map_one]
end Formalism.L2.Th1.B.Map
