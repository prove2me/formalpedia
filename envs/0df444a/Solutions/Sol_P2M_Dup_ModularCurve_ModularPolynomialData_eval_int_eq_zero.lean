-- Prove2me | solution 1 for P2M.Dup.ModularCurve.ModularPolynomialData.eval_int_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/47f2da09-aa7e-5f17-9506-2eb579447afb

import Definitions.Def_ModularCurve_KroneckerTransport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ModularPolynomialData_eval_int_eq_zero

open PowerSeries HahnSeries IntermediateField ModularCurve

theorem solution {N : ℕ} [NeZero N]
    (data : ModularCurve.ModularPolynomialData N) :
    data.Φ.eval₂ ModularCurve.evalAtJInt (ModularCurve.jqIntN N) = 0 := by
  refine laurentMap_injective (f := Int.castRingHom ℚ) Int.cast_injective ?_
  rw [map_zero, Polynomial.hom_eval₂, laurentMap_comp_evalAtJInt, laurentMap_jqIntN]
  exact data.eval_eq_zero

end S_ModularCurve_ModularPolynomialData_eval_int_eq_zero
end P2MW
export P2MW.S_ModularCurve_ModularPolynomialData_eval_int_eq_zero (solution)
