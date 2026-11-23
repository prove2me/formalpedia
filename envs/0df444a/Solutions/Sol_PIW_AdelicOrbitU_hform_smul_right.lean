-- Prove2me | solution 1 for PIW.AdelicOrbitU.hform_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:08:47.635107+00:00
-- url     : https://prove2.me/submissions/4cba6a07-13d3-400a-b75b-478abaaba341

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_UnitChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_HformEntry
import Theorems.Thm_PIW_AdelicOrbitU_hform_eq_dot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelicOrbitU
open Matrix Formalism.UG
variable {S : Type} [CommRing S] (s : S →+* S) {n : ℕ} (J : Matrix (Fin n) (Fin n) S)
namespace PIW.AdelicOrbitU
theorem _root_.solution (a : S) (x y : Fin n → S) :
    hform s J x (a • y) = a * hform s J x y := by
  simp only [hform_eq_dot, dotProduct, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm]
end PIW.AdelicOrbitU
