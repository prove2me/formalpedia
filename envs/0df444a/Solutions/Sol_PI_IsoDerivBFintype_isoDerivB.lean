-- Prove2me | solution 1 for PI.IsoDerivBFintype.isoDerivB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:09:50.25614+00:00
-- url     : https://prove2.me/submissions/630ef15a-293c-47af-a639-5e57757429ac

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoDerivB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDerivative_ExistsOePerm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDerivative_ApplyAt0EqSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDerivative_IsoDerivB
import Theorems.Thm_PI_IsoDerivBFintype_polD_eq_aeval
import Theorems.Thm_PI_IsoDerivBFintype_aeval_mY
import Theorems.Thm_PI_IsoDerivBFintype_Q_eq
import Theorems.Thm_PI_IsoDerivBFintype_applyAt0_C_mul
import Theorems.Thm_PI_IsoDerivBFintype_applyAt0_mul_C
import Theorems.Thm_PI_IsoDerivBFintype_applyAt0_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open PI PI.IsoDerivBFintype
open PI.IsoDerivB
namespace PI.IsoDerivBFintype
theorem _root_.solution : IsoDerivB := by
  intro Lt T _ _ _ tp N N' nu s Θ φ Q hQ y'
  rw [polD_eq_aeval, Q_eq tp nu φ Q hQ, map_sum]
  simp only [map_mul, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, aeval_mY]
  rw [applyAt0_sum]
  simp only [applyAt0_C_mul, applyAt0_sum, applyAt0_mul_C]
  unfold canC prC hvC AOp
  rw [finsum_eq_sum_of_fintype]
  simp only [finsum_eq_sum_of_fintype, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
end PI.IsoDerivBFintype
