-- Prove2me | solution 1 for PI.EagonNorthcottZ.ct_Phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:37:58.084212+00:00
-- url     : https://prove2.me/submissions/63ab102e-bf97-44eb-9356-bc299afd7ad5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_ExactSecondDegreeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_DivisionPartitionTotal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_CardFilterLtInsert

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EagonNorthcottZ
open MvPolynomial PI.EagonNorthcott
namespace PI.EagonNorthcottZ
theorem _root_.solution {D r : ℕ} (b : Fin r → W D) (v : Fin r → S D) (i : Fin D) (J : Finset (Fin D)) :
    ct i (Phi b v) J = ∑ k, inx (v k) * ct i (b k) J := by
  simp only [ct, Phi]
  split_ifs
  · simp
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
end PI.EagonNorthcottZ
