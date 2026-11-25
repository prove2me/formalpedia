-- Prove2me | solution 1 for PI.OddDualWeyl.rowOpIntertwining
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:25:15.562861+00:00
-- url     : https://prove2.me/submissions/9adf4a7d-7908-4b4e-9478-a7d3c64c527b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_TransvectionMulApply
import Theorems.Thm_PI_OddDualWeyl_Intw_coeff_comp_neg_X
import Theorems.Thm_PI_OddDualWeyl_Intw_rowGen_det
import Theorems.Thm_PI_OddDualWeyl_Intw_key

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl
open Intw
namespace PI.OddDualWeyl
theorem _root_.solution : W1 := by
  unfold W1
  intro R _ k M a b j f f' hab hrel
  unfold Rel at hrel ⊢
  unfold rowDiv
  have h := congrArg (fun p => Polynomial.coeff p j) (PI.OddDualWeyl.Intw.key a b hab f')
  rw [coeff_comp_neg_X, Polynomial.coeff_map, hrel, map_mul, map_pow,
    PI.OddDualWeyl.Intw.rowGen_det a b hab, ← Polynomial.C_pow, Polynomial.coeff_C_mul] at h
  rw [map_mul, map_pow, map_neg, map_one]
  exact h.symm
end PI.OddDualWeyl
