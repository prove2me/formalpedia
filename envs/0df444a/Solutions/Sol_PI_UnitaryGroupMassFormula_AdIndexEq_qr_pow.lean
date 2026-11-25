-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.qr_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:36:44.047013+00:00
-- url     : https://prove2.me/submissions/8b88978f-5a52-43db-9733-a6f5a8069d58

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertPowDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ChiEqOneOfClosure
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Reduce
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_CartierFrobeniusFormLocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertPow
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_mul_qr
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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix
open scoped TensorProduct
open Formalism.MainNotions.S
namespace PI.UnitaryGroupMassFormula.AdIndexEq
theorem _root_.solution {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
    (P : Matrix n n R) (hP : P * P = P) (c : R) (m : ℕ) :
    (1 + (c - 1) • P) ^ m = 1 + (c ^ m - 1) • P := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, mul_qr P hP]
    congr 2
    ring
end PI.UnitaryGroupMassFormula.AdIndexEq
