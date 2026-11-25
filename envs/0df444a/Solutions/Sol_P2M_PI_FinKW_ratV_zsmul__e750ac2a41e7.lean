-- Prove2me | solution 1 for P2M_PI_FinKW_ratV_zsmul__e750ac2a41e7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:44:42.944676+00:00
-- url     : https://prove2.me/submissions/787af60b-7523-40ab-b331-9cb98567e9da

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_MemLocFrom
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocFrom
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
open PI PI.FinKW
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst)
namespace PI.FinKW
theorem _root_.solution {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    {n : ℕ} (k : ℤ) (a : Fin n → E) :
    Formalism.L2.SG.Sub.ratV (F := F) R (k • a) = k • Formalism.L2.SG.Sub.ratV (F := F) R a := by
  funext i
  simp [Formalism.L2.SG.Sub.ratV]
end PI.FinKW
