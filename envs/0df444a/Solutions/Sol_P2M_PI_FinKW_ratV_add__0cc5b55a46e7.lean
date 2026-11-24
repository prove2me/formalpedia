-- Prove2me | solution 1 for P2M_PI_FinKW_ratV_add__0cc5b55a46e7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:35:05.932649+00:00
-- url     : https://prove2.me/submissions/08551f21-4794-44b5-9452-38de30308439

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
    {n : ℕ} (a b : Fin n → E) :
    Formalism.L2.SG.Sub.ratV (F := F) R (a + b) = Formalism.L2.SG.Sub.ratV (F := F) R a + Formalism.L2.SG.Sub.ratV (F := F) R b := by
  funext i
  simp [Formalism.L2.SG.Sub.ratV]
end PI.FinKW
