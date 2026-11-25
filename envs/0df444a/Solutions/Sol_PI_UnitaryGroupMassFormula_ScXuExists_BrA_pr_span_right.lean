-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.BrA.pr_span_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:22:27.909618+00:00
-- url     : https://prove2.me/submissions/9ec6d2ad-26c8-4a48-85dc-0a6b5a265aa1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LocDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_ValNatCastLtOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_GlueHoldsVar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_LocSplitChiOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_AdelicLatticeToLocalLattices
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_SecondCoordinateVectorMemSpan
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_BrA_prA_add_right
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_BrA_prA_smul_right
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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists PI.UnitaryGroupMassFormula.ScXuExists.BrA
open NumberField IsDedekindDomain Matrix PI.UnitaryGroupMassFormula.AdIndexEq PI.UnitaryGroupMassFormula.ScXuExists
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists
variable {K : Type} [Field K] (O : ValuationSubring K) {n : ℕ} (P : Matrix (Fin n) (Fin n) K)
namespace PI.UnitaryGroupMassFormula.ScXuExists.BrA
theorem _root_.solution {S : Set (Fin n → K)} {β : Fin n → K} (h : ∀ x ∈ S, pr P β x ∈ O) :
    ∀ x ∈ Submodule.span O S, pr P β x ∈ O := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact h y hy
  | zero => simp [pr]
  | add a b _ _ ha hb => rw [prA_add_right]; exact add_mem ha hb
  | smul c a _ ha =>
    have : c • a = (c : K) • a := rfl
    rw [this, prA_smul_right]
    exact mul_mem c.2 ha
end PI.UnitaryGroupMassFormula.ScXuExists.BrA
