-- Prove2me | solution 1 for PI.DvRows.linInd_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:04.774989+00:00
-- url     : https://prove2.me/submissions/36bbae11-fb64-4570-9c9d-242b422547f2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_AsmBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_AsmDual
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
open PI PI.DvRows
open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv Formalism.LFunctionChainParameters.LLcv
namespace PI.DvRows
theorem _root_.solution {K V : Type} [Field K] [AddCommGroup V] [Module K V] {k d : ℕ} (u : Fin k → V)
    (z : Fin d → V) (h : LinearIndependent K (Fin.append u z)) : LinearIndependent K u := by
  have : u = Fin.append u z ∘ Fin.castAdd d := by funext i; simp
  rw [this]
  exact h.comp _ (Fin.castAdd_injective k d)
end PI.DvRows
