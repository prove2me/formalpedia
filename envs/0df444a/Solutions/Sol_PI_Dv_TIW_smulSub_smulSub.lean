-- Prove2me | solution 1 for PI.Dv.TIW.smulSub_smulSub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:30.445032+00:00
-- url     : https://prove2.me/submissions/cc664782-6f67-4977-b944-50aec3442387

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_IdxNonnegOfLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_FinsumEqLogNorm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_IdxSmulSubMap
import Theorems.Thm_PI_Dv_TIW_mem_smulSub
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
open PI PI.Dv PI.Dv.TIW
open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace PI.Dv.TIW
theorem _root_.solution (d e : K) (L : Submodule (𝓞 K) V) : smulSub d (smulSub e L) = smulSub (d * e) L := by
  ext x
  simp only [mem_smulSub]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩; exact ⟨z, hz, by rw [smul_smul]⟩
  · rintro ⟨z, hz, rfl⟩; exact ⟨e • z, ⟨z, hz, rfl⟩, by rw [smul_smul]⟩
end PI.Dv.TIW
