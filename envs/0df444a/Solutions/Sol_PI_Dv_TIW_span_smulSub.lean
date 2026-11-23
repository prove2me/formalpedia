-- Prove2me | solution 1 for PI.Dv.TIW.span_smulSub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:01:54.714181+00:00
-- url     : https://prove2.me/submissions/95b69ea2-7859-47b3-b5a9-22db82b2e8ae

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_IdxNonnegOfLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_FinsumEqLogNorm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_IdxSmulSubMap
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
theorem _root_.solution (d : K) (hd : d ≠ 0) (L : Submodule (𝓞 K) V) :
    Submodule.span K (smulSub d L : Set V) = Submodule.span K (L : Set V) := by
  rw [smulSub, Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using Submodule.smul_mem _ d hy
  · intro hx
    refine ⟨d⁻¹ • x, Submodule.smul_mem _ _ hx, ?_⟩
    simp [smul_smul, inv_mul_cancel₀ hd]
end PI.Dv.TIW
