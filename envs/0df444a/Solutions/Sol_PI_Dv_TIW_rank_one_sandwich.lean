-- Prove2me | solution 1 for PI.Dv.TIW.rank_one_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:30.228417+00:00
-- url     : https://prove2.me/submissions/6569be1a-17b7-4d1d-a6df-8506716a5a22

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_TauCentralScalar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_GrpNorm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_DvTransferIdxOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_MemOOfIsIntegral
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
open PI.Dv NumberField
variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
namespace PI.Dv.TIW
theorem _root_.solution (p : Module.End K W) (hp : p * p = p) (h1 : Module.finrank K (LinearMap.range p) = 1)
    (X : Module.End K W) : p * X * p = LinearMap.trace K W (p * X) • p := by
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp h1
  obtain ⟨β, hβ⟩ := hv ⟨p (X v), LinearMap.mem_range_self p _⟩
  have hβ' : p (X v) = β • (v : W) := by
    have := congrArg Subtype.val hβ; simpa using this.symm
  have key : p * X * p = β • p := by
    apply LinearMap.ext; intro w
    obtain ⟨c, hc⟩ := hv ⟨p w, LinearMap.mem_range_self p w⟩
    have hc' : p w = c • (v : W) := by have := congrArg Subtype.val hc; simpa using this.symm
    simp only [Module.End.mul_apply, LinearMap.smul_apply]
    rw [hc', map_smul, map_smul, hβ', smul_comm]
  have htp : LinearMap.trace K W p = 1 := by
    rw [(LinearMap.IsIdempotentElem.isProj_range p hp).trace, h1, Nat.cast_one]
  have htr : LinearMap.trace K W (p * X) = β := by
    have : LinearMap.trace K W (p * X * p) = LinearMap.trace K W (p * X) := by
      rw [LinearMap.trace_mul_comm, ← mul_assoc, hp]
    rw [← this, key, map_smul, htp, smul_eq_mul, mul_one]
  rw [htr, key]
end PI.Dv.TIW
