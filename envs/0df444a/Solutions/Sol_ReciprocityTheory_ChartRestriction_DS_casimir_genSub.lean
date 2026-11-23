-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.casimir_genSub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:20:50.608829+00:00
-- url     : https://prove2.me/submissions/f5e03918-a922-495f-b470-205dc3c56e03

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_casimir_comm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [AddCommGroup M] [Module ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hE : IsGlRep E) {c : ℂ} (hc : ∀ v ∈ V, casimir E v = c • v) :
    ∀ v ∈ genSub E V, casimir E v = c • v := by
  intro v hv
  have hle : genSub E V ≤ LinearMap.ker (casimir E - c • LinearMap.id) := by
    refine sInf_le ⟨fun w hw => ?_, fun a b w hw => ?_⟩
    · rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        hc w hw, sub_self]
    · rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        sub_eq_zero] at hw ⊢
      have h := congrArg (fun f : Module.End ℂ M => f w) (casimir_comm hE a b)
      simp only [Module.End.mul_apply] at h
      rw [h, hw, map_smul]
  have h := hle hv
  rwa [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero] at h
end ReciprocityTheory.ChartRestriction.DS
