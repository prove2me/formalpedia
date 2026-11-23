-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.mk_eq_mk_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:01:34.648774+00:00
-- url     : https://prove2.me/submissions/3ba13201-fe6b-424f-a115-78c1c5779335

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtD
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtE
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_subG_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh Function
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
variable {p K}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution {M : IntermediateField ℚ_[p] (PadicAlgCl p)} (σ τ : GK p K) :
    (QuotientGroup.mk σ : GalLK p K M) = QuotientGroup.mk τ ↔ ∀ x ∈ M, σ x = τ x := by
  rw [QuotientGroup.eq, mem_subG_iff]
  constructor
  · intro h x hx
    have := congrArg σ (h x hx)
    rw [AlgEquiv.mul_apply, ← AlgEquiv.mul_apply, mul_inv_cancel] at this
    exact this.symm
  · intro h x hx
    rw [AlgEquiv.mul_apply, ← h x hx, ← AlgEquiv.mul_apply, inv_mul_cancel]
    rfl
end ReciprocityTheory.DiscreteGroups.LocalClassField
