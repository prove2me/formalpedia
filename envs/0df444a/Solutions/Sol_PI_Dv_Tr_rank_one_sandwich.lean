-- Prove2me | solution 1 for PI.Dv.Tr.rank_one_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:35:44.040694+00:00
-- url     : https://prove2.me/submissions/e81b172f-0874-4cbf-a89d-77b2b60efb5b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_ESMulESOfNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_CharacteristicPolynomialCompatibility
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_NormAtAddLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_RankIdentity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_PerSAlg
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
open PI PI.Dv PI.Dv.Tr
open PI.Dv Module
variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
namespace PI.Dv.Tr
theorem _root_.solution (p : Module.End K W) (_hp : p * p = p) (h1 : finrank K (LinearMap.range p) = 1)
    (X : Module.End K W) : ∃ c : K, p * X * p = c • p := by
  obtain ⟨w0, hw0r, hw0⟩ : ∃ w0 ∈ LinearMap.range p, w0 ≠ 0 := by
    have : LinearMap.range p ≠ ⊥ := by
      intro h; rw [h, finrank_bot] at h1; exact zero_ne_one h1
    exact Submodule.exists_mem_ne_zero_of_ne_bot this
  have hline : ∀ x ∈ LinearMap.range p, ∃ c : K, x = c • w0 := by
    intro x hx
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨w0, hw0r⟩ : LinearMap.range p)
      (by simpa using hw0)).mp h1 ⟨x, hx⟩
    refine ⟨c, ?_⟩
    have := congrArg Subtype.val hc
    simpa using this.symm
  obtain ⟨c, hc⟩ := hline (p (X w0)) ⟨_, rfl⟩
  refine ⟨c, ?_⟩
  ext w
  obtain ⟨μ, hμ⟩ := hline (p w) ⟨w, rfl⟩
  simp only [Module.End.mul_apply, LinearMap.smul_apply]
  rw [hμ, map_smul, map_smul, hc, smul_smul, smul_smul, mul_comm]
end PI.Dv.Tr
