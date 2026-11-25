-- Prove2me | solution 1 for PI.Dv.Tr.select
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:35:57.921553+00:00
-- url     : https://prove2.me/submissions/718605a2-eb42-4fd9-8b19-e4a1a72c4fd2

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
theorem _root_.solution {ι M : Type} [Fintype ι] [AddCommGroup M] [Module K M] (v : ι → M) (n : ℕ)
    (hn : finrank K (Submodule.span K (Set.range v)) = n) :
    ∃ a : Fin n → ι, LinearIndependent K (v ∘ a) ∧
      Submodule.span K (Set.range (v ∘ a)) = Submodule.span K (Set.range v) := by
  classical
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent'.{0} K v
  have : Finite κ := Finite.of_injective a ha
  have : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = n := by
    rw [← finrank_span_eq_card hli, hsp, hn]
  let e : Fin n ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨a ∘ e, ?_, ?_⟩
  · exact hli.comp e e.injective
  · rw [← hsp]
    congr 1
    ext x
    simp only [Set.mem_range, Function.comp_apply]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨e i, rfl⟩
    · rintro ⟨k, rfl⟩; exact ⟨e.symm k, by simp⟩
end PI.Dv.Tr
