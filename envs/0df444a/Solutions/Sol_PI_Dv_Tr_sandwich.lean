-- Prove2me | solution 1 for PI.Dv.Tr.sandwich
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:35:54.907994+00:00
-- url     : https://prove2.me/submissions/71460041-aa0a-4559-a5b6-5524b611076b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_HarderNarasimhan_FinalCor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_TraceFormulaOfRankDegree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_CharacteristicPolynomialCompatibility
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_NormAtAddLe
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
open PI.Dv Module NumberField
variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
namespace PI.Dv.Tr
theorem _root_.solution (Y : Module.End K W) (hY : Y ≠ 0) :
    ∃ (n : ℕ) (A B : Fin n → Module.End K W), ∑ i, A i * Y * B i = 1 := by
  classical
  obtain ⟨v, hv⟩ : ∃ v, Y v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hY (LinearMap.ext h)
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Module.Dual K W, ψ (Y v) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv ((Module.forall_dual_apply_eq_zero_iff K (Y v)).mp h)
  set φ : Module.Dual K W := (ψ (Y v))⁻¹ • ψ with hφdef
  have hφ : φ (Y v) = 1 := by
    rw [hφdef, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hψ]
  let b := Module.finBasis K W
  refine ⟨Module.finrank K W, fun i => φ.smulRight (b i), fun i => (b.coord i).smulRight v, ?_⟩
  apply b.ext
  intro j
  rw [LinearMap.sum_apply]
  simp only [Module.End.mul_apply, LinearMap.smulRight_apply, Module.Basis.coord_apply,
    Module.Basis.repr_self, map_smul, Module.End.one_apply]
  rw [Finset.sum_eq_single j]
  · simp [hφ]
  · intro i _ hij
    simp [Finsupp.single_apply, Ne.symm hij]
  · simp
end PI.Dv.Tr
