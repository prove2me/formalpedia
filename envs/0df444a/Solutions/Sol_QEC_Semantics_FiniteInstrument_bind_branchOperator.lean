-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.bind_branchOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:37:13.559196+00:00
-- url     : https://prove2.me/submissions/3aa5e3d0-1dfd-4fe9-a14f-4e9e96d9ad04

import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Semantics_Instruments_Sequential_Composition
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
universe u v w x y
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder TensorProduct
noncomputable section
open QEC.Semantics.FiniteInstrument
variable {κ : Type v} [Fintype κ]
variable {Ω : Type w} [Fintype Ω]
variable {κ' : Type x} [Fintype κ']
variable {Ξ : Ω → Type y} [∀ outcome, Fintype (Ξ outcome)]
variable {H K L : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution (I : FiniteInstrument κ Ω H K)
    (J : (outcome : Ω) → FiniteInstrument κ' (Ξ outcome) K L)
    (firstOutcome : Ω) (secondOutcome : Ξ firstOutcome) (A : Operator H) :
    (I.bind J).branchOperator ⟨firstOutcome, secondOutcome⟩ A =
      (J firstOutcome).branchOperator secondOutcome
        (I.branchOperator firstOutcome A) := by
  classical
  unfold branchOperator
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro secondIndex _
  by_cases hsecond : (J firstOutcome).observe secondIndex = secondOutcome
  · rw [if_pos hsecond]
    ext vector
    simp only [bind, LinearMap.adjoint_comp, LinearMap.comp_apply,
      LinearMap.sum_apply, map_sum]
    apply Finset.sum_congr rfl
    intro firstIndex _
    by_cases hfirst : I.observe firstIndex = firstOutcome
    · subst firstOutcome
      simp [hsecond, LinearMap.comp_apply]
    · simp [hfirst]
  · rw [if_neg hsecond]
    apply Finset.sum_eq_zero
    intro firstIndex _
    by_cases hfirst : I.observe firstIndex = firstOutcome
    · subst firstOutcome
      have hobserve :
          (I.bind J).observe (firstIndex, secondIndex) ≠
            ⟨I.observe firstIndex, secondOutcome⟩ := by
        intro heq
        change
          (⟨I.observe firstIndex,
              (J (I.observe firstIndex)).observe secondIndex⟩ : Sigma Ξ) =
            ⟨I.observe firstIndex, secondOutcome⟩ at heq
        cases heq
        exact hsecond rfl
      rw [if_neg hobserve]
    · have hcomposite :
          (⟨I.observe firstIndex,
              (J (I.observe firstIndex)).observe secondIndex⟩ : Sigma Ξ) ≠
            ⟨firstOutcome, secondOutcome⟩ := by
        intro heq
        exact hfirst (congrArg Sigma.fst heq)
      have hobserve :
          (I.bind J).observe (firstIndex, secondIndex) ≠
            ⟨firstOutcome, secondOutcome⟩ := by
        simpa only [bind] using hcomposite
      rw [if_neg hobserve]
end QEC.Semantics.FiniteInstrument
