-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.sum_positive_bornWeight_smul_conditionalDensity_eq_mapDensity_toOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:44:44.747829+00:00
-- url     : https://prove2.me/submissions/676db1de-55cf-442d-bdc8-baca33a53bbe

import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Instruments_Core
import Theorems.Thm_QEC_Semantics_FiniteInstrument_bornWeight_nonneg
import Theorems.Thm_QEC_Semantics_FiniteInstrument_sum_branchOperator_eq_mapDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_branchOperator_eq_zero_of_bornWeight_eq_zero
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_bornWeight_smul_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator

set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
open QEC.Semantics.FiniteInstrument
variable {κ : Type v} [Fintype κ]
variable {Ω : Type w} [Fintype Ω]
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
attribute [local instance] QEC.Semantics.FiniteInstrument._p2m_local_instance_a5f1a79248_39
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution
    (I : FiniteInstrument κ Ω H K) (hComplete : I.kraus.Complete)
    (rho : DensityOperator H) :
    (∑ outcome : {outcome : Ω // 0 < I.bornWeight outcome rho},
        (I.bornWeight outcome.1 rho : Complex) •
          (I.conditionalDensity outcome.1 rho outcome.2).toOperator) =
      ((I.kraus.toQuantumChannel hComplete).mapDensity rho).toOperator := by
  classical
  calc
    (∑ outcome : {outcome : Ω // 0 < I.bornWeight outcome rho},
        (I.bornWeight outcome.1 rho : Complex) •
          (I.conditionalDensity outcome.1 rho outcome.2).toOperator) =
        ∑ outcome : {outcome : Ω // 0 < I.bornWeight outcome rho},
          I.branchOperator outcome.1 rho.toOperator := by
            apply Finset.sum_congr rfl
            intro outcome _houtcome
            exact I.bornWeight_smul_conditionalDensity_toOperator
              outcome.1 rho outcome.2
    _ = ∑ outcome : Ω, I.branchOperator outcome rho.toOperator := by
          let positiveOutcomes : Finset Ω :=
            Finset.univ.filter
              (fun outcome : Ω => 0 < I.bornWeight outcome rho)
          let positiveOutcomeEquiv :
              {outcome : Ω // 0 < I.bornWeight outcome rho} ≃
                positiveOutcomes :=
            Equiv.subtypeEquivProp (by
              funext outcome
              simp [positiveOutcomes])
          have hfiltered :
              (∑ outcome ∈ positiveOutcomes,
                I.branchOperator outcome rho.toOperator) =
                ∑ outcome : Ω, I.branchOperator outcome rho.toOperator := by
            apply Finset.sum_subset (Finset.filter_subset _ _)
            intro outcome _houtcome hnot
            have hnpos : ¬ 0 < I.bornWeight outcome rho := by
              simpa using hnot
            have hzero : I.bornWeight outcome rho = 0 :=
              le_antisymm (not_lt.mp hnpos)
                (I.bornWeight_nonneg outcome rho)
            exact I.branchOperator_eq_zero_of_bornWeight_eq_zero
              outcome rho hzero
          calc
            (∑ outcome : {outcome : Ω //
                0 < I.bornWeight outcome rho},
              I.branchOperator outcome.1 rho.toOperator) =
                ∑ outcome : positiveOutcomes,
                  I.branchOperator outcome.1 rho.toOperator := by
                    exact Fintype.sum_equiv positiveOutcomeEquiv _ _
                      (fun _ => rfl)
            _ = ∑ outcome ∈ positiveOutcomes,
                  I.branchOperator outcome rho.toOperator := by
                    exact Finset.sum_coe_sort positiveOutcomes
                      (fun outcome : Ω =>
                        I.branchOperator outcome rho.toOperator)
            _ = ∑ outcome : Ω,
                  I.branchOperator outcome rho.toOperator :=
                    hfiltered
    _ = ((I.kraus.toQuantumChannel hComplete).mapDensity rho).toOperator :=
      I.sum_branchOperator_eq_mapDensity_toOperator hComplete rho
end QEC.Semantics.FiniteInstrument
