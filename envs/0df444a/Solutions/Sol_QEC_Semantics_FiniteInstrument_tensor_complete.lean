-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensor_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:42:03.285688+00:00
-- url     : https://prove2.me/submissions/4bcb67a9-0417-40a4-99fd-6c0316e62471

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


section
universe u v w x y
namespace QEC
namespace Semantics
open scoped BigOperators ComplexOrder TensorProduct
noncomputable section
namespace FiniteInstrument
variable {κ : Type v} [Fintype κ]
variable {Ω : Type w} [Fintype Ω]
variable {κ' : Type x} [Fintype κ']
variable {Ξ : Ω → Type y} [∀ outcome, Fintype (Ξ outcome)]
variable {H K L : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]
section Tensor
variable {Ω' : Type y} [Fintype Ω']
variable {R S : Type u}
variable [NormedAddCommGroup R] [InnerProductSpace Complex R] [FiniteQuantumSystem R]
variable [NormedAddCommGroup S] [InnerProductSpace Complex S] [FiniteQuantumSystem S]
private theorem tensorMap_sum_sum (a : κ → Operator H) (b : κ' → Operator R) :
    TensorProduct.map (∑ i, a i) (∑ j, b j) =
      ∑ i, ∑ j, TensorProduct.map (a i) (b j) := by
  classical
  have hleft (s : Finset κ) :
      TensorProduct.map (∑ i ∈ s, a i) (∑ j, b j) =
        ∑ i ∈ s, TensorProduct.map (a i) (∑ j, b j) := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
        simp [Finset.sum_insert hi, TensorProduct.map_add_left, ih]
  have hright (i : κ) (t : Finset κ') :
      TensorProduct.map (a i) (∑ j ∈ t, b j) =
        ∑ j ∈ t, TensorProduct.map (a i) (b j) := by
    induction t using Finset.induction_on with
    | empty => simp
    | insert j t hj ih =>
        simp [Finset.sum_insert hj, TensorProduct.map_add_right, ih]
  calc
    TensorProduct.map (∑ i, a i) (∑ j, b j) =
        ∑ i, TensorProduct.map (a i) (∑ j, b j) := by
          simpa using hleft Finset.univ
    _ = ∑ i, ∑ j, TensorProduct.map (a i) (b j) := by
      apply Finset.sum_congr rfl
      intro i _
      simpa using hright i Finset.univ
end Tensor
section TensorPower
end TensorPower
end FiniteInstrument
end
end Semantics
end QEC
end

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
variable {Ω' : Type y} [Fintype Ω']
variable {R S : Type u}
variable [NormedAddCommGroup R] [InnerProductSpace Complex R] [FiniteQuantumSystem R]
variable [NormedAddCommGroup S] [InnerProductSpace Complex S] [FiniteQuantumSystem S]
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution (I : FiniteInstrument κ Ω H K)
    (J : FiniteInstrument κ' Ω' R S)
    (hI : I.kraus.Complete) (hJ : J.kraus.Complete) :
    (I.tensor J).kraus.Complete := by
  classical
  rw [FiniteKrausFamily.Complete]
  calc
    (∑ index : κ × κ',
        (LinearMap.adjoint ((I.tensor J).kraus.operator index)).comp
          ((I.tensor J).kraus.operator index)) =
        ∑ leftIndex, ∑ rightIndex,
          TensorProduct.map
            ((LinearMap.adjoint (I.kraus.operator leftIndex)).comp
              (I.kraus.operator leftIndex))
            ((LinearMap.adjoint (J.kraus.operator rightIndex)).comp
              (J.kraus.operator rightIndex)) := by
          rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro leftIndex _
          apply Finset.sum_congr rfl
          intro rightIndex _
          simp only [tensor]
          rw [TensorProduct.adjoint_map, ← TensorProduct.map_comp]
    _ = TensorProduct.map
        (∑ leftIndex,
          (LinearMap.adjoint (I.kraus.operator leftIndex)).comp
            (I.kraus.operator leftIndex))
        (∑ rightIndex,
          (LinearMap.adjoint (J.kraus.operator rightIndex)).comp
            (J.kraus.operator rightIndex)) := by
          rw [tensorMap_sum_sum]
    _ = TensorProduct.map (1 : Operator H) (1 : Operator R) := by
          rw [hI, hJ]
    _ = 1 := TensorProduct.map_one
end QEC.Semantics.FiniteInstrument
