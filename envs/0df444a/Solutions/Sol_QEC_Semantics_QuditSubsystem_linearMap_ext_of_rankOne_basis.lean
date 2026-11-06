-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.linearMap_ext_of_rankOne_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:20:09.796095+00:00
-- url     : https://prove2.me/submissions/3eb4289d-9238-43c9-8283-1db391c24317

import Definitions.Def_QEC_Semantics_Channels_Core
import Mathlib.Analysis.InnerProductSpace.PiL2
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Theorems.Thm_QEC_Semantics_QuditSubsystem_operator_eq_sum_rankOne_basis
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



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}
set_option maxRecDepth 4096
namespace QEC.Semantics.QuditSubsystem
theorem _root_.solution {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    {κ : Type v} [Fintype κ] (b : OrthonormalBasis κ Complex H)
    (Φ Ψ : Operator H →ₗ[Complex] Operator K)
    (h : ∀ i j : κ,
      Φ (InnerProductSpace.rankOne Complex (b i) (b j)).toLinearMap =
        Ψ (InnerProductSpace.rankOne Complex (b i) (b j)).toLinearMap) : Φ = Ψ := by
  apply LinearMap.ext
  intro A
  rw [operator_eq_sum_rankOne_basis H b A]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hExpand :
      (InnerProductSpace.rankOne Complex (A (b i)) (b i)).toLinearMap =
        ∑ j : κ, inner Complex (b j) (A (b i)) •
          (InnerProductSpace.rankOne Complex (b j) (b i)).toLinearMap := by
    ext x
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    change inner Complex (b i) x • A (b i) =
      ∑ j : κ, inner Complex (b j) (A (b i)) • (inner Complex (b i) x • b j)
    calc
      inner Complex (b i) x • A (b i) =
          inner Complex (b i) x •
            ∑ j : κ, inner Complex (b j) (A (b i)) • b j := by
              rw [b.sum_repr']
      _ = ∑ j : κ, inner Complex (b j) (A (b i)) • (inner Complex (b i) x • b j) := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro j _
        simp [smul_smul, mul_comm]
  rw [hExpand, map_sum]
  rw [map_sum]
  simp only [map_smul]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun B : Operator K => inner Complex (b j) (A (b i)) • B) (h j i)
end QEC.Semantics.QuditSubsystem
