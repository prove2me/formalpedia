-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.entropyTerm_sum_le_card_mul_entropyTerm_reciprocal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:28:42.199295+00:00
-- url     : https://prove2.me/submissions/dbe49db1-cc23-4473-acad-77d97cd504bc

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Definitions.Def_QEC_Semantics_Entropy_QuditBounds
import Theorems.Thm_QEC_Semantics_DensityOperator_entropyTerm_concaveOn_nonnegative
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
open QEC.Semantics.DensityOperator
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
namespace QEC.Semantics.DensityOperator
theorem _root_.solution (n : Nat) (hn : 0 < n)
    (p : Fin n -> Real) (hp : forall i, 0 <= p i) (hsum : (∑ i, p i) = 1) :
    (∑ i, entropyTerm (p i)) <= (n : Real) * entropyTerm ((n : Real)⁻¹) := by
  let w : Fin n -> Real := fun _ => (n : Real)⁻¹
  have hweights : (∑ i, w i) = 1 := by
    simp [w, hn.ne']
  have hmean : (∑ i, w i * p i) = (n : Real)⁻¹ := by
    calc
      ∑ i, w i * p i = (n : Real)⁻¹ * ∑ i, p i := by
        simp [w, Finset.mul_sum]
      _ = (n : Real)⁻¹ := by rw [hsum, mul_one]
  have hJensen := entropyTerm_concaveOn_nonnegative.le_map_sum
    (t := Finset.univ) (w := w) (p := p)
    (by intro i _; exact inv_nonneg.mpr (Nat.cast_nonneg n)) hweights
    (by intro i _; exact hp i)
  have hmean_smul : (∑ i, w i • p i) = (n : Real)⁻¹ := by
    simpa [smul_eq_mul] using hmean
  rw [hmean_smul] at hJensen
  calc
    (∑ i, entropyTerm (p i)) =
        (n : Real) * (∑ i, w i * entropyTerm (p i)) := by
      simp [w, Finset.mul_sum, hn.ne']
    _ <= (n : Real) * entropyTerm ((n : Real)⁻¹) := by
      exact mul_le_mul_of_nonneg_left hJensen (Nat.cast_nonneg n)
end QEC.Semantics.DensityOperator
