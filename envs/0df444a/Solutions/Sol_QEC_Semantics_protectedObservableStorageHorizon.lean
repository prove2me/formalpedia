-- Prove2me | solution 1 for QEC.Semantics.protectedObservableStorageHorizon
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:05:36.172316+00:00
-- url     : https://prove2.me/submissions/273bcee9-5d02-40f6-b082-565dc61b9b8e

import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
import Definitions.Def_QEC_Semantics_Dynamics_StorageHorizon
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_traceNorm_density_sub_le
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_clbtProtectedObservableDecay
import Theorems.Thm_QEC_Semantics_finiteLindbladEvolutionLinearMap_zero
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
import Theorems.Thm_QEC_Semantics_traceNorm_neg
import Theorems.Thm_QEC_Semantics_traceNorm_nonneg
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.finiteLindbladEvolutionLinearMap_zero
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.traceNorm_neg



set_option autoImplicit false
noncomputable section
open QEC QEC.Semantics
variable {K : Type}
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteQuantumSystem K]
namespace QEC.Semantics
theorem _root_.solution
    {a : Type} [Nontrivial K] [Fintype a]
    (logical : ThermalEncoding.PauliLikePair K)
    (hamiltonian : Operator K) (hhamiltonian : hamiltonian.IsSymmetric)
    (beta : ℝ) (J : a → Operator K) (P : Operator K)
    (hP : IsStarProjection P)
    (hPx : Commute P logical.x) (hPz : Commute P logical.z)
    (hHx : Commute hamiltonian logical.x)
    (hHz : Commute hamiltonian logical.z)
    (hPH : Commute P hamiltonian)
    (hprotectedX : JumpProtected J logical.x P)
    (hprotectedZ : JumpProtected J logical.z P)
    (hstationary : lindbladDissipator J
      (logical.physicalGibbsState hamiltonian hHz hhamiltonian beta).toOperator = 0) :
    ∃ Enc : QuantumChannel Qubit.QubitSpace K,
      ∃ Dec : QuantumChannel K Qubit.QubitSpace,
        (∀ eta : DensityOperator Qubit.QubitSpace,
          Dec.mapDensity (Enc.mapDensity eta) = eta) ∧
        (∀ (eta : DensityOperator Qubit.QubitSpace) (delta t : ℝ)
            (_hdelta : 0 ≤ delta) (ht : 0 ≤ t),
          8 * t * lindbladDissipatorNorm J *
              clbtGibbsTailMass P
                (logical.physicalGibbsState hamiltonian hHz hhamiltonian beta) ≤
            delta →
          traceNorm
              (((finiteLindbladEvolutionChannel hamiltonian J hhamiltonian t
                    ht)
                  |>.mapDensity (Enc.mapDensity eta)).toOperator -
                (Enc.mapDensity eta).toOperator) ≤ delta ∧
          traceNorm
              ((Dec.mapDensity
                  ((finiteLindbladEvolutionChannel hamiltonian J hhamiltonian t
                      ht)
                    |>.mapDensity (Enc.mapDensity eta))).toOperator -
                eta.toOperator) ≤ delta) ∧
        (lindbladDissipatorNorm J *
              clbtGibbsTailMass P
                (logical.physicalGibbsState hamiltonian hHz hhamiltonian beta) = 0 →
          ∀ (eta : DensityOperator Qubit.QubitSpace) (t : ℝ) (ht : 0 ≤ t),
            traceNorm
                (((finiteLindbladEvolutionChannel hamiltonian J hhamiltonian t ht)
                    |>.mapDensity (Enc.mapDensity eta)).toOperator -
                  (Enc.mapDensity eta).toOperator) = 0 ∧
            traceNorm
                ((Dec.mapDensity
                    ((finiteLindbladEvolutionChannel hamiltonian J hhamiltonian t ht)
                      |>.mapDensity (Enc.mapDensity eta))).toOperator -
                  eta.toOperator) = 0) := by
  rcases clbtProtectedObservableDecay logical hamiltonian hhamiltonian beta J P
      hP hPx hPz hHx hHz hPH hprotectedX hprotectedZ hstationary with
    ⟨Enc, Dec, hleftInverse, hdecay⟩
  have hhorizon :
      ∀ (eta : DensityOperator Qubit.QubitSpace) (delta t : ℝ)
          (_hdelta : 0 ≤ delta) (ht : 0 ≤ t),
        8 * t * lindbladDissipatorNorm J *
            clbtGibbsTailMass P
              (logical.physicalGibbsState hamiltonian hHz hhamiltonian beta) ≤
          delta →
        traceNorm
            (((finiteLindbladEvolutionChannel hamiltonian J hhamiltonian t ht)
                |>.mapDensity (Enc.mapDensity eta)).toOperator -
              (Enc.mapDensity eta).toOperator) ≤ delta ∧
        traceNorm
            ((Dec.mapDensity
                ((finiteLindbladEvolutionChannel hamiltonian J hhamiltonian t ht)
                  |>.mapDensity (Enc.mapDensity eta))).toOperator -
              eta.toOperator) ≤ delta := by
    intro eta delta t _hdelta ht hwindow
    let evolved :=
      (finiteLindbladEvolutionChannel hamiltonian J hhamiltonian t ht).mapDensity
        (Enc.mapDensity eta)
    have hencoded :
        traceNorm (evolved.toOperator - (Enc.mapDensity eta).toOperator) ≤
          delta :=
      (hdecay eta t ht).trans hwindow
    have hdecoded :
        traceNorm
            ((Dec.mapDensity evolved).toOperator - eta.toOperator) ≤ delta := by
      have hcontract :=
        Dec.traceNorm_density_sub_le evolved (Enc.mapDensity eta)
      have hleftOperator :
          Dec (Enc.mapDensity eta).toOperator = eta.toOperator := by
        rw [← QuantumChannel.mapDensity_toOperator]
        exact congrArg DensityOperator.toOperator (hleftInverse eta)
      rw [hleftOperator] at hcontract
      simpa only [QuantumChannel.mapDensity_toOperator] using
        hcontract.trans hencoded
    exact ⟨hencoded, hdecoded⟩
  refine ⟨Enc, Dec, hleftInverse, hhorizon, ?_⟩
  intro hzero eta t ht
  have hwindow :
      8 * t * lindbladDissipatorNorm J *
          clbtGibbsTailMass P
            (logical.physicalGibbsState hamiltonian hHz hhamiltonian beta) ≤
        0 := by
    calc
      8 * t * lindbladDissipatorNorm J *
            clbtGibbsTailMass P
              (logical.physicalGibbsState hamiltonian hHz hhamiltonian beta) =
          8 * t *
            (lindbladDissipatorNorm J *
              clbtGibbsTailMass P
                (logical.physicalGibbsState hamiltonian hHz hhamiltonian beta)) := by
              ring
      _ = 0 := by rw [hzero, mul_zero]
      _ ≤ 0 := le_refl 0
  rcases hhorizon eta 0 t (le_refl 0) ht hwindow with
    ⟨hencoded, hdecoded⟩
  exact ⟨le_antisymm hencoded (traceNorm_nonneg _),
    le_antisymm hdecoded (traceNorm_nonneg _)⟩
end QEC.Semantics
