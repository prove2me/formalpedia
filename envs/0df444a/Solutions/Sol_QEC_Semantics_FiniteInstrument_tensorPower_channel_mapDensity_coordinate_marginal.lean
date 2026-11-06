-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensorPower_channel_mapDensity_coordinate_marginal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:24:49.190443+00:00
-- url     : https://prove2.me/submissions/edb366ac-e4a5-463c-9f86-34dc2b049d02

import Definitions.Def_QEC_Semantics_Instruments_Tensor_MarginalBornMass
import Definitions.Def_QEC_Semantics_Instruments_Tensor_MarginalChannel
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensor_channel_mapDensity_partialTraceRight
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensor_channel_mapDensity_leftMarginal
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPower_complete
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensor_complete


set_option autoImplicit false
universe u v w x y
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators TensorProduct
noncomputable section
open QEC.Semantics.FiniteInstrument
variable {kappa : Type v} [Fintype kappa]
variable {Omega : Type w} [Fintype Omega]
variable {kappaTwo : Type x} [Fintype kappaTwo]
variable {Xi : Type y} [Fintype Xi]
variable {H K R S : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup R] [InnerProductSpace Complex R] [FiniteQuantumSystem R]
variable [NormedAddCommGroup S] [InnerProductSpace Complex S] [FiniteQuantumSystem S]
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution
    (I : FiniteInstrument kappa Omega H K) (hI : I.kraus.Complete) :
    ∀ (attempts : Nat)
      (rho : DensityOperator (tensorPowerCarrier H attempts))
      (trial : Fin attempts),
      tensorPowerInputMarginal attempts
          (((I.tensorPower attempts).kraus.toQuantumChannel
            (I.tensorPower_complete hI attempts)).mapDensity rho) trial =
        (I.kraus.toQuantumChannel hI).mapDensity
          (tensorPowerInputMarginal attempts rho trial) := by
  intro attempts
  induction attempts with
  | zero =>
      intro rho trial
      exact Fin.elim0 trial
  | succ attempts ih =>
      intro rho trial
      refine Fin.cases ?_ ?_ trial
      · exact tensor_channel_mapDensity_partialTraceRight
          I (I.tensorPower attempts) hI
          (I.tensorPower_complete hI attempts) rho
      · intro tailTrial
        change tensorPowerInputMarginal attempts
            (DensityOperator.leftMarginal
              (((I.tensorPower (attempts + 1)).kraus.toQuantumChannel
                (I.tensorPower_complete hI (attempts + 1))).mapDensity rho)) tailTrial =
          (I.kraus.toQuantumChannel hI).mapDensity
            (tensorPowerInputMarginal attempts
              (DensityOperator.leftMarginal rho) tailTrial)
        have hmarginal := tensor_channel_mapDensity_leftMarginal
          I (I.tensorPower attempts) hI
            (I.tensorPower_complete hI attempts) rho
        change DensityOperator.leftMarginal
            (((I.tensor (I.tensorPower attempts)).kraus.toQuantumChannel
              (I.tensor_complete (I.tensorPower attempts) hI
                (I.tensorPower_complete hI attempts))).mapDensity rho) =
          ((I.tensorPower attempts).kraus.toQuantumChannel
            (I.tensorPower_complete hI attempts)).mapDensity
              (DensityOperator.leftMarginal rho) at hmarginal
        change tensorPowerInputMarginal attempts
            (DensityOperator.leftMarginal
              (((I.tensor (I.tensorPower attempts)).kraus.toQuantumChannel
                (I.tensor_complete (I.tensorPower attempts) hI
                  (I.tensorPower_complete hI attempts))).mapDensity rho)) tailTrial =
          (I.kraus.toQuantumChannel hI).mapDensity
            (tensorPowerInputMarginal attempts
              (DensityOperator.leftMarginal rho) tailTrial)
        rw [hmarginal]
        exact ih (DensityOperator.leftMarginal rho) tailTrial
end QEC.Semantics.FiniteInstrument
