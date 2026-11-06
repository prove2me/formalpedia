-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensor_channel_mapDensity_leftMarginal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:59:40.595737+00:00
-- url     : https://prove2.me/submissions/fd8810bf-4efb-4530-9f13-521dfaeaac41

import Definitions.Def_QEC_Semantics_Instruments_Tensor_MarginalBornMass
import Definitions.Def_QEC_Semantics_Instruments_Tensor_MarginalChannel
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensor_inducedMap_partialTraceLeft
import Theorems.Thm_QEC_Semantics_DensityOperator_ext_toOperator
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
    (I : FiniteInstrument kappa Omega H K)
    (J : FiniteInstrument kappaTwo Xi R S)
    (hI : I.kraus.Complete) (hJ : J.kraus.Complete)
    (rho : DensityOperator (CompositeSystem H R)) :
    DensityOperator.leftMarginal
        (((I.tensor J).kraus.toQuantumChannel
          (I.tensor_complete J hI hJ)).mapDensity rho) =
      (J.kraus.toQuantumChannel hJ).mapDensity
        (DensityOperator.leftMarginal rho) := by
  apply DensityOperator.ext_toOperator
  change FiniteMatrixEntropy.partialTraceLeftRaw K S
      ((I.tensor J).kraus.inducedMap rho.toOperator) =
    J.kraus.inducedMap
      (FiniteMatrixEntropy.partialTraceLeftRaw H R rho.toOperator)
  exact tensor_inducedMap_partialTraceLeft I J hI rho.toOperator
end QEC.Semantics.FiniteInstrument
