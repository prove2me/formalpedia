-- Prove2me | solution 1 for QEC.Distillation.Why24OneRoundProtocol.f1024Why24OddAGDualDecoder_alwaysReturns
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:47:43.284117+00:00
-- url     : https://prove2.me/submissions/56c6694d-59d5-4ed4-bc52-3c91301b2740

import Definitions.Def_QEC_Coding_QuditQubitConversion_ResourceCircuit
import Definitions.Def_QEC_Distillation_Core_FiniteDecodedTrace
import Definitions.Def_QEC_Distillation_Core_FiniteInstrumentBinaryRun
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_MagicResource
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_ConstantOverheadProtocol_AlgebraicGeometryFamily
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Semantics_Instruments_Sequential_Composition
import Definitions.Def_QEC_Semantics_Instruments_Registers_ProductDensity
import Definitions.Def_QEC_Semantics_Instruments_Registers_Marginal
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Channels_Instrument
import Definitions.Def_QEC_Distillation_ConstantOverheadProtocol_OneRound
section
noncomputable section
namespace QEC.Distillation.Why24OneRoundProtocol
open QEC.Coding
open QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
open QEC.Distillation
open QEC.Distillation.Why24AGFamily
open QEC.Distillation.KT19PrimeQuditCSS
open QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS
open QEC.Distillation.Why24WeightedTriorthogonalCSS
open QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix
open QEC.Semantics
open scoped BigOperators ComplexOrder
attribute [local instance]
  QEC.Distillation.KT19PrimeQuditCSS.primeQuditRegisterLabelFintype
attribute [local instance] QEC.Distillation.KT19PrimeQuditCSS.primeQuditRegisterLabelFintype QEC.Distillation.Why24OneRoundProtocol.instWhy24OneRoundClassicalDecidable
namespace Why24CCZFaultOperation
variable {Location : Type} [Fintype Location] [DecidableEq Location]
variable {fault : Finset Location}
end Why24CCZFaultOperation
namespace Why24LocalStochasticPreparation
variable {Location : Type} [Fintype Location] [DecidableEq Location]
variable {ideal : DensityOperator (Why24CCZRegister Location)}
end Why24LocalStochasticPreparation
open QEC.Distillation.OneQubitMagic
attribute [local instance 2000] QEC.Distillation.Why24OneRoundProtocol.why24DecoderDirectConstantAlgebra QEC.Distillation.Why24OneRoundProtocol.why24DecoderDirectConstantScalarTower
private theorem why24DecoderRecoveryRangeSection_rightInverse (r : Nat)
    (syndrome : f1024Why24OddZSyndrome r)
    (value : LinearMap.range (why24DecoderRecoverySyndromeMap r syndrome)) :
    why24DecoderRecoverySyndromeMap r syndrome
        (why24DecoderRecoveryRangeSection r syndrome value) = value.1 := by
  let recovery := why24DecoderRecoverySyndromeMap r syndrome
  letI : Module.Free F1024 (LinearMap.range recovery) :=
    Module.Free.of_divisionRing F1024 (LinearMap.range recovery)
  let basis := Module.finBasis F1024 (LinearMap.range recovery)
  have hcoordinates := LinearMap.leftInverse_splittingOfFunOnFintypeSurjective
    (why24DecoderRecoveryCoordinates r syndrome)
    (why24DecoderRecoveryCoordinates_surjective r syndrome)
    (basis.equivFun value)
  have hrange : recovery.rangeRestrict
      (why24DecoderRecoveryRangeSection r syndrome value) = value := by
    apply basis.equivFun.injective
    exact hcoordinates
  exact congrArg Subtype.val hrange
namespace Why24OneRoundTwirledConversionLaw
variable {r : Nat}
variable {preparation : Why24LocalStochasticPreparation
  (Fin (why24OneRoundInputCount r))
  (why24IdealCCZRegisterDensity (why24OneRoundInputCount r))}
end Why24OneRoundTwirledConversionLaw
end QEC.Distillation.Why24OneRoundProtocol
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Why24OneRoundProtocol
open QEC.Coding
open QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
open QEC.Distillation
open QEC.Distillation.Why24AGFamily
open QEC.Distillation.KT19PrimeQuditCSS
open QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS
open QEC.Distillation.Why24WeightedTriorthogonalCSS
open QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix
open QEC.Semantics
open scoped BigOperators ComplexOrder
attribute [local instance]
  QEC.Distillation.KT19PrimeQuditCSS.primeQuditRegisterLabelFintype
attribute [local instance] QEC.Distillation.Why24OneRoundProtocol.instWhy24OneRoundClassicalDecidable
attribute [local instance] QEC.Distillation.KT19PrimeQuditCSS.primeQuditRegisterLabelFintype QEC.Distillation.Why24OneRoundProtocol.instWhy24OneRoundClassicalDecidable
open QEC.Distillation.OneQubitMagic
attribute [local instance 2000] QEC.Distillation.Why24OneRoundProtocol.why24DecoderDirectConstantAlgebra
attribute [local instance 2000] QEC.Distillation.Why24OneRoundProtocol.why24DecoderDirectConstantScalarTower
attribute [local instance 2000] QEC.Distillation.Why24OneRoundProtocol.why24DecoderDirectConstantAlgebra QEC.Distillation.Why24OneRoundProtocol.why24DecoderDirectConstantScalarTower
namespace QEC.Distillation.Why24OneRoundProtocol
theorem _root_.solution (r : Nat)
    (syndrome : f1024Why24OddZSyndrome r) :
    (∃ recovered : LinearMap.ker
        (why24DecoderLocatorProductLinearMap r
          (why24DecoderLocator r syndrome)),
      f1024Why24OddAGDualDecoder r syndrome = recovered.1 ∧
        f1024Why24OddZSyndromeMap r recovered.1 = syndrome) ∨
      (syndrome ∉ LinearMap.range
        (why24DecoderRecoverySyndromeMap r syndrome) ∧
        f1024Why24OddAGDualDecoder r syndrome = 0) := by
  classical
  by_cases hmem : syndrome ∈
      LinearMap.range (why24DecoderRecoverySyndromeMap r syndrome)
  · left
    let recovered := why24DecoderRecoveryRangeSection r syndrome
      ⟨syndrome, hmem⟩
    refine ⟨recovered, ?_, ?_⟩
    · rw [f1024Why24OddAGDualDecoder, dif_pos hmem]
    · have hright := why24DecoderRecoveryRangeSection_rightInverse r
        syndrome ⟨syndrome, hmem⟩
      exact hright
  · right
    refine ⟨hmem, ?_⟩
    rw [f1024Why24OddAGDualDecoder, dif_neg hmem]
end QEC.Distillation.Why24OneRoundProtocol
