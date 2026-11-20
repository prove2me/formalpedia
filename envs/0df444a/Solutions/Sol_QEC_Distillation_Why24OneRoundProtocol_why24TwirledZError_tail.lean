-- Prove2me | solution 1 for QEC.Distillation.Why24OneRoundProtocol.why24TwirledZError_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:56:33.698108+00:00
-- url     : https://prove2.me/submissions/8167180d-8c4d-4cb0-b463-7950d836d243

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
import Theorems.Thm_QEC_Distillation_Why24OneRoundProtocol_Why24LocalStochasticPreparation_why24LocalStochastic_tail_maxRate

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
namespace QEC.Distillation.Why24OneRoundProtocol
theorem _root_.solution {count : Nat}
    (preparation : Why24LocalStochasticPreparation (Fin count)
      (why24IdealCCZRegisterDensity count)) (sites : Finset (Fin count)) :
    (∑ fault : Finset (Fin count),
      if sites ⊆ fault then
        why24TwirledZErrorFaultDistribution preparation fault else 0) ≤
      preparation.rate ^ sites.card :=
  preparation.why24LocalStochastic_tail_maxRate sites
end QEC.Distillation.Why24OneRoundProtocol
