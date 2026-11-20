-- Prove2me | solution 1 for QEC.Distillation.Why24OneRoundProtocol.why24OneRoundBinaryLabelEquiv_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:41:41.365659+00:00
-- url     : https://prove2.me/submissions/f3d1897d-c19a-4f99-9ad9-3f64a8040397

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
theorem _root_.solution {Site : Type}
    [Fintype Site] (left right : Why24Word Site) :
    why24OneRoundBinaryLabelEquiv (left + right) =
      why24OneRoundBinaryLabelEquiv left +
        why24OneRoundBinaryLabelEquiv right := by
  funext siteBit
  rcases siteBit with ⟨site, bit⟩
  change f1024SelectedCoordinates ((left + right) site) bit =
    f1024SelectedCoordinates (left site) bit +
      f1024SelectedCoordinates (right site) bit
  rw [Pi.add_apply, map_add, Pi.add_apply]
end QEC.Distillation.Why24OneRoundProtocol
