-- Prove2me | solution 1 for QEC.Distillation.KT19PrimeQuditCSS.fiveSiteSingleLogical_implements_inverseLogicalU13
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T10:54:02.464647+00:00
-- url     : https://prove2.me/submissions/0c6181de-d821-4e07-b569-32d933a82d1b

import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS
import Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_fiveSiteSingleLogical_intertwines_encoding

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.KT19PrimeQuditCSS
open Semantics
open scoped BigOperators
universe u
attribute [local instance] QEC.Distillation.KT19PrimeQuditCSS.primeQuditRegisterLabelFintype
attribute [local instance] primeQuditRegisterLabelFintype
namespace QEC.Distillation.KT19PrimeQuditCSS
theorem _root_.solution :
    fiveSiteSingleLogical.encodedCode.ImplementsLogicalGate fiveSiteSingleLogical.physicalU13
      fiveSiteSingleLogical.logicalInverseU13 := by
  intro psi
  exact fiveSiteSingleLogical_intertwines_encoding psi
end QEC.Distillation.KT19PrimeQuditCSS
