-- Prove2me | solution 1 for QEC.Distillation.KT19PrimeQuditCSS.fiveSiteSingleLogical_intertwines_encoding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T10:52:46.208963+00:00
-- url     : https://prove2.me/submissions/2bb64433-5ea9-4306-b1c4-4d4f9e09d73c

import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS
import Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_CubicRowFamily_physicalU13_intertwines_encodingLinearMap
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.KT19PrimeQuditCSS
open Semantics
open scoped BigOperators
universe u
attribute [local instance] QEC.Distillation.KT19PrimeQuditCSS.primeQuditRegisterLabelFintype
attribute [local instance] primeQuditRegisterLabelFintype
namespace QEC.Distillation.KT19PrimeQuditCSS
theorem _root_.solution (psi : PrimeQudit 5) :
    fiveSiteSingleLogical.physicalU13 (fiveSiteSingleLogical.encodedCode.encode psi) =
      fiveSiteSingleLogical.encodedCode.encode (fiveSiteSingleLogical.logicalInverseU13 psi) := by
  change physicalU13 5
      (fiveSiteSingleLogical.encodingLinearMap (singleLogicalRegisterEquiv 5 psi)) =
    fiveSiteSingleLogical.encodingLinearMap
      (singleLogicalRegisterEquiv 5
        ((singleLogicalRegisterEquiv 5).symm
          (CubicRowFamily.logicalInverseU13 fiveSiteSingleLogical
            (singleLogicalRegisterEquiv 5 psi))))
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact CubicRowFamily.physicalU13_intertwines_encodingLinearMap fiveSiteSingleLogical
    (singleLogicalRegisterEquiv 5 psi)
end QEC.Distillation.KT19PrimeQuditCSS
