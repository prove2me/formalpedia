-- Prove2me | solution 1 for QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS.magicRegisterInstrument_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T11:02:11.382053+00:00
-- url     : https://prove2.me/submissions/5c8c3bb3-2cf7-487f-be89-7fd34e695f85

import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_MagicResource
import Theorems.Thm_QEC_Distillation_KT19MagicResource_KT19PrimeQuditCSS_magicRegisterKrausFamily_complete

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.KT19MagicResource
open Semantics
open QEC.Distillation.KT19PrimeQuditCSS
open scoped BigOperators
open QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS
universe u v w
variable (p : Nat) [NeZero p]
variable {Site : Type u} [Fintype Site]
attribute [local instance] QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS._p2m_local_instance_d135975d44_41
attribute [local instance] QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS.primeQuditRegisterLabelFintypeLocal
namespace QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS
theorem _root_.solution :
    (magicRegisterInstrument p (Site := Site)).kraus.Complete :=
  magicRegisterKrausFamily_complete p
end QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS
