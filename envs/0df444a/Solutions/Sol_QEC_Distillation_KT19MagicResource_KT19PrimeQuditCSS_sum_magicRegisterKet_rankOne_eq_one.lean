-- Prove2me | solution 1 for QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS.sum_magicRegisterKet_rankOne_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T10:57:49.082569+00:00
-- url     : https://prove2.me/submissions/af1e5d3e-20d3-408e-b7df-db7cb2f7c3cf

import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_MagicResource
import Theorems.Thm_QEC_Distillation_KT19MagicResource_KT19PrimeQuditCSS_sum_characterKet_rankOne_eq_one
import Theorems.Thm_QEC_Distillation_KT19MagicResource_KT19PrimeQuditCSS_physicalU13_characterKet
import Theorems.Thm_QEC_Semantics_QuditSubsystem_conjOperator_rankOne


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
    (∑ e : PrimeQuditRegisterLabel p Site,
        (InnerProductSpace.rankOne ℂ (magicRegisterKet p e)
          (magicRegisterKet p e)).toLinearMap) = 1 := by
  calc
    (∑ e : PrimeQuditRegisterLabel p Site,
        (InnerProductSpace.rankOne ℂ (magicRegisterKet p e)
          (magicRegisterKet p e)).toLinearMap) =
        ∑ e : PrimeQuditRegisterLabel p Site,
          (physicalU13 p).conjOperator
            (InnerProductSpace.rankOne ℂ (characterKet p e)
              (characterKet p e)).toLinearMap := by
      apply Finset.sum_congr rfl
      intro e _
      rw [QuditSubsystem.conjOperator_rankOne, physicalU13_characterKet]
    _ = (physicalU13 p).conjOperator
        (∑ e : PrimeQuditRegisterLabel p Site,
          (InnerProductSpace.rankOne ℂ (characterKet p e)
            (characterKet p e)).toLinearMap) := by
      rw [← (physicalU13 p).conjOperatorLinearMap_apply, map_sum]
      rfl
    _ = 1 := by
      rw [sum_characterKet_rankOne_eq_one, (physicalU13 p).conjOperator_one]
end QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS
