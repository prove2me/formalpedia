-- Prove2me | solution 1 for QEC.Distillation.PhaseRetry.targetMissCard_le_certificate_twelve
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:02:07.248822+00:00
-- url     : https://prove2.me/submissions/7fd4b55c-19f5-4d8c-b4ac-847ad882e52f

import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry
import Theorems.Thm_QEC_Distillation_PhaseRetry_traceVisitsTarget_of_positiveBlock_twelve

set_option autoImplicit false
open QEC
open QEC.Distillation
open QEC.Distillation.PhaseRetry
noncomputable section
namespace QEC.Distillation.PhaseRetry
theorem _root_.solution (start target : ZMod 12) (blocks : Nat) :
    @Fintype.card (TargetMissTrace 12 blocks start target)
      (targetMissTraceFintype 12 blocks start target) ≤
      Fintype.card (NoPositiveTrace 12 blocks) := by
  classical
  letI : Fintype (TargetMissTrace 12 blocks start target) :=
    targetMissTraceFintype 12 blocks start target
  let embed : TargetMissTrace 12 blocks start target → NoPositiveTrace 12 blocks :=
    fun missed index =>
      ⟨missed.val index, by
        apply Bool.eq_false_of_not_eq_true
        intro hPositive
        apply missed.property
        apply traceVisitsTarget_of_positiveBlock_twelve start target missed.val index
        simpa [isPositiveBlock] using hPositive⟩
  apply Fintype.card_le_of_injective embed
  intro left right h
  apply Subtype.ext
  have hValues : (fun index => (embed left index).val) =
      (fun index => (embed right index).val) :=
    congrArg (fun certificate : NoPositiveTrace 12 blocks =>
      fun index => (certificate index).val) h
  simpa [embed] using hValues
end QEC.Distillation.PhaseRetry
