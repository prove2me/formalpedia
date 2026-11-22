-- Prove2me | solution 1 for P2M_ZhangYeung_copyLemma_delta_le_mutualInfo_Y__217277e4688a
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:14:02.552348+00:00
-- url     : https://prove2.me/submissions/cbde7f6f-8727-4e63-8343-ef25451cbb43

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_Delta
public import Definitions.Def_LeanPool_ZhangYeungInequality_Prelude
public import Definitions.Def_LeanPool_ZhangYeungInequality_CopyLemma
public import Theorems.Thm_P2M_ZhangYeung_copyLemma_delta_identity_Y__c9ae01529d93
public import Theorems.Thm_P2M_ZhangYeung_copyLemma_delta_transport_Y_to_Y__4293faf356ee
public import Theorems.Thm_ProbabilityTheory_condMutualInfo_nonneg


set_option autoImplicit true
@[expose] public section
public section
open ZhangYeung
open MeasureTheory ProbabilityTheory
open scoped ZhangYeungPFR
universe u
variable {Ω : Type*} [MeasurableSpace Ω]
  {S₁ S₂ S₃ S₄ : Type*}
  [MeasurableSpace S₁] [MeasurableSpace S₂]
  [MeasurableSpace S₃] [MeasurableSpace S₄]
  [Finite S₁] [Finite S₂] [Finite S₃] [Finite S₄]
  [MeasurableSingletonClass S₁] [MeasurableSingletonClass S₂]
  [MeasurableSingletonClass S₃] [MeasurableSingletonClass S₄]
  {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {Ω' : Type*} [MeasurableSpace Ω']
  {ν : Measure Ω'} [IsProbabilityMeasure ν]
  {X' : Ω' → S₁} {Y' : Ω' → S₂}
  {X₁ : Ω' → S₁} {Y₁ : Ω' → S₂}
  {Z' : Ω' → S₃} {U' : Ω' → S₄}
namespace ZhangYeung
namespace _root_.ZhangYeung
theorem _root_.solution
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (hU : Measurable U)
    (hX' : Measurable X') (hY₁ : Measurable Y₁)
    (hZ' : Measurable Z') (hU' : Measurable U')
    (hFirst : IdentDistrib (fun ω' => (X' ω', Y' ω', Z' ω', U' ω'))
                           (fun ω => (X ω, Y ω, Z ω, U ω)) ν μ)
    (hSecond : IdentDistrib (fun ω' => (X₁ ω', Y₁ ω', Z' ω', U' ω'))
                            (fun ω => (X ω, Y ω, Z ω, U ω)) ν μ)
    (hCond : CondIndepFun (fun ω' => (X' ω', Y' ω'))
                          (fun ω' => (X₁ ω', Y₁ ω'))
                          (fun ω' => (Z' ω', U' ω')) ν) :
    delta Z U X Y μ ≤ I[X' : Y₁; ν] := by
  rw [copyLemma_delta_transport_Y_to_Y₁ hX hY hZ hU hX' hY₁ hZ' hU' hFirst hSecond,
      copyLemma_delta_identity_Y₁ hX' hY₁ hZ' hU' hCond]
  have h1 : 0 ≤ I[X' : Y₁ | Z'; ν] := condMutualInfo_nonneg hX' hY₁
  have h2 : 0 ≤ I[X' : Y₁ | U'; ν] := condMutualInfo_nonneg hX' hY₁
  have h3 : 0 ≤ I[Z' : U' | ⟨X', Y₁⟩; ν] := condMutualInfo_nonneg hZ' hU'
  linarith
end _root_.ZhangYeung
end ZhangYeung
