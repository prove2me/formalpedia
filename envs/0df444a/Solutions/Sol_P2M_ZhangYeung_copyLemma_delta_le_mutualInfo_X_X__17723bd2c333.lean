-- Prove2me | solution 1 for P2M_ZhangYeung_copyLemma_delta_le_mutualInfo_X_X__17723bd2c333
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:14:46.011395+00:00
-- url     : https://prove2.me/submissions/7fd9cd70-dfd0-4d7b-b6fe-532e2f2c795d

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_Delta
public import Definitions.Def_LeanPool_ZhangYeungInequality_Prelude
public import Definitions.Def_LeanPool_ZhangYeungInequality_CopyLemma
public import Theorems.Thm_P2M_ZhangYeung_copyLemma_delta_identity_X_X__d1ae47cd13b8
public import Theorems.Thm_P2M_ZhangYeung_copyLemma_delta_transport_X_to_X__38bc3900b8ed
public import Theorems.Thm_ProbabilityTheory_condMutualInfo_nonneg
public import Theorems.Thm_ZhangYeung_delta_self


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
omit [Finite S₂] [MeasurableSingletonClass S₂]
namespace ZhangYeung
namespace _root_.ZhangYeung
theorem _root_.solution
    (hX : Measurable X) (hZ : Measurable Z) (hU : Measurable U)
    (hX' : Measurable X') (hX₁ : Measurable X₁)
    (hZ' : Measurable Z') (hU' : Measurable U')
    (hFirst : IdentDistrib (fun ω' => (X' ω', Y' ω', Z' ω', U' ω'))
                           (fun ω => (X ω, Y ω, Z ω, U ω)) ν μ)
    (hSecond : IdentDistrib (fun ω' => (X₁ ω', Y₁ ω', Z' ω', U' ω'))
                            (fun ω => (X ω, Y ω, Z ω, U ω)) ν μ)
    (hCond : CondIndepFun (fun ω' => (X' ω', Y' ω'))
                          (fun ω' => (X₁ ω', Y₁ ω'))
                          (fun ω' => (Z' ω', U' ω')) ν) :
    I[Z : U; μ] - 2 * I[Z : U | X; μ] ≤ I[X' : X₁; ν] := by
  rw [← delta_self Z U X μ,
      copyLemma_delta_transport_X_to_X₁ hX hZ hU hX' hX₁ hZ' hU' hFirst hSecond,
      copyLemma_delta_identity_X_X₁ hX' hX₁ hZ' hU' hCond]
  have h1 : 0 ≤ I[X' : X₁ | Z'; ν] := condMutualInfo_nonneg hX' hX₁
  have h2 : 0 ≤ I[X' : X₁ | U'; ν] := condMutualInfo_nonneg hX' hX₁
  have h3 : 0 ≤ I[Z' : U' | ⟨X', X₁⟩; ν] := condMutualInfo_nonneg hZ' hU'
  linarith
end _root_.ZhangYeung
end ZhangYeung
