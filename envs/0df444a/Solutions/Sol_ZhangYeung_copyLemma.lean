-- Prove2me | solution 1 for ZhangYeung.copyLemma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:55:29.950916+00:00
-- url     : https://prove2.me/submissions/506c8bf2-67f6-4f32-88a9-2fc7ec3ec3a8

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_Delta
public import Definitions.Def_LeanPool_ZhangYeungInequality_Prelude
public import Definitions.Def_LeanPool_ZhangYeungInequality_CopyLemma
public import Theorems.Thm_ProbabilityTheory_IdentDistrib_prodMk
public import Theorems.Thm_ProbabilityTheory_IsUniform_comp
public import Theorems.Thm_ProbabilityTheory_condIndep_copies


set_option autoImplicit true
@[expose] public section
public section
open ZhangYeung
open MeasureTheory ProbabilityTheory
open scoped ZhangYeungPFR
universe u
namespace ZhangYeung
theorem _root_.solution
    {Ω : Type*} [MeasurableSpace Ω]
    {S₁ S₂ S₃ S₄ : Type u}
    [MeasurableSpace S₁] [MeasurableSpace S₂]
    [MeasurableSpace S₃] [MeasurableSpace S₄]
    [Finite S₃] [Finite S₄]
    [MeasurableSingletonClass S₃] [MeasurableSingletonClass S₄]
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ∃ (Ω' : Type u) (_ : MeasurableSpace Ω') (ν : Measure Ω')
        (X' : Ω' → S₁) (Y' : Ω' → S₂)
        (X₁ : Ω' → S₁) (Y₁ : Ω' → S₂)
        (Z' : Ω' → S₃) (U' : Ω' → S₄),
      IsProbabilityMeasure ν ∧
      Measurable X' ∧ Measurable Y' ∧
      Measurable X₁ ∧ Measurable Y₁ ∧
      Measurable Z' ∧ Measurable U' ∧
      IdentDistrib (fun ω' => (X' ω', Y' ω', Z' ω', U' ω'))
                   (fun ω  => (X ω,  Y ω,  Z ω,  U ω)) ν μ ∧
      IdentDistrib (fun ω' => (X₁ ω', Y₁ ω', Z' ω', U' ω'))
                   (fun ω  => (X ω,  Y ω,  Z ω,  U ω)) ν μ ∧
      CondIndepFun (fun ω' => (X' ω', Y' ω'))
                   (fun ω' => (X₁ ω', Y₁ ω'))
                   (fun ω' => (Z' ω', U' ω')) ν := by
  obtain ⟨Ω', mΩ', W₁, W₂, V, ν, hIsProb, hW₁, hW₂, hV, hCond, hIdent₁,
    hIdent₂⟩ :=
    condIndep_copies (⟨X, Y⟩ : Ω → S₁ × S₂) (⟨Z, U⟩ : Ω → S₃ × S₄)
      (hX.prodMk hY) (hZ.prodMk hU) μ
  have hr : Measurable
      (fun p : (S₁ × S₂) × (S₃ × S₄) => (p.1.1, p.1.2, p.2.1, p.2.2)) := by fun_prop
  refine ⟨Ω', mΩ', ν, fun ω => (W₁ ω).1, fun ω => (W₁ ω).2,
      fun ω => (W₂ ω).1, fun ω => (W₂ ω).2,
      fun ω => (V ω).1, fun ω => (V ω).2,
      hIsProb,
      measurable_fst.comp hW₁, measurable_snd.comp hW₁,
      measurable_fst.comp hW₂, measurable_snd.comp hW₂,
      measurable_fst.comp hV, measurable_snd.comp hV,
      hIdent₁.comp hr, hIdent₂.comp hr, hCond⟩
end ZhangYeung
