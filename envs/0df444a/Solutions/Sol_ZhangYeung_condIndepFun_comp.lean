-- Prove2me | solution 1 for ZhangYeung.condIndepFun_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:52:38.773067+00:00
-- url     : https://prove2.me/submissions/478ccb4f-1dd9-49f8-b839-5c25b35610e3

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_Prelude
public import Theorems.Thm_ProbabilityTheory_IsUniform_comp
public import Theorems.Thm_ProbabilityTheory_condIndepFun_iff


set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory
open scoped ZhangYeungPFR
open ZhangYeung
namespace ZhangYeung
theorem _root_.solution
    {Ω α α' β β' γ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace α']
    [MeasurableSpace β] [MeasurableSpace β'] [MeasurableSpace γ]
    {μ : Measure Ω} {f : Ω → α} {g : Ω → β} {k : Ω → γ}
    {φ : α → α'} {ψ : β → β'}
    (hφ : Measurable φ) (hψ : Measurable ψ) (h : CondIndepFun f g k μ) :
    CondIndepFun (φ ∘ f) (ψ ∘ g) k μ := by
  rw [condIndepFun_iff] at h ⊢
  filter_upwards [h] with z hfg
  exact hfg.comp hφ hψ
end ZhangYeung
