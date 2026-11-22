-- Prove2me | solution 1 for ZhangYeung.zhangYeung_averaged
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:18:07.397349+00:00
-- url     : https://prove2.me/submissions/4fa58c22-dbbc-4296-af99-11403ee5efdd

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_Delta
public import Definitions.Def_LeanPool_ZhangYeungInequality_CopyLemma
public import Definitions.Def_LeanPool_ZhangYeungInequality_Prelude
public import Definitions.Def_LeanPool_ZhangYeungInequality_Theorem3
public import Theorems.Thm_ZhangYeung_zhangYeung
public import Theorems.Thm_ZhangYeung_zhangYeung_dual
public import Theorems.Thm_ZhangYeung_delta_form23_iff
public import Theorems.Thm_ZhangYeung_delta_form23_of_form21_form22


set_option autoImplicit true
@[expose] public section
public section
open ZhangYeung
open MeasureTheory ProbabilityTheory
open scoped ZhangYeungPFR
universe u
variable {Ω : Type*} [MeasurableSpace Ω]
  {S₁ S₂ S₃ S₄ : Type u}
  [MeasurableSpace S₁] [MeasurableSpace S₂]
  [MeasurableSpace S₃] [MeasurableSpace S₄]
  [Finite S₁] [Finite S₂] [Finite S₃] [Finite S₄]
  [MeasurableSingletonClass S₁] [MeasurableSingletonClass S₂]
  [MeasurableSingletonClass S₃] [MeasurableSingletonClass S₄]
namespace ZhangYeung
namespace _root_.ZhangYeung
theorem _root_.solution
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    delta Z U X Y μ
      ≤ (1 / 2) * I[X : Y; μ]
        + (1 / 4) * (I[X : ⟨Z, U⟩; μ] + I[Y : ⟨Z, U⟩; μ]) := by
  have h21 := zhangYeung hX hY hZ hU μ
  have h22 := zhangYeung_dual hX hY hZ hU μ
  have h21' : 2 * delta Z U X Y μ
      ≤ I[X : Y; μ] + I[X : ⟨Z, U⟩; μ]
        + I[Z : U | X; μ] - I[Z : U | Y; μ] := by linarith
  have h22' : 2 * delta Z U X Y μ
      ≤ I[X : Y; μ] + I[Y : ⟨Z, U⟩; μ]
        - I[Z : U | X; μ] + I[Z : U | Y; μ] := by linarith
  exact (delta_form23_iff Z U X Y μ).mp (delta_form23_of_form21_form22 h21' h22')
end _root_.ZhangYeung
end ZhangYeung
