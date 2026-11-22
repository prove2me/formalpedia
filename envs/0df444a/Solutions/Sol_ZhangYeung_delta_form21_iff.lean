-- Prove2me | solution 1 for ZhangYeung.delta_form21_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:00:24.537062+00:00
-- url     : https://prove2.me/submissions/64c73aaa-d5ff-4051-ad9d-f5e85e21e26b

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_Delta
public import Theorems.Thm_ZhangYeung_delta_def

set_option autoImplicit true
@[expose] public section
public section
open ZhangYeung
open MeasureTheory ProbabilityTheory
open scoped ZhangYeungPFR
variable {Ω : Type*} [MeasurableSpace Ω]
  {S₁ S₂ S₃ S₄ : Type*}
  [MeasurableSpace S₁] [MeasurableSpace S₂]
  [MeasurableSpace S₃] [MeasurableSpace S₄]
namespace ZhangYeung
theorem _root_.solution
    (Z : Ω → S₁) (U : Ω → S₂) (X : Ω → S₃) (Y : Ω → S₄) (μ : Measure Ω) :
    2 * delta Z U X Y μ
        ≤ I[X : Y; μ] + I[X : ⟨Z, U⟩; μ] + I[Z : U | X; μ] - I[Z : U | Y; μ]
      ↔ 2 * I[Z : U; μ] - 3 * I[Z : U | X; μ] - I[Z : U | Y; μ]
          ≤ I[X : Y; μ] + I[X : ⟨Z, U⟩; μ] := by
  constructor <;> intro h <;> linarith [delta_def Z U X Y μ]
end ZhangYeung
