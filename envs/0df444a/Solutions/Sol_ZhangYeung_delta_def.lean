-- Prove2me | solution 1 for ZhangYeung.delta_def
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:51:58.201049+00:00
-- url     : https://prove2.me/submissions/f4bacb0f-0abd-4ba0-911c-a7e7a50588c2

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_Delta

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
theorem _root_.solution (Z : Ω → S₁) (U : Ω → S₂) (X : Ω → S₃) (Y : Ω
  → S₄) (μ : Measure Ω) :
    delta Z U X Y μ
      = I[Z : U; μ] - I[Z : U | X; μ] - I[Z : U | Y; μ] := rfl
end ZhangYeung
