-- Prove2me | solution 1 for ZhangYeung.delta_form23_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:55:12.607798+00:00
-- url     : https://prove2.me/submissions/be58dc26-4892-42b6-be6d-d4c17f4c716f

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
theorem _root_.solution
    (Z : Ω → S₁) (U : Ω → S₂) (X : Ω → S₃) (Y : Ω → S₄) (μ : Measure Ω) :
    4 * delta Z U X Y μ
        ≤ 2 * I[X : Y; μ] + I[X : ⟨Z, U⟩; μ] + I[Y : ⟨Z, U⟩; μ]
      ↔ delta Z U X Y μ
          ≤ (1 / 2) * I[X : Y; μ] + (1 / 4) * (I[X : ⟨Z, U⟩; μ] + I[Y : ⟨Z,
            U⟩; μ]) := by
  constructor <;> intro h <;> linarith
end ZhangYeung
