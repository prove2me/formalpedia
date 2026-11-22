-- Prove2me | solution 1 for ZhangYeung.delta_form23_of_form21_form22
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:55:12.136778+00:00
-- url     : https://prove2.me/submissions/bb698307-135b-4d43-9fcd-77041d2c80ab

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
    {Z : Ω → S₁} {U : Ω → S₂} {X : Ω → S₃} {Y : Ω → S₄} {μ : Measure Ω}
    (h21 : 2 * delta Z U X Y μ
        ≤ mutualInfo X Y μ + mutualInfo X (fun ω => (Z ω, U ω)) μ
          + I[Z : U|X;μ] - I[Z : U|Y;μ])
    (h22 : 2 * delta Z U X Y μ
        ≤ mutualInfo X Y μ + mutualInfo Y (fun ω => (Z ω, U ω)) μ
          - I[Z : U|X;μ] + I[Z : U|Y;μ]) :
    4 * delta Z U X Y μ
      ≤ 2 * mutualInfo X Y μ
        + mutualInfo X (fun ω => (Z ω, U ω)) μ
        + mutualInfo Y (fun ω => (Z ω, U ω)) μ := by
  linarith
end ZhangYeung
