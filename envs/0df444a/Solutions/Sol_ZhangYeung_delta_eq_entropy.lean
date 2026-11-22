-- Prove2me | solution 1 for ZhangYeung.delta_eq_entropy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:09:39.4758+00:00
-- url     : https://prove2.me/submissions/07a055b4-8301-4444-9b3a-ec4a1498e406

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_Delta
public import Theorems.Thm_ZhangYeung_delta_def
public import Theorems.Thm_ProbabilityTheory_Kernel_mutualInfo_def
public import Theorems.Thm_ProbabilityTheory_condMutualInfo_eq


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
variable [Finite S₁] [Finite S₂]
  [MeasurableSingletonClass S₁] [MeasurableSingletonClass S₂]
variable [Finite S₃] [Finite S₄]
  [MeasurableSingletonClass S₃] [MeasurableSingletonClass S₄]
namespace ZhangYeung
theorem _root_.solution
    {Z : Ω → S₁} {U : Ω → S₂} {X : Ω → S₃} {Y : Ω → S₄}
    (hZ : Measurable Z) (hU : Measurable U) (hX : Measurable X) (hY : Measurable Y)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    delta Z U X Y μ
      = (H[Z; μ] + H[U; μ] - H[⟨Z, U⟩; μ])
        - (H[Z | X; μ] + H[U | X; μ] - H[⟨Z, U⟩ | X; μ])
        - (H[Z | Y; μ] + H[U | Y; μ] - H[⟨Z, U⟩ | Y; μ]) := by
  rw [delta_def, mutualInfo_def, condMutualInfo_eq hZ hU hX, condMutualInfo_eq hZ hU hY]
end ZhangYeung
