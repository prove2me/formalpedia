-- Prove2me | solution 1 for ZhangYeung.delta_le_mutualInfo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:00:35.120896+00:00
-- url     : https://prove2.me/submissions/38e453ae-5b9f-4adb-aa32-afc01048f29c

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_Delta
public import Theorems.Thm_ZhangYeung_delta_def
public import Theorems.Thm_ProbabilityTheory_condMutualInfo_nonneg


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
namespace ZhangYeung
theorem _root_.solution
    {Z : Ω → S₁} {U : Ω → S₂} (hZ : Measurable Z) (hU : Measurable U)
    {X : Ω → S₃} {Y : Ω → S₄} (μ : Measure Ω) :
    delta Z U X Y μ ≤ I[Z : U; μ] := by
  have h₁ : 0 ≤ I[Z : U | X; μ] := condMutualInfo_nonneg hZ hU
  have h₂ : 0 ≤ I[Z : U | Y; μ] := condMutualInfo_nonneg hZ hU
  rw [delta_def]; linarith
end ZhangYeung
