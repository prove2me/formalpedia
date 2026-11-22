-- Prove2me | solution 1 for P2M_ZhangYeung_copyLemma_delta_identity_X_X__d1ae47cd13b8
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:12:42.701799+00:00
-- url     : https://prove2.me/submissions/45afefb0-17f0-415f-8608-9c61e385e8fc

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_Delta
public import Definitions.Def_LeanPool_ZhangYeungInequality_Prelude
public import Definitions.Def_LeanPool_ZhangYeungInequality_CopyLemma
public import Theorems.Thm_ZhangYeung_delta_of_condMI_vanishes_eq
public import Theorems.Thm_ProbabilityTheory_condMutualInfo_eq_zero
public import Theorems.Thm_ZhangYeung_condIndepFun_comp

section
@[expose] public section
namespace ZhangYeung
open MeasureTheory ProbabilityTheory
open scoped ZhangYeungPFR
universe u
section Consequences
section TripleIdentDistribs
variable {Ω : Type*} [MeasurableSpace Ω]
  {S₁ S₂ S₃ S₄ : Type*}
  [MeasurableSpace S₁] [MeasurableSpace S₂]
  [MeasurableSpace S₃] [MeasurableSpace S₄]
  {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
  {μ : Measure Ω}
  {Ω' : Type*} [MeasurableSpace Ω']
  {ν : Measure Ω'}
  {X' : Ω' → S₁} {Y' : Ω' → S₂}
  {X₁ : Ω' → S₁} {Y₁ : Ω' → S₂}
  {Z' : Ω' → S₃} {U' : Ω' → S₄}
end TripleIdentDistribs
section Finite
variable {S₁ S₂ S₃ S₄ : Type*}
  [MeasurableSpace S₁] [MeasurableSpace S₂]
  [MeasurableSpace S₃] [MeasurableSpace S₄]
  [Finite S₁] [Finite S₂] [Finite S₃] [Finite S₄]
  [MeasurableSingletonClass S₁] [MeasurableSingletonClass S₂]
  [MeasurableSingletonClass S₃] [MeasurableSingletonClass S₄]
  {Ω' : Type*} [MeasurableSpace Ω']
  {ν : Measure Ω'} [IsProbabilityMeasure ν]
  {X' : Ω' → S₁} {Y' : Ω' → S₂}
  {X₁ : Ω' → S₁} {Y₁ : Ω' → S₂}
  {Z' : Ω' → S₃} {U' : Ω' → S₄}
omit [Finite S₂] [MeasurableSingletonClass S₂] in
/--
`I[X' : X₁ | ⟨Z', U'⟩; ν] = 0`: the symmetric companion to
`copyLemma_condMI_X_Y₁_vanishes` used by
the `X ↔ X₁` variant of Lemma 2. Derived by projecting each measured pair to its first
coordinate.
-/
private lemma copyLemma_condMI_X_X₁_vanishes
    (hX' : Measurable X') (hX₁ : Measurable X₁)
    (hCond : CondIndepFun (fun ω' => (X' ω', Y' ω'))
                          (fun ω' => (X₁ ω', Y₁ ω'))
                          (fun ω' => (Z' ω', U' ω')) ν) :
    I[X' : X₁ | fun ω' => (Z' ω', U' ω'); ν] = 0 :=
  (condMutualInfo_eq_zero hX' hX₁).mpr
    (ZhangYeung.condIndepFun_comp (φ := Prod.fst) (ψ := Prod.fst)
      measurable_fst measurable_fst hCond)
end Finite
section Transport
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
end Transport
end Consequences
end ZhangYeung
end
end

set_option autoImplicit true
@[expose] public section
public section
open ZhangYeung
open MeasureTheory ProbabilityTheory
open scoped ZhangYeungPFR
universe u
variable {S₁ S₂ S₃ S₄ : Type*}
  [MeasurableSpace S₁] [MeasurableSpace S₂]
  [MeasurableSpace S₃] [MeasurableSpace S₄]
  [Finite S₁] [Finite S₂] [Finite S₃] [Finite S₄]
  [MeasurableSingletonClass S₁] [MeasurableSingletonClass S₂]
  [MeasurableSingletonClass S₃] [MeasurableSingletonClass S₄]
  {Ω' : Type*} [MeasurableSpace Ω']
  {ν : Measure Ω'} [IsProbabilityMeasure ν]
  {X' : Ω' → S₁} {Y' : Ω' → S₂}
  {X₁ : Ω' → S₁} {Y₁ : Ω' → S₂}
  {Z' : Ω' → S₃} {U' : Ω' → S₄}
omit [Finite S₂] [MeasurableSingletonClass S₂]
namespace ZhangYeung
namespace _root_.ZhangYeung
theorem _root_.solution
    (hX' : Measurable X') (hX₁ : Measurable X₁) (hZ' : Measurable Z') (hU' : Measurable U')
    (hCond : CondIndepFun (fun ω' => (X' ω', Y' ω'))
                          (fun ω' => (X₁ ω', Y₁ ω'))
                          (fun ω' => (Z' ω', U' ω')) ν) :
    delta Z' U' X' X₁ ν
      = I[X' : X₁; ν] - I[X' : X₁ | Z'; ν] - I[X' : X₁ | U'; ν]
        - I[Z' : U' | ⟨X', X₁⟩; ν] :=
  delta_of_condMI_vanishes_eq hX' hZ' hU' hX₁ ν
    (copyLemma_condMI_X_X₁_vanishes (Y' := Y') (Y₁ := Y₁) hX' hX₁ hCond)
end _root_.ZhangYeung
end ZhangYeung
