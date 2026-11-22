-- Prove2me | solution 1 for P2M_ZhangYeung_copyLemma_delta_transport_Y_to_Y__4293faf356ee
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:11:33.914313+00:00
-- url     : https://prove2.me/submissions/766eecd7-c701-4f99-bfee-030d594c709d

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_Delta
public import Definitions.Def_LeanPool_ZhangYeungInequality_Prelude
public import Definitions.Def_LeanPool_ZhangYeungInequality_CopyLemma
public import Theorems.Thm_ProbabilityTheory_IdentDistrib_mutualInfo_eq
public import Theorems.Thm_ProbabilityTheory_IsUniform_comp
public import Theorems.Thm_ProbabilityTheory_condMutualInfo_eq
public import Theorems.Thm_ZhangYeung_IdentDistrib_condMutualInfo_eq
public import Theorems.Thm_ZhangYeung_delta_def

section
@[expose] public section
namespace ZhangYeung
open MeasureTheory ProbabilityTheory
open scoped ZhangYeungPFR
universe u
section Consequences
private lemma measurable_projZUA {S₁ S₂ S₃ S₄ : Type*}
    [MeasurableSpace S₁] [MeasurableSpace S₂] [MeasurableSpace S₃] [MeasurableSpace S₄] :
    Measurable (projZUA : S₁ × S₂ × S₃ × S₄ → _) := by
  unfold projZUA; fun_prop
private lemma measurable_projZUB {S₁ S₂ S₃ S₄ : Type*}
    [MeasurableSpace S₁] [MeasurableSpace S₂] [MeasurableSpace S₃] [MeasurableSpace S₄] :
    Measurable (projZUB : S₁ × S₂ × S₃ × S₄ → _) := by
  unfold projZUB; fun_prop
private lemma measurable_pairZU {S₁ S₂ S₃ S₄ : Type*}
    [MeasurableSpace S₁] [MeasurableSpace S₂] [MeasurableSpace S₃] [MeasurableSpace S₄] :
    Measurable (fun p : S₁ × S₂ × S₃ × S₄ => (p.2.2.1, p.2.2.2)) := by fun_prop
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
private lemma copyLemma_triple_XFirst
    (hFirst : IdentDistrib
        (fun ω' => (X' ω', Y' ω', Z' ω', U' ω'))
        (fun ω => (X ω, Y ω, Z ω, U ω)) ν μ) :
    IdentDistrib (fun ω => (Z ω, U ω, X ω))
                 (fun ω' => (Z' ω', U' ω', X' ω')) μ ν :=
  hFirst.symm.comp measurable_projZUA
private lemma copyLemma_triple_YSecond
    (hSecond : IdentDistrib
        (fun ω' => (X₁ ω', Y₁ ω', Z' ω', U' ω'))
        (fun ω => (X ω, Y ω, Z ω, U ω)) ν μ) :
    IdentDistrib (fun ω => (Z ω, U ω, Y ω))
                 (fun ω' => (Z' ω', U' ω', Y₁ ω')) μ ν :=
  hSecond.symm.comp measurable_projZUB
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
namespace ZhangYeung
namespace _root_.ZhangYeung
theorem _root_.solution
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (hU : Measurable U)
    (hX' : Measurable X') (hY₁ : Measurable Y₁)
    (hZ' : Measurable Z') (hU' : Measurable U')
    (hFirst : IdentDistrib (fun ω' => (X' ω', Y' ω', Z' ω', U' ω'))
                           (fun ω => (X ω, Y ω, Z ω, U ω)) ν μ)
    (hSecond : IdentDistrib (fun ω' => (X₁ ω', Y₁ ω', Z' ω', U' ω'))
                            (fun ω => (X ω, Y ω, Z ω, U ω)) ν μ) :
    delta Z U X Y μ = delta Z' U' X' Y₁ ν := by
  have hZU : IdentDistrib (fun ω => (Z ω, U ω)) (fun ω' => (Z' ω', U' ω')) μ ν :=
    hFirst.symm.comp measurable_pairZU
  rw [delta_def, delta_def, hZU.mutualInfo_eq,
      IdentDistrib.condMutualInfo_eq hZ hU hX hZ' hU' hX' (copyLemma_triple_XFirst hFirst),
      IdentDistrib.condMutualInfo_eq hZ hU hY hZ' hU' hY₁ (copyLemma_triple_YSecond hSecond)]
end _root_.ZhangYeung
end ZhangYeung
