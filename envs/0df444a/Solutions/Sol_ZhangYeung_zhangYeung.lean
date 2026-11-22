-- Prove2me | solution 1 for ZhangYeung.zhangYeung
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:16:28.190803+00:00
-- url     : https://prove2.me/submissions/fa136f59-6e71-4457-932b-576f8a940aee

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_Delta
public import Definitions.Def_LeanPool_ZhangYeungInequality_CopyLemma
public import Definitions.Def_LeanPool_ZhangYeungInequality_Prelude
public import Definitions.Def_LeanPool_ZhangYeungInequality_Theorem3
public import Theorems.Thm_P2M_ZhangYeung_copyLemma_delta_le_mutualInfo_X_X__17723bd2c333
public import Theorems.Thm_P2M_ZhangYeung_copyLemma_delta_le_mutualInfo_Y__217277e4688a
public import Theorems.Thm_ProbabilityTheory_IdentDistrib_mutualInfo_eq
public import Theorems.Thm_ProbabilityTheory_IdentDistrib_prodMk
public import Theorems.Thm_ProbabilityTheory_IsUniform_comp
public import Theorems.Thm_ProbabilityTheory_condMutualInfo_nonneg
public import Theorems.Thm_ZhangYeung_condIndepFun_comp
public import Theorems.Thm_ZhangYeung_copyLemma
public import Theorems.Thm_ZhangYeung_delta_def
public import Theorems.Thm_ZhangYeung_delta_form21_iff
public import Theorems.Thm_ZhangYeung_mutualInfo_add_three_way_identity
public import Theorems.Thm_ZhangYeung_mutualInfo_le_of_condIndepFun

section
@[expose] public section
namespace ZhangYeung
open MeasureTheory ProbabilityTheory
open scoped ZhangYeungPFR
universe u
section Helpers
variable {Ω : Type*} [MeasurableSpace Ω]
private lemma measurable_pairXZU
    {S₁ S₂ S₃ S₄ : Type*}
    [MeasurableSpace S₁] [MeasurableSpace S₂] [MeasurableSpace S₃] [MeasurableSpace S₄] :
    Measurable (fun p : S₁ × S₂ × S₃ × S₄ => (p.1, (p.2.2.1, p.2.2.2))) := by
  fun_prop
private lemma measurable_pairXY
    {S₁ S₂ S₃ S₄ : Type*}
    [MeasurableSpace S₁] [MeasurableSpace S₂] [MeasurableSpace S₃] [MeasurableSpace S₄] :
    Measurable (fun p : S₁ × S₂ × S₃ × S₄ => (p.1, p.2.1)) := by
  fun_prop
end Helpers
section MainTheorems
variable {Ω : Type*} [MeasurableSpace Ω]
  {S₁ S₂ S₃ S₄ : Type u}
  [MeasurableSpace S₁] [MeasurableSpace S₂]
  [MeasurableSpace S₃] [MeasurableSpace S₄]
  [Finite S₁] [Finite S₂] [Finite S₃] [Finite S₄]
  [MeasurableSingletonClass S₁] [MeasurableSingletonClass S₂]
  [MeasurableSingletonClass S₃] [MeasurableSingletonClass S₄]
private theorem zhangYeung_integer
    {X : Ω → S₁} {Y : Ω → S₂} {Z : Ω → S₃} {U : Ω → S₄}
    (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hU : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    2 * I[Z : U; μ] - 3 * I[Z : U | X; μ] - I[Z : U | Y; μ]
      ≤ I[X : Y; μ] + I[X : ⟨Z, U⟩; μ] := by
  obtain ⟨Ω', _, ν, X', Y', X₁, Y₁, Z', U',
      _, hX', _, hX₁, hY₁, hZ', hU', hFirst, hSecond, hCond⟩ :=
    copyLemma hX hY hZ hU μ
  -- Step 1: two copy-lemma inequalities (paper lines 683, 689).
  have h1 : delta Z U X Y μ ≤ I[X' : Y₁; ν] :=
    copyLemma_delta_le_mutualInfo_Y₁ hX hY hZ hU hX' hY₁ hZ' hU' hFirst hSecond hCond
  have h2 : I[Z : U; μ] - 2 * I[Z : U | X; μ] ≤ I[X' : X₁; ν] :=
    copyLemma_delta_le_mutualInfo_X_X₁ hX hZ hU hX' hX₁ hZ' hU' hFirst hSecond hCond
  rw [delta_def] at h1
  -- Step 2: three-way interaction identity on ν (paper line 700).
  have h_three :
      I[X' : X₁; ν] + I[X' : Y₁; ν]
        = I[X' : ⟨X₁, Y₁⟩; ν] + I[X₁ : Y₁; ν] - I[X₁ : Y₁ | X'; ν] :=
    mutualInfo_add_three_way_identity hX' hX₁ hY₁ ν
  -- Step 3: drop the nonneg CMI term.
  have h_nonneg : 0 ≤ I[X₁ : Y₁ | X'; ν] := condMutualInfo_nonneg hX₁ hY₁
  -- Step 4: data processing (paper line 708).
  have hCond_proj : CondIndepFun X' (fun ω' => (X₁ ω', Y₁ ω'))
                      (fun ω' => (Z' ω', U' ω')) ν :=
    ZhangYeung.condIndepFun_comp (φ := Prod.fst) (ψ := id)
      measurable_fst measurable_id hCond
  have h_dp : I[X' : ⟨X₁, Y₁⟩; ν] ≤ I[X' : ⟨Z', U'⟩; ν] :=
    mutualInfo_le_of_condIndepFun hX' (hX₁.prodMk hY₁) (hZ'.prodMk hU') ν hCond_proj
  -- Step 5: transport `I[X' : ⟨Z', U'⟩; ν] = I[X : ⟨Z, U⟩; μ]` via `hFirst`.
  have hPairXZU : IdentDistrib
      (fun ω' => (X' ω', (Z' ω', U' ω'))) (fun ω => (X ω, (Z ω, U ω))) ν μ :=
    hFirst.comp measurable_pairXZU
  have h_marg_XZU : I[X' : ⟨Z', U'⟩; ν] = I[X : ⟨Z, U⟩; μ] :=
    hPairXZU.mutualInfo_eq
  -- Step 6: transport `I[X₁ : Y₁; ν] = I[X : Y; μ]` via `hSecond`.
  have hPairXY : IdentDistrib
      (fun ω' => (X₁ ω', Y₁ ω')) (fun ω => (X ω, Y ω)) ν μ :=
    hSecond.comp measurable_pairXY
  have h_marg_XY : I[X₁ : Y₁; ν] = I[X : Y; μ] :=
    hPairXY.mutualInfo_eq
  linarith [h1, h2, h_three, h_nonneg, h_dp, h_marg_XZU, h_marg_XY]
end MainTheorems
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
      ≤ (1 / 2) * (I[X : Y; μ] + I[X : ⟨Z, U⟩; μ]
        + I[Z : U | X; μ] - I[Z : U | Y; μ]) := by
  have h_int := zhangYeung_integer hX hY hZ hU μ
  linarith [(delta_form21_iff Z U X Y μ).mpr h_int]
end _root_.ZhangYeung
end ZhangYeung
