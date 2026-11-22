-- Prove2me | solution 1 for ZhangYeung.delta_of_condMI_vanishes_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:11:22.958239+00:00
-- url     : https://prove2.me/submissions/c9da6c48-da4a-44e8-845c-3f030b85cb3a

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_Delta
public import Definitions.Def_LeanPool_ZhangYeungInequality_Prelude
public import Definitions.Def_LeanPool_ZhangYeungInequality_CopyLemma
public import Theorems.Thm_P2M_ProbabilityTheory_chain_rule___ff6bade4a15d
public import Theorems.Thm_ProbabilityTheory_IdentDistrib_prodMk
public import Theorems.Thm_ProbabilityTheory_Kernel_mutualInfo_def
public import Theorems.Thm_ProbabilityTheory_condMutualInfo_eq
public import Theorems.Thm_ZhangYeung_IdentDistrib_condMutualInfo_eq
public import Theorems.Thm_ZhangYeung_delta_def


set_option autoImplicit true
@[expose] public section
public section
open ZhangYeung
open MeasureTheory ProbabilityTheory
open scoped ZhangYeungPFR
universe u
namespace ZhangYeung
theorem _root_.solution
    {Ω : Type*} [MeasurableSpace Ω]
    {α β γ δ : Type*}
    [Finite α] [Finite β] [Finite γ] [Finite δ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [MeasurableSingletonClass γ] [MeasurableSingletonClass δ]
    {A : Ω → α} {B : Ω → β} {C : Ω → γ} {D : Ω → δ}
    (hA : Measurable A) (hB : Measurable B) (hC : Measurable C) (hD : Measurable D)
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (hVanish : I[A : D|⟨B, C⟩;ν] = 0) :
    delta B C A D ν
      = I[A : D; ν] - I[A : D | B; ν] - I[A : D | C; ν]
        - I[B : C | ⟨A, D⟩; ν] := by
  have hBC : Measurable (fun ω => (B ω, C ω)) := hB.prodMk hC
  have hAD : Measurable (fun ω => (A ω, D ω)) := hA.prodMk hD
  rw [delta_def,
      mutualInfo_def B C ν, mutualInfo_def A D ν,
      condMutualInfo_eq hB hC hA ν,
      condMutualInfo_eq hB hC hD ν,
      condMutualInfo_eq hA hD hB ν,
      condMutualInfo_eq hA hD hC ν,
      condMutualInfo_eq hB hC hAD ν]
  rw [condMutualInfo_eq hA hD hBC ν] at hVanish
  rw [chain_rule'' ν hB hA, chain_rule'' ν hC hA, chain_rule'' ν hBC hA,
      chain_rule'' ν hB hD, chain_rule'' ν hC hD, chain_rule'' ν hBC hD,
      chain_rule'' ν hA hB, chain_rule'' ν hD hB, chain_rule'' ν hAD hB,
      chain_rule'' ν hA hC, chain_rule'' ν hD hC, chain_rule'' ν hAD hC,
      chain_rule'' ν hB hAD, chain_rule'' ν hC hAD, chain_rule'' ν hBC hAD]
  rw [chain_rule'' ν hA hBC, chain_rule'' ν hD hBC, chain_rule'' ν hAD hBC] at hVanish
  linarith [entropy_comm hB hA ν, entropy_comm hC hA ν, entropy_comm hB hD ν,
    entropy_comm hC hD ν, entropy_comm hAD hB ν, entropy_comm hAD hC ν,
    entropy_comm hA hBC ν, entropy_comm hD hBC ν, entropy_comm hAD hBC ν]
end ZhangYeung
