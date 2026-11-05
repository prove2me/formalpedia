-- Prove2me | solution 1 for ShortWDRODual.IP.IP_imp_selStar
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T11:08:05.592209+00:00
-- url     : https://prove2.me/submissions/5b949528-b6aa-47a7-bd8b-96d6fe150f6e

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_IP_Setting

open MeasureTheory ModelRiskOT.Duality ShortWDRODual.IP
open scoped ENNReal

theorem solution {X : Type*} [MeasurableSpace X] (Phat : Measure X)
    [IsProbabilityMeasure Phat]
    (hIP : ∀ φ : X × X → EReal, DiagDomFun φ → (∀ p, φ p ≠ ⊤) → ShortWDRODual.Legendre.IP Phat φ) :
    SelStar Phat := by
  intro E hE
  classical
  set G := graph E with hG
  have hGm : MeasurableSet G := hE.2.1
  set φ : X × X → EReal := fun p => if p ∈ G then 0 else ⊥ with hφdef
  have hmeas : Measurable φ := Measurable.ite hGm measurable_const measurable_const
  have hdd : DiagDomFun φ := by
    refine ⟨hmeas, fun xh x => ?_⟩
    by_cases h : (xh, x) ∈ G
    · have h2 : (x, x) ∈ G := hE.2.2 xh x h
      simp [φ, h, h2]
    · simp [φ, h]
  have hnt : ∀ p, φ p ≠ ⊤ := by
    intro p; simp only [φ]; split_ifs <;> simp
  obtain ⟨-, -, -, hEq⟩ := hIP φ hdd hnt
  have hsup : ShortWDRODual.Legendre.supFn φ = fun _ => 0 := by
    funext xh
    obtain ⟨x, hx⟩ := (hE.1 xh).2
    apply le_antisymm
    · refine iSup_le fun y => ?_
      simp only [φ]; split_ifs <;> simp
    · refine le_iSup_of_le x ?_
      have : (xh, x) ∈ G := hx
      simp [φ, this]
  have hlhs : extIntegral Phat (ShortWDRODual.Legendre.supFn φ) = 0 := by
    rw [hsup]; simp [extIntegral]
  by_contra hne
  push Not at hne
  have hbot : ∀ γ ∈ ShortWDRODual.Legendre.couplingsFst Phat, extIntegral γ φ = ⊥ := by
    intro γ hγ
    have hpos : (fun p => (φ p).toENNReal) = fun _ => 0 := by
      funext p; simp only [φ]; split_ifs <;> simp
    have hneg : (fun p => (-φ p).toENNReal) = Gᶜ.indicator (fun _ => ∞) := by
      funext p
      by_cases h : p ∈ G
      · simp [φ, h]
      · simp [φ, h]
    have h1 : (∫⁻ p, (-φ p).toENNReal ∂γ) = ⊤ := by
      rw [hneg, lintegral_indicator_const hGm.compl]
      exact ENNReal.top_mul (hne γ hγ)
    unfold extIntegral
    rw [hpos, h1]
    simp
  have : (⨆ γ ∈ ShortWDRODual.Legendre.couplingsFst Phat, extIntegral γ φ) = ⊥ := by
    refine le_antisymm (iSup₂_le fun γ hγ => (hbot γ hγ).le) bot_le
  rw [hlhs, this] at hEq
  exact absurd hEq (by simp)
