-- Prove2me | solution 1 for ShortWDRODual.IP.IP_imp_proj
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T11:08:04.948205+00:00
-- url     : https://prove2.me/submissions/d6b5b2df-8993-4d9f-8e57-6d2ad28be549

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_IP_Setting

open MeasureTheory ModelRiskOT.Duality ShortWDRODual.IP
open scoped ENNReal

theorem solution {X : Type*} [MeasurableSpace X] (Phat : Measure X)
    [IsProbabilityMeasure Phat]
    (hIP : ∀ φ : X × X → EReal, DiagDomFun φ → (∀ p, φ p ≠ ⊤) → ShortWDRODual.Legendre.IP Phat φ) :
    Proj Phat := by
  intro A hA
  classical
  set φ : X × X → EReal := fun p => if p ∈ A then 1 else 0 with hφdef
  have hmeas : Measurable φ := Measurable.ite hA.1 measurable_const measurable_const
  have hdd : DiagDomFun φ := by
    refine ⟨hmeas, fun xh x => ?_⟩
    by_cases h : (xh, x) ∈ A
    · simp [φ, h, hA.2 xh x h]
    · simp only [φ, h, if_false]
      split_ifs <;> norm_num
  have hnt : ∀ p, φ p ≠ ⊤ := by
    intro p; simp only [φ]; split_ifs
    · exact EReal.coe_ne_top 1
    · exact EReal.coe_ne_top 0
  obtain ⟨-, -, hnm, -⟩ := hIP φ hdd hnt
  have hset : Prod.fst '' A = ShortWDRODual.Legendre.supFn φ ⁻¹' Set.Ioi 0 := by
    ext xh
    simp only [Set.mem_image, Set.mem_preimage, Set.mem_Ioi, ShortWDRODual.Legendre.supFn,
      lt_iSup_iff]
    constructor
    · rintro ⟨⟨a, b⟩, hab, rfl⟩
      exact ⟨b, by simp [φ, hab]⟩
    · rintro ⟨b, hb⟩
      refine ⟨(xh, b), ?_, rfl⟩
      by_contra h
      simp [φ, h] at hb
  rw [hset]
  exact hnm measurableSet_Ioi
