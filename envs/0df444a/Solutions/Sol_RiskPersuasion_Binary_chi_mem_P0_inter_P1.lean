-- Prove2me | solution 1 for RiskPersuasion.Binary.chi_mem_P0_inter_P1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:05:55.555799+00:00
-- url     : https://prove2.me/submissions/dfdb72b8-50a2-462d-912c-36286a59f0b7

import Mathlib
import Definitions.Def_RiskPersuasion_Binary_Model

set_option autoImplicit false

open RiskPersuasion.Binary

theorem solution {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (ρ : (Ω → ℝ) → Fin 2 → ℝ) (hA1 : Assumption1 ρ)
    (ω₀ ω₁ : Ω) (h₀ : ω₀ ∈ L0 ρ) (h₁ : ω₁ ∈ K1 ρ) :
    χ ρ ω₀ ω₁ ∈ P ρ 0 ∩ P ρ 1 := by
  have he0 : e ω₀ ∈ P ρ 0 := h₀.1
  have he0' : e ω₀ ∉ P ρ 1 := h₀.2
  have he1 : e ω₁ ∈ P ρ 1 := h₁
  set φ : ℝ → (Ω → ℝ) := fun g => g • e ω₀ + (1 - g) • e ω₁ with hφ
  have hφc : Continuous φ := by rw [hφ]; fun_prop
  have hφs : ∀ g ∈ Set.Icc (0 : ℝ) 1, φ g ∈ stdSimplex ℝ Ω := fun g hg =>
    (convex_stdSimplex ℝ Ω) he0.1 he1.1 hg.1 (by linarith [hg.2]) (by ring)
  have hGc : IsClosed (Set.Icc (0 : ℝ) 1 ∩ φ ⁻¹' P ρ 1) :=
    isClosed_Icc.inter ((hA1 1).preimage hφc)
  have hne : (Set.Icc (0 : ℝ) 1 ∩ φ ⁻¹' P ρ 1).Nonempty :=
    ⟨0, ⟨le_refl 0, zero_le_one⟩, by simpa [hφ] using he1⟩
  have hbdd : BddAbove (Set.Icc (0 : ℝ) 1 ∩ φ ⁻¹' P ρ 1) := ⟨1, fun g hg => hg.1.2⟩
  have hγdef : γ ρ ω₀ ω₁ = sSup (Set.Icc (0 : ℝ) 1 ∩ φ ⁻¹' P ρ 1) := rfl
  have hχdef : χ ρ ω₀ ω₁ = φ (γ ρ ω₀ ω₁) := rfl
  have hmem := hGc.csSup_mem hne hbdd
  rw [← hγdef] at hmem
  have hγ01 : γ ρ ω₀ ω₁ ∈ Set.Icc (0 : ℝ) 1 := hmem.1
  have hγP1 : φ (γ ρ ω₀ ω₁) ∈ P ρ 1 := hmem.2
  have hγlt : γ ρ ω₀ ω₁ < 1 := by
    refine lt_of_le_of_ne hγ01.2 (fun h => he0' ?_)
    have := hγP1
    rw [h] at this
    simpa [hφ] using this
  rw [hχdef]
  refine ⟨?_, hγP1⟩
  by_contra hnot
  set γ' := γ ρ ω₀ ω₁ with hγ'
  have hopen : IsOpen (φ ⁻¹' (P ρ 0)ᶜ) := (hA1 0).isOpen_compl.preimage hφc
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen γ' hnot
  set g : ℝ := min 1 (γ' + ε / 2) with hg
  have hgγ : γ' < g := lt_min hγlt (by linarith)
  have hg01 : g ∈ Set.Icc (0 : ℝ) 1 := ⟨by have := hγ01.1; have := le_of_lt hgγ; linarith, min_le_left _ _⟩
  have hgball : g ∈ Metric.ball γ' ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    have : g ≤ γ' + ε / 2 := min_le_right _ _
    constructor <;> linarith
  have hnP0 : φ g ∉ P ρ 0 := hball hgball
  have hs := hφs g hg01
  have hlt : ρ (φ g) 0 < ρ (φ g) 1 := by
    by_contra hle
    push_neg at hle
    refine hnP0 ⟨hs, fun a' => ?_⟩
    fin_cases a'
    · exact le_refl _
    · exact hle
  have hgP1 : φ g ∈ P ρ 1 := ⟨hs, fun a' => by
    fin_cases a'
    · exact hlt.le
    · exact le_refl _⟩
  have hgG : g ∈ Set.Icc (0 : ℝ) 1 ∩ φ ⁻¹' P ρ 1 := ⟨hg01, hgP1⟩
  have := le_csSup hbdd hgG
  rw [← hγdef] at this
  linarith
