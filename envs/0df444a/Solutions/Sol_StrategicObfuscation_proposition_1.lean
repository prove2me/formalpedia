-- Prove2me | solution 1 for StrategicObfuscation.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T02:17:04.277759+00:00
-- url     : https://prove2.me/submissions/44028cff-5e51-449a-b582-6bcdd37f14ce

import Mathlib
import Definitions.Def_StrategicObfuscation_IsDetection
import Definitions.Def_StrategicObfuscation_IsEffort
import Definitions.Def_StrategicObfuscation_IsEquilibrium
import Definitions.Def_StrategicObfuscation_SolvesFour

open Set

open StrategicObfuscation in
theorem solution {V c g p : ℝ} {π : ℝ → ℝ → ℝ} {E : ℝ → ℝ → ℝ}
    (hc : 0 < c) (hcV : c < V) (hg : 0 < g) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hπ : IsDetection π) (hE : IsEffort π g E)
    {σ e α Q : ℝ} (hσ : σ ∈ Icc (0 : ℝ) 1) (heq : IsEquilibrium π V c p E σ e α Q) :
    (c < Q * V → α = 1 ∧ e = E 1 σ) ∧
    (Q * V < c → α = 0 ∧ e = 0) ∧
    (Q * V = c → α ∈ Icc (0 : ℝ) 1 ∧ SolvesFour π V c p E σ α ∧ e = E α σ) := by
  obtain ⟨heff, hα, hQ, hbayes, hopt⟩ := heq
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have h1 := hopt 1 ⟨zero_le_one, le_refl _⟩
    have : α = 1 := by
      have : 1 ≤ α := by nlinarith
      linarith [hα.2]
    subst this
    exact ⟨rfl, heff⟩
  · have h1 := hopt 0 ⟨le_refl _, zero_le_one⟩
    have : α = 0 := by
      have : α ≤ 0 := by nlinarith
      linarith [hα.1]
    subst this
    refine ⟨rfl, ?_⟩
    have hbr := hE 0 ⟨le_refl _, zero_le_one⟩ σ hσ
    have h2 := hbr.2 0 (le_refl _)
    have h3 := hbr.1
    rw [heff]
    simp at h2
    linarith
  · refine ⟨hα, ?_, heff⟩
    unfold SolvesFour
    rw [← heff, ← h]
    linear_combination V * hbayes
