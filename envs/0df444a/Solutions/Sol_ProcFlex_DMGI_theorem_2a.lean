-- Prove2me | solution 1 for ProcFlex.DMGI.theorem_2a
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T20:49:17.095792+00:00
-- url     : https://prove2.me/submissions/3cabbda5-6af6-45e3-9c33-95e20edd5c13

import Mathlib
import Definitions.Def_ProcFlex_DMGI_Model
import Theorems.Thm_ProcFlex_DMGI_theorem_1

open ProcFlex.DMGI

theorem solution {m n T : ℕ} (S : System m n T) (hS : S.IsValid)
    (A₁ A₂ : Design m n) (h : ℝ → (Fin T → ℝ) → ℝ)
    (hh : ∀ y, StrictMono (fun x => h x y))
    (hcont₁ : ContinuousOn (f S h A₁) {d | ∀ i, 0 ≤ d i})
    (hcont₂ : ContinuousOn (f S h A₂) {d | ∀ i, 0 ≤ d i})
    (U : Set (Fin n → ℝ)) (μ : Fin n → ℝ)
    (hU : IsSymmetricAround S U μ)
    (hUpos : ∀ d ∈ U, ∀ i, 0 ≤ d i)
    (hUne : U.Nonempty) (hUc : IsCompact U)
    (hδ : ∀ K, InQ S K → dmgi S μ K A₂ ≤ dmgi S μ K A₁) :
    Rf S h A₂ U ≤ Rf S h A₁ U := by
  have h1 := theorem_1 S hS A₁ h hh hcont₁ U μ hU hUpos hUne hUc
  have h2 := theorem_1 S hS A₂ h hh hcont₂ U μ hU hUpos hUne hUc
  obtain ⟨K, hK, ε, hε, hv⟩ := h1.1
  rw [hv]
  have hmem : h (dmgi S μ K A₂ + blockSum S K ε) (catSum S (μ + ε)) ∈
      {v : ℝ | ∃ (K : Fin T → Fin (T + 1) → ℕ), InQ S K ∧
        ∃ ε ∈ ((fun d => d - μ) '' U),
          v = h (dmgi S μ K A₂ + blockSum S K ε) (catSum S (μ + ε))} :=
    ⟨K, hK, ε, hε, rfl⟩
  calc Rf S h A₂ U ≤ h (dmgi S μ K A₂ + blockSum S K ε) (catSum S (μ + ε)) :=
        h2.2 hmem
    _ ≤ h (dmgi S μ K A₁ + blockSum S K ε) (catSum S (μ + ε)) :=
        (hh (catSum S (μ + ε))).monotone (by linarith [hδ K hK])
