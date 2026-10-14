-- Prove2me | solution 1 for PersistClust.Count.theorem_4_5_elder_chase_essential_bar
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-12T17:04:59.186886+00:00
-- url     : https://prove2.me/submissions/0be62567-4b40-4adb-b7ee-ed16af71091b

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_Rips

open PersistClust.Count

/- Diagram-likeness of the multiplicity diagram: every nonzero point has death
coordinate strictly below birth. (The same fact appears in the auxiliary layer of the
accepted theorem_4_8_core solution; inlined here so this file is self-contained.) -/
theorem t45gamma_isDiagramLike_mult (r : ℝ → ℝ → ℕ∞) : IsDiagramLike (mult r) := by
  intro p hp
  by_contra hne
  have hle : p.1 ≤ p.2 := not_lt.mp hne
  have h0 : mult r p = 0 := by
    unfold mult
    by_cases h1 : p.1 ≠ ⊥ ∧ p.1 ≠ ⊤
    · rw [if_pos h1]
      by_cases h2 : p.2 = ⊥
      · have hle' : p.1 ≤ ⊥ := h2 ▸ hle
        exact absurd (le_antisymm hle' bot_le) h1.1
      · rw [if_neg h2]
        by_cases h3 : p.2 < p.1
        · exact absurd h3 (not_lt.mpr hle)
        · rw [if_neg h3]
    · rw [if_neg h1]
  exact hp h0

theorem solution {X : Type*} [MetricSpace X] {f : X → ℝ} {c δ τ : ℝ}
    (hfin : {p : EReal × EReal | diagram0 f p ≠ 0}.Finite)
    (hstart : ∃ p : EReal × EReal, diagram0 f p ≠ 0 ∧
      p.1 ≤ ((τ + c * δ : ℝ) : EReal))
    (helder : ∀ (b d : EReal), diagram0 f (b, d) ≠ 0 → d ≠ ⊥ →
      ∃ (b' d' : EReal), diagram0 f (b', d') ≠ 0 ∧ d < d' ∧ d' ≤ b' ∧ b' ≤ b) :
    ∃ b : EReal, b ≤ ((τ + c * δ : ℝ) : EReal) ∧ diagram0 f (b, ⊥) ≠ 0 := by
  classical
  by_contra hno
  have hDiag : IsDiagramLike (diagram0 f) := t45gamma_isDiagramLike_mult (superRank f)
  have hSfin : {p : EReal × EReal | diagram0 f p ≠ 0 ∧
      p.1 ≤ ((τ + c * δ : ℝ) : EReal) ∧ p.2 < p.1}.Finite :=
    hfin.subset (fun p hp => hp.1)
  obtain ⟨p₀, hp₀ne, hp₀le⟩ := hstart
  have hp₀S : p₀ ∈ {p : EReal × EReal | diagram0 f p ≠ 0 ∧
      p.1 ≤ ((τ + c * δ : ℝ) : EReal) ∧ p.2 < p.1} :=
    ⟨hp₀ne, hp₀le, hDiag p₀ hp₀ne⟩
  obtain ⟨pstar, hpS, hpSmax⟩ :=
    Set.exists_max_image {p : EReal × EReal | diagram0 f p ≠ 0 ∧
      p.1 ≤ ((τ + c * δ : ℝ) : EReal) ∧ p.2 < p.1} (fun p => p.2) hSfin ⟨p₀, hp₀S⟩
  have hpSne : pstar.2 ≠ ⊥ := by
    intro hbot
    apply hno
    have hne1 : diagram0 f (pstar.1, (⊥ : EReal)) ≠ 0 := by
      have h1 := hpS.1
      rwa [show pstar = (pstar.1, (⊥ : EReal)) from Prod.ext rfl hbot] at h1
    exact ⟨pstar.1, hpS.2.1, hne1⟩
  obtain ⟨b', d', hqne, hlt, -, hble⟩ := helder pstar.1 pstar.2 hpS.1 hpSne
  have hqS : (b', d') ∈ {p : EReal × EReal | diagram0 f p ≠ 0 ∧
      p.1 ≤ ((τ + c * δ : ℝ) : EReal) ∧ p.2 < p.1} :=
    ⟨hqne, le_trans hble hpS.2.1, hDiag (b', d') hqne⟩
  exact absurd (hpSmax (b', d') hqS) (not_le.mpr hlt)
