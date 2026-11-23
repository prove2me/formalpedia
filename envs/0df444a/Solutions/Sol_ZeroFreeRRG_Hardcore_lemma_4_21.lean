-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.lemma_4_21
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:10:18.765225+00:00
-- url     : https://prove2.me/submissions/31763770-7dab-478c-a0fb-929890553551
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AFIsingKS_Matching
import Definitions.Def_ZeroFreeRRG_Hardcore_Kernels
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
import Definitions.Def_ZeroFreeRRG_Hardcore_ConfigModel
import Definitions.Def_ZeroFreeRRG_Hardcore_Moments
import Theorems.Thm_ZeroFreeRRG_Hardcore_l421_realCut
import Theorems.Thm_ZeroFreeRRG_Hardcore_l421_weights
import Theorems.Thm_ZeroFreeRRG_Hardcore_l421_first
import Theorems.Thm_ZeroFreeRRG_Hardcore_l421_color
import Theorems.Thm_ZeroFreeRRG_Hardcore_l421_continue

open scoped Classical
open AFIsingKS

namespace ZeroFreeRRG.Hardcore
end ZeroFreeRRG.Hardcore

open ZeroFreeRRG.Hardcore

theorem solution (m : Model) (hm : m.Valid) (d : ℕ) (hd : 3 ≤ d) (t : ℝ) (ht : m.Nontrivial t)
    (hC1 : Condition1 m d t) (hC2 : Condition2 m d t) :
    ∃ r : ℝ, 0 < r ∧ ∀ (c₀ : m.Spin × m.Spin) (lo hi : m.Spin × m.Spin → ℝ),
      tensorVec (m.pi t) (m.pi t) ∈ overlapBox c₀ lo hi → (∀ ab, hi ab - lo ab < r) →
      ∃ E : ∀ n : ℕ, Set (Matching n d), (∀ n, IsGraphEvent (E n)) ∧
        ∃ R : ℝ, 0 < R ∧ ∃ γ : ℝ, 0 < γ ∧
        ∃ C : ℝ, ∃ N : ℕ, ∀ n ≥ N, Even (n * d) →
          ‖cmE (fun M : Matching n d =>
              if M ∈ E n then normZ m (t : ℂ) M ^ 2 - Z2 m (overlapBox c₀ lo hi) t t M else 0)‖
            ≤ C * Real.exp (-γ * n) * ‖an m d n (t : ℂ)‖ ^ 2 ∧
          ∀ z ∈ Metric.ball (t : ℂ) R, ∀ w ∈ Metric.ball (t : ℂ) R,
            ‖cmE (fun M : Matching n d => if M ∈ E n then normZ m z M else 0) - an m d n z‖
              ≤ C * Real.exp (-γ * n) * ‖an m d n z‖ ∧
            ‖cmE (fun M : Matching n d =>
                (if M ∈ E n then normZ m z M else 0) * (if M ∈ E n then normZ m w M else 0)) -
              cmE (fun M : Matching n d => Z2 m (overlapBox c₀ lo hi) z w M)‖
              ≤ C * Real.exp (-γ * n) * ‖an m d n z * an m d n w‖ := by
  have build_positive : ∀ (m : Model), m.Valid → ∀ (d : ℕ), 3 ≤ d → ∀ (x : ℝ),
      m.PosParam x → Condition1 m d x → Condition2 m d x →
      ∃ r : ℝ, 0 < r ∧ ∀ (c₀ : m.Spin × m.Spin) (lo hi : m.Spin × m.Spin → ℝ),
        tensorVec (m.pi x) (m.pi x) ∈ overlapBox c₀ lo hi → (∀ ab, hi ab - lo ab < r) →
        ∃ E : ∀ n : ℕ, Set (Matching n d), (∀ n, IsGraphEvent (E n)) ∧
          ∃ R : ℝ, 0 < R ∧ ∃ γ : ℝ, 0 < γ ∧
          ∃ C : ℝ, ∃ N : ℕ, ComplexTruncationBound m d x (overlapBox c₀ lo hi) E R γ C N := by
    intro m hm d hd x hx hC1 hC2
    obtain ⟨r, hr, hboxes⟩ := l421_realCut m hm d hd x hx hC1 hC2
    refine ⟨r, hr, ?_⟩
    intro c₀ lo hi hcenter hside
    obtain ⟨ε, hε, hE, c, hc, C, N, hReal⟩ := hboxes c₀ lo hi hcenter hside
    obtain ⟨A, R, hCompare⟩ :=
      l421_weights m hm d hd x hx (overlapBox c₀ lo hi) (c / 4) (by positivity)
    have hxn : m.Nontrivial x := by
      cases m with
      | hardcore => exact hx
      | potts q => exact ⟨hx.1.le, hx.2⟩
    have hFirst := l421_first m hm d hd x hxn hC2 x hx
    obtain ⟨R', hR', γ, hγ, C', N', hmom⟩ :=
      l421_continue m d x x (overlapBox c₀ lo hi)
        (fun n => partitionCutoff m x d n ε) c C N A (c / 4) R hReal hCompare hFirst
        (by linarith)
    exact ⟨fun n => partitionCutoff m x d n ε, hE, R', hR', γ, hγ, C', N', hmom⟩
  cases m with
  | hardcore =>
      exact build_positive .hardcore hm d hd t ht hC1 hC2
  | potts q =>
      by_cases ht0 : t = 0
      · subst t
        obtain ⟨r, hr, hboxes⟩ := l421_color q hm d hd hC1 hC2
        refine ⟨r, hr, ?_⟩
        intro c₀ lo hi hcenter hside
        obtain ⟨x, hx0, hx1, ε, hε, hE, c, hc, C, N, A, k, R, hkc, hReal, hCompare⟩ :=
          hboxes c₀ lo hi hcenter hside
        have hx : (Model.potts q).PosParam x := ⟨hx0, hx1⟩
        have hFirst := l421_first (.potts q) hm d hd 0 ht hC2 x hx
        obtain ⟨R', hR', γ, hγ, C', N', hmom⟩ :=
          l421_continue (.potts q) d 0 x (overlapBox c₀ lo hi)
            (fun n => partitionCutoff (.potts q) x d n ε) c C N A k R hReal hCompare hFirst
            (by linarith)
        exact ⟨fun n => partitionCutoff (.potts q) x d n ε, hE, R', hR', γ, hγ, C', N', hmom⟩
      · have hx : (Model.potts q).PosParam t := ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), ht.2⟩
        exact build_positive (.potts q) hm d hd t hx hC1 hC2
