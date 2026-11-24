-- Prove2me | solution 1 for WeightedEdgeColor.theorem_3_1_partite
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T05:57:20.736796+00:00
-- url     : https://prove2.me/submissions/bbb69582-31b7-4f63-844d-27403951118f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WeightedEdgeColor_WGraph
import Definitions.Def_WeightedEdgeColor_WGraph_IsFeasiblePartialColoring
import Definitions.Def_WeightedEdgeColor_IsAvgOfFeasibleSets
import Theorems.Thm_WeightedEdgeColor_lemma_profile_selection
import Theorems.Thm_WeightedEdgeColor_lemma_whole_edge_rounding

set_option autoImplicit false

open WeightedEdgeColor WeightedEdgeColor.WGraph

theorem solution (C₀ C₁ ε : ℝ) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) (hε : 0 < ε) (r : ℕ) :
    ∃ n₀ Kc : ℝ, ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
      (G : WGraph V E), G.IsSimple → ∀ g : V → Fin r,
      (∀ (e : E) (u v : V), G.ends e = s(u, v) → g u ≠ g v) →
      ∀ n : ℝ, n₀ ≤ n → (∀ v, G.W v ≤ n) →
      ∀ (𝒞 : Type) [Fintype 𝒞] [DecidableEq 𝒞], (Fintype.card 𝒞 : ℝ) ≤ C₁ * n →
      ∀ x : E → 𝒞 → ℝ, (∀ e c, 0 ≤ x e c ∧ x e c ≤ C₀ / n) → (∀ e, ∑ c, x e c ≤ 1) →
      (∀ v c, G.InK v (fun e => x e c)) →
      ∃ φ : E → Option 𝒞, G.IsFeasiblePartialColoring φ ∧
        (∀ e c, φ e = some c → 0 < x e c) ∧
        ∀ v, (∑ e ∈ G.inc v, G.w e * ∑ c, x e c) - ε * n - Kc * n ^ (3 / 4 : ℝ) ≤
          G.coloredWeight φ v := by
  obtain ⟨σ, r₀, β, Cm, Ks, hσ0, hσ1, hr₀, hr₀1, hβ0, hβ, hβσ, hCm, n₀, K, hPS⟩ :=
    lemma_profile_selection C₀ C₁ (ε / 2) hC₀ hC₁ (by positivity) r
  obtain ⟨n₀', K', hWR⟩ :=
    lemma_whole_edge_rounding C₁ σ r₀ β Cm (ε / 2) Ks hC₁ hσ0 hσ1 hr₀ hr₀1 hβ0 hβ hβσ hCm
      (by positivity)
  refine ⟨max (max n₀ n₀') 1, K + |K'|, ?_⟩
  intro V E _ _ _ _ G hG g hg n hn hW 𝒞 _ _ hcard x hx hxs hxK
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hn0 : n₀ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn0' : n₀' ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  -- an orientation of every edge
  have hex : ∀ e, ∃ p : V × V, G.ends e = s(p.1, p.2) := by
    intro e
    obtain ⟨⟨a, b⟩, h⟩ := Quot.exists_rep (G.ends e)
    exact ⟨(a, b), h.symm⟩
  choose pr hst using hex
  let src : E → V := fun e => (pr e).1
  let tgt : E → V := fun e => (pr e).2
  obtain ⟨b, R, XL, XS, hprof, hXL0, hXS0, hXLc, hXSc, hsum, hmass, hslot, hres, hsupp, hloss⟩ :=
    hPS V E G hG g hg src tgt hst n hn0 hW 𝒞 hcard x hx hxs hxK
  obtain ⟨φ, hφf, hφs, hφc⟩ := hWR V E G hG src tgt hst n hn0' hW 𝒞 hcard b R XL XS hprof hXL0 hXS0
    hXLc hXSc hsum hmass hslot hres
  refine ⟨φ, hφf, ?_, ?_⟩
  · intro e c h
    exact hsupp e c (hφs e c h).ne'
  · intro v
    have h1 := hloss v
    have h2 := hφc v
    have hpow : n ^ (2 / 3 : ℝ) ≤ n ^ (3 / 4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
    have h3 : K' * n ^ (2 / 3 : ℝ) ≤ |K'| * n ^ (3 / 4 : ℝ) := by
      calc K' * n ^ (2 / 3 : ℝ) ≤ |K'| * n ^ (2 / 3 : ℝ) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
        _ ≤ |K'| * n ^ (3 / 4 : ℝ) := mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
    have hexp : (K + |K'|) * n ^ (3 / 4 : ℝ) = K * n ^ (3 / 4 : ℝ) + |K'| * n ^ (3 / 4 : ℝ) := by
      ring
    rw [hexp]
    linarith
