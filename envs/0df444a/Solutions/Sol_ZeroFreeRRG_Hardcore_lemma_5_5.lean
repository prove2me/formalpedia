-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.lemma_5_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-22T22:55:41.668694+00:00
-- url     : https://prove2.me/submissions/ea920923-77ab-483e-9789-4c6f0234b88e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_ZeroFreeRRG_Hardcore_lemma_5_5_local_moments
import Theorems.Thm_ZeroFreeRRG_Hardcore_lemma_5_5_paired_gap
import Theorems.Thm_ZeroFreeRRG_Hardcore_lemma_5_5_cycle_moments
import Theorems.Thm_ZeroFreeRRG_Hardcore_lemma_5_5_cycle_bounds

open scoped Classical ComplexOrder
open Filter Topology AFIsingKS
open ZeroFreeRRG.Hardcore

theorem solution (m : Model) (hm : m.Valid) (d : ℕ) (hd : 3 ≤ d) (t : ℝ) (ht : m.Nontrivial t)
    (hκ : ∀ κ ∈ m.nonconstEig (t : ℂ), κ ≤ 0) (hC2 : Condition2 m d t) :
    ∃ r : ℝ, 0 < r ∧ ∀ (c₀ : m.Spin × m.Spin) (lo hi : m.Spin × m.Spin → ℝ),
      tensorVec (m.pi t) (m.pi t) ∈ overlapBox c₀ lo hi → (∀ ab, hi ab - lo ab < r) →
      ∃ c : ℝ, 0 < c ∧ ∃ R : ℝ, 0 < R ∧
        (∃ A : ℂ → ℂ, DifferentiableOn ℂ A (Metric.ball (t : ℂ) R) ∧
            (∀ z ∈ Metric.ball (t : ℂ) R, A z ≠ 0) ∧
            TendstoLocallyUniformlyOn (fun n z => an m d n z) A
              (atTop ⊓ 𝓟 {n : ℕ | Even (n * d)}) (Metric.ball (t : ℂ) R)) ∧
        (∃ G2 : ℂ × ℂ → ℂ,
            DifferentiableOn ℂ G2 (Metric.ball (t : ℂ) R ×ˢ Metric.ball (t : ℂ) R) ∧
            TendstoLocallyUniformlyOn
              (fun n (p : ℂ × ℂ) => cmE (fun M : Matching n d => Z2 m (overlapBox c₀ lo hi) p.1 p.2 M) /
                (an m d n p.1 * an m d n p.2)) G2
              (atTop ⊓ 𝓟 {n : ℕ | Even (n * d)})
              (Metric.ball (t : ℂ) R ×ˢ Metric.ball (t : ℂ) R)) ∧
        (∀ s u : ℝ, (s : ℂ) ∈ Metric.ball (t : ℂ) R → (u : ℂ) ∈ Metric.ball (t : ℂ) R →
          (∀ i j, 0 ≤ m.P s i j) → (∀ i j, 0 ≤ m.P u i j) →
          ∀ (ρ : m.Spin × m.Spin → ℝ) (Q : m.Spin × m.Spin → m.Spin × m.Spin → ℝ),
            IsEdgeMarginal ρ Q → ρ ∈ overlapBox c₀ lo hi →
            rateFn d (tensorVec (m.pi s) (m.pi u)) (tensorMat (m.P s) (m.P u)) ρ Q ≤
              (((-c) * sqDist ρ (tensorVec (m.pi s) (m.pi u)) Q (tensorMat (m.P s) (m.P u)) : ℝ)
                : EReal)) ∧
        (∀ k : ℕ, 1 ≤ k → ∀ j : Fin k → ℕ,
          Tendsto (fun n => cmProb (fun M : Matching n d => ∀ i : Fin k, cycleCount M ((i : ℕ) + 1) = j i))
            (atTop ⊓ 𝓟 {n : ℕ | Even (n * d)})
            (𝓝 (∏ i : Fin k, (ProbabilityTheory.poissonMeasure (lamCyc d ((i : ℕ) + 1)).toNNReal).real {j i}))) ∧
        (∀ s : ℝ, (s : ℂ) ∈ Metric.ball (t : ℂ) R → (∀ i j, 0 ≤ m.P s i j) →
          Tendsto (fun n => cmE (fun M : Matching n d => Z2 m (overlapBox c₀ lo hi) s s M) /
              an m d n (s : ℂ) ^ 2)
            (atTop ⊓ 𝓟 {n : ℕ | Even (n * d)})
            (𝓝 (Complex.exp (∑' ℓ : ℕ, (lamCyc d (ℓ + 1) : ℂ) * deltaCyc m (ℓ + 1) s ^ 2))) ∧
          ∀ k : ℕ, 1 ≤ k → ∀ j : Fin k → ℕ,
            Tendsto (fun n => cmE (fun M : Matching n d => normZ m (s : ℂ) M *
                ∏ i : Fin k, (((cycleCount M ((i : ℕ) + 1)).descFactorial (j i) : ℕ) : ℂ)) /
                an m d n (s : ℂ))
              (atTop ⊓ 𝓟 {n : ℕ | Even (n * d)})
              (𝓝 (∏ i : Fin k, ((lamCyc d ((i : ℕ) + 1) : ℂ) * (1 + deltaCyc m ((i : ℕ) + 1) s)) ^ (j i)))) ∧
        (∃ β : ℕ → ℝ, (∀ ℓ, ∀ z ∈ Metric.ball (t : ℂ) R, ‖deltaCyc m (ℓ + 1) z‖ ^ 2 ≤ β ℓ) ∧
            Summable (fun ℓ => lamCyc d (ℓ + 1) * β ℓ)) ∧
        (∀ ℓ : ℕ, 3 ≤ ℓ → ∀ z ∈ Metric.ball (t : ℂ) R, 1 + deltaCyc m ℓ z ≠ 0) := by
  obtain ⟨r₁, hr₁, hmom⟩ := lemma_5_5_local_moments m hm d hd t ht hκ hC2
  obtain ⟨r₂, hr₂, hgap⟩ := lemma_5_5_paired_gap m hm d hd t ht hκ hC2
  obtain ⟨r₃, hr₃, hcycles⟩ := lemma_5_5_cycle_moments m hm d hd t ht hκ hC2
  obtain ⟨R₄, hR₄, hβ, hnonzero⟩ := lemma_5_5_cycle_bounds m hm d hd t ht hκ hC2
  let r := min r₁ (min r₂ r₃)
  refine ⟨r, lt_min hr₁ (lt_min hr₂ hr₃), ?_⟩
  intro c₀ lo hi hcenter hsides
  have hs₁ : ∀ ab, hi ab - lo ab < r₁ := fun ab =>
    (hsides ab).trans_le (min_le_left _ _)
  have hs₂ : ∀ ab, hi ab - lo ab < r₂ := fun ab =>
    (hsides ab).trans_le ((min_le_right r₁ _).trans (min_le_left _ _))
  have hs₃ : ∀ ab, hi ab - lo ab < r₃ := fun ab =>
    (hsides ab).trans_le ((min_le_right r₁ _).trans (min_le_right _ _))
  obtain ⟨R₁, hR₁, hA, hG2⟩ := hmom c₀ lo hi hcenter hs₁
  obtain ⟨c, hc, R₂, hR₂, hrate⟩ := hgap c₀ lo hi hcenter hs₂
  obtain ⟨R₃, hR₃, hpoisson, hweighted⟩ := hcycles c₀ lo hi hcenter hs₃
  let R := min R₁ (min R₂ (min R₃ R₄))
  have hsub₁ : Metric.ball (t : ℂ) R ⊆ Metric.ball (t : ℂ) R₁ :=
    Metric.ball_subset_ball (min_le_left _ _)
  have hsub₂ : Metric.ball (t : ℂ) R ⊆ Metric.ball (t : ℂ) R₂ :=
    Metric.ball_subset_ball ((min_le_right R₁ _).trans (min_le_left _ _))
  have hsub₃ : Metric.ball (t : ℂ) R ⊆ Metric.ball (t : ℂ) R₃ :=
    Metric.ball_subset_ball ((min_le_right R₁ _).trans ((min_le_right R₂ _).trans (min_le_left _ _)))
  have hsub₄ : Metric.ball (t : ℂ) R ⊆ Metric.ball (t : ℂ) R₄ :=
    Metric.ball_subset_ball ((min_le_right R₁ _).trans ((min_le_right R₂ _).trans (min_le_right _ _)))
  obtain ⟨A, hAdiff, hAne, hAlim⟩ := hA
  obtain ⟨G2, hG2diff, hG2lim⟩ := hG2
  refine ⟨c, hc, R, lt_min hR₁ (lt_min hR₂ (lt_min hR₃ hR₄)), ?_⟩
  refine ⟨⟨A, hAdiff.mono hsub₁, fun z hz => hAne z (hsub₁ hz), hAlim.mono hsub₁⟩,
    ⟨G2, hG2diff.mono (Set.prod_mono hsub₁ hsub₁), hG2lim.mono (Set.prod_mono hsub₁ hsub₁)⟩,
    ?_, hpoisson, ?_, ?_, ?_⟩
  · intro s u hs hu hPs hPu ρ Q hQ hρ
    exact hrate s u (hsub₂ hs) (hsub₂ hu) hPs hPu ρ Q hQ hρ
  · intro s hs hPs
    exact hweighted s (hsub₃ hs) hPs
  · obtain ⟨β, hbound, hsum⟩ := hβ
    exact ⟨β, fun ℓ z hz => hbound ℓ z (hsub₄ hz), hsum⟩
  · intro ℓ hℓ z hz
    exact hnonzero ℓ hℓ z (hsub₄ hz)
