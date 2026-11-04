-- Prove2me | solution 1 for PowerOfDUniversality.Diffusion.theorem_2_4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T00:42:17.350847+00:00
-- url     : https://prove2.me/submissions/54b7c792-640d-42fe-8adb-71dcd93fca3a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PowerOfDUniversality_Diffusion_HalfinWhitt
import Theorems.Thm_PowerOfDUniversality_Diffusion_theorem_2_4_uniqueness
import Theorems.Thm_PowerOfDUniversality_Diffusion_theorem_2_4_jsq
import Theorems.Thm_PowerOfDUniversality_Diffusion_proposition_5_1

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open PowerOfDUniversality.Diffusion

theorem solution (β : ℝ) (hβ : 0 < β) (b : ℕ∞) (hb : 2 ≤ b) (k : ℕ) (hk : 2 ≤ k)
    (ν : Measure (Fin k → ℝ)) (d : ℕ → ℕ) (lam : ℕ → ℝ) {Ω : ℕ → Type}
    [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N)) (Q₀ : ∀ N, Ω N → ℕ → ℕ)
    (E : ∀ N, Ω N → ℕ → ℝ) (M : ∀ N, Ω N → ℕ → Mark)
    (hseq : IsHWSequence β b k ν (fun N => N) d lam P Q₀ E M)
    (hd : Tendsto (fun N : ℕ => (d N : ℝ) / (Real.sqrt N * Real.log N)) atTop atTop) :
    (∀ (w : ℝ → ℝ) (x : Fin k → ℝ) (Q Q' : ℝ → ℕ → ℝ) (U U' : ℝ → ℝ),
        Solves24 β k w x Q U → Solves24 β k w x Q' U' →
        ∀ t : ℝ, 0 ≤ t → Q t = Q' t ∧ U t = U' t) ∧
    HasDiffusionLimit24 β k ν P
      (fun N ω => diffusionProcess b N (Q₀ N ω) (E N ω) (M N ω)) := by
  refine ⟨fun w x Q Q' U U' h h' => theorem_2_4_uniqueness β hβ k hk w x Q Q' U U' h h', ?_⟩
  have hJSQ : JSQDiffusionLimitStatement β b k ν := by
    intro Ns lam' Ω' _ P' Q₀' E' M' hs
    exact theorem_2_4_jsq β hβ b hb k hk ν Ns lam' P' Q₀' E' M' hs
  exact proposition_5_1 β hβ b hb k hk ν hJSQ d lam P Q₀ E M hseq hd
