-- Prove2me | solution 1 for RobustSAA.Convergence.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T19:59:33.940204+00:00
-- url     : https://prove2.me/submissions/d9598040-26c6-4770-b5ec-e9ff91608757

import Mathlib
import Definitions.Def_RobustSAA_Convergence_Setting
import Theorems.Thm_RobustSAA_Convergence_theorem_2_only_if
import Theorems.Thm_RobustSAA_Convergence_theorem_2_if

open MeasureTheory Filter Topology
open RobustSAA.Convergence

theorem solution {d : ℕ} {Ξ : Set (Pt d)} (hΞ : IsClosed Ξ) (𝓕 : DUS Ξ)
    (hne : ∀ (N : ℕ) (s : Fin N → ↥Ξ), (𝓕 N s).Nonempty) :
    IsUniformlyConsistent 𝓕 ↔
      ∀ (F : ProbabilityMeasure ↥Ξ) (dx : ℕ) (X : Set (Pt dx)) (c : Pt dx → ↥Ξ → ℝ),
        Standing F X c → Assumption1 X c → Assumption2 F X c → Assumption3 F 𝓕 X c →
          ∀ᵐ ω ∂(dataLaw F), Conditions F X c (fun N => 𝓕 N (sample ω N)) := by
  constructor
  · exact theorem_2_only_if hΞ 𝓕 hne
  · intro h
    by_contra hU
    obtain ⟨F, dx, X, c, hS, hA1, hA2, hA3, hbad⟩ := theorem_2_if hΞ 𝓕 hU
    exact hbad (h F dx X c hS hA1 hA2 hA3)
