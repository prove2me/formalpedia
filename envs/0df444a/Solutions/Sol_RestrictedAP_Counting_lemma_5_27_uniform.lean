-- Prove2me | solution 1 for RestrictedAP.Counting.lemma_5_27_uniform
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-22T22:57:11.879868+00:00
-- url     : https://prove2.me/submissions/da78fb2c-a65d-4f10-997f-ff12a9018f5e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RestrictedAP_Counting_Distributions
import Definitions.Def_RestrictedAP_Counting_Resilience
import Definitions.Def_RestrictedAP_Counting_LowInfluence
import Theorems.Thm_RestrictedAP_Counting_lemma_5_27_regularized_uniform
import Theorems.Thm_RestrictedAP_Counting_claim_5_22_uniform

open RestrictedAP.Counting

theorem solution (m : ℕ) (s δ : ℝ) (hs : 0 < s) (hδ : 0 < δ) :
    ∃ B₀ : ℕ, ∃ c : ℝ, 0 < c ∧
      ∀ (Sig : Type) [Fintype Sig] [DecidableEq Sig], Fintype.card Sig ≤ m →
      ∀ (μ : Sig × Sig × Sig → ℝ) (ν : Sig → ℝ), IsDist μ →
        (∀ i : Fin 3, marginal μ i = ν) → (∀ x : Sig, μ (x, x, x) ≠ 0) →
        ¬ DistHasEmbedding ℤ μ → AtomsAtLeast μ s →
      ∀ (n B : ℕ), B₀ ≤ B →
      ∀ f : (Fin n → Sig) → ℝ, (∀ x, f x = 0 ∨ f x = 1) → Resilient ν B (1 / 2) f →
        δ ≤ expect (tensorPow ν n) f →
        s ^ (B + 1) * c ≤ Delta1 μ f := by
  obtain ⟨D, C, hC, Hreg⟩ := lemma_5_27_regularized_uniform m s δ hs hδ
  obtain ⟨τ, ξ, c₂, hτ, hξ, hc₂, Hgauss⟩ :=
    claim_5_22_uniform m s (δ / 256) hs (by positivity) D C hC
  obtain ⟨B₀, c₁, hc₁, Hgood⟩ := Hreg τ ξ hτ hξ
  refine ⟨B₀, c₁ * c₂, mul_pos hc₁ hc₂, ?_⟩
  intro Sig _ _ hcard μ ν hμ hmarg hdiag hemb hatoms n B hB f hf hres hdens
  have hne : Nonempty (Sig × Sig × Sig) := nonempty_of_isDist μ hμ
  letI : Nonempty Sig := ⟨(Classical.choice hne).1⟩
  obtain ⟨g, hdeg, hnorm, hinf, hmean, htrunc, hcompare⟩ :=
    Hgood Sig hcard μ ν hμ hmarg hdiag hemb hatoms n B hB f hf hres hdens
  have hT := Hgauss Sig hcard μ ν hμ hmarg hdiag hemb hatoms n g
    hdeg hnorm hinf hmean htrunc
  calc
    s ^ (B + 1) * (c₁ * c₂) = (s ^ (B + 1) * c₁) * c₂ := by ring
    _ ≤ (s ^ (B + 1) * c₁) * tripleTrunc μ g := by
      exact mul_le_mul_of_nonneg_left hT
        (mul_nonneg (pow_nonneg hs.le _) hc₁.le)
    _ ≤ Delta1 μ f := hcompare
