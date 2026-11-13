-- Prove2me | solution 1 for RestrictedAP.Counting.lemma_5_27
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T22:20:27.937825+00:00
-- url     : https://prove2.me/submissions/340cbf87-baac-4064-be76-6ca3b4ba4b16
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RestrictedAP_Counting_Distributions
import Definitions.Def_RestrictedAP_Counting_Resilience
import Theorems.Thm_RestrictedAP_Counting_lemma_5_27_uniform

section
set_option autoImplicit false

namespace RestrictedAP.Counting

/-- Lemma 5.27 from its uniform version `lemma_5_27_uniform` (with `s := α`): a minimum
non-zero atom probability `α` is in particular a lower bound on all atoms. -/
theorem chk_lemma_5_27 (m : ℕ) (α δ : ℝ) (hα : 0 < α) (hδ : 0 < δ) :
    ∃ B₀ : ℕ, ∃ c : ℝ, 0 < c ∧
      ∀ (Sig : Type) [Fintype Sig] [DecidableEq Sig], Fintype.card Sig ≤ m →
      ∀ (μ : Sig × Sig × Sig → ℝ) (ν : Sig → ℝ), IsDist μ →
        (∀ i : Fin 3, marginal μ i = ν) → (∀ x : Sig, μ (x, x, x) ≠ 0) →
        ¬ DistHasEmbedding ℤ μ → IsMinAtom μ α →
      ∀ (n B : ℕ), B₀ ≤ B →
      ∀ f : (Fin n → Sig) → ℝ, (∀ x, f x = 0 ∨ f x = 1) → Resilient ν B (1 / 2) f →
        δ ≤ expect (tensorPow ν n) f →
        α ^ (B + 1) * c ≤ Delta1 μ f := by
  obtain ⟨B₀, c, hc, H⟩ := lemma_5_27_uniform m α δ hα hδ
  refine ⟨B₀, c, hc, ?_⟩
  intro Sig _ _ hcard μ ν hμ hmarg hdiag hemb hmin n B hB f hf hres hdens
  exact H Sig hcard μ ν hμ hmarg hdiag hemb hmin.2.1 n B hB f hf hres hdens

end RestrictedAP.Counting
end

theorem solution : type_of% @RestrictedAP.Counting.chk_lemma_5_27 := @RestrictedAP.Counting.chk_lemma_5_27
