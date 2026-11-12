-- Prove2me | solution 1 for RamseyDisambig.Spherical.theorem_13
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:03:11.208234+00:00
-- url     : https://prove2.me/submissions/7721e6f6-6f0b-4d55-92fd-25c2fa2bae71
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RamseyDisambig_Spherical_Torus
import Definitions.Def_NatureSLT_GrowthFunction_vcDim
import Theorems.Thm_RamseyDisambig_Spherical_lemma_8
import Theorems.Thm_RamseyDisambig_Spherical_lemma_10
import Theorems.Thm_RamseyDisambig_Spherical_lemma_12

section
set_option autoImplicit false

namespace RamseyDisambig.Spherical

theorem chk_theorem_13 (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2) (q : ℕ) (hq : 1 ≤ q) :
    ∃ (N : ℕ) (R : ℕ+), 1 ≤ N ∧ 2 ≤ (R : ℕ) ∧ Even (R : ℕ) ∧
      ∀ c : Torus R N → Torus R N → Bool,
        GapColoring ε torusDistance c → (q : ℕ∞) ≤ NatureSLT.GrowthFunction.vcDim c := by
  obtain ⟨n, R, hn, hR2, hRe, h8⟩ := lemma_8 (ε / 2) (by linarith) (by linarith) q hq
  obtain ⟨N, hN, h12⟩ := lemma_12 ε hε hεhalf R n hn
  refine ⟨N, R, hN, hR2, hRe, fun c hc => ?_⟩
  obtain ⟨ι₁, ι₂, hg, hcan⟩ := h12 c hc
  exact lemma_10 ι₁ ι₂ c q hq (h8 _ hg hcan)

end RamseyDisambig.Spherical
end

theorem solution : type_of% @RamseyDisambig.Spherical.chk_theorem_13 := @RamseyDisambig.Spherical.chk_theorem_13
