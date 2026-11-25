-- Prove2me | solution 1 for PI.SqPair.LCP.locCartanPair_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:42:58.613769+00:00
-- url     : https://prove2.me/submissions/75b1d2ed-29b7-4b8c-9c2e-eeaa243de201

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PiNonunit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_FiniteAdeleIdempotentOfFMulSelf
import Theorems.Thm_PI_SqPair_LCP_pgen_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.SqPair PI.SqPair.LCP
namespace PI.SqPair.LCP
theorem _root_.solution (h1 : Dichotomy) (hB : BaseLag) (hS : Step) :
    PI.SqPair.LocCartanPair := by
  intro R _ σ hσ R₀ hR₀ _ _ _ _ hθ ϖ hϖ N hN k h hh
  let _ : StarRing R :=
    { star := σ
      star_involutive := hσ
      star_mul := fun a b => by rw [map_mul, mul_comm]
      star_add := fun a b => map_add σ a b }
  have hR₀' : ∀ x, x ∈ R₀ ↔ star x = x := hR₀
  have hθ' : ∃ θ : R, IsUnit (θ - star θ) := hθ
  have hh' : hᴴ * 1 * h = ((ϖ : R) ^ (2 * k)) • (1 : Matrix (Fin N) (Fin N) R) := by
    rw [Matrix.mul_one]; exact hh
  rcases h1 R R₀ hR₀' hθ' ϖ hϖ with ⟨ε, hε, hεs⟩ | hI
  · refine ⟨ε • 1, ε • 1, ?_, ?_, ?_⟩
    · simp [smul_smul, hε]
    · change (ε • (1 : Matrix (Fin N) (Fin N) R))ᴴ = _
      rw [conjTranspose_smul, conjTranspose_one, hεs, sub_smul, one_smul]
    · simp
  · obtain ⟨e, f, he, heA, hef⟩ := pgen_main hB hS R₀ (ϖ : R) hI N (Fin N) (Fintype.card_fin N) hN
      1 1 h k ⟨⟨conjTranspose_one, by simp⟩, ⟨conjTranspose_one, by simp⟩, hh'⟩
    refine ⟨e, f, he, ?_, hef⟩
    rw [Matrix.mul_one, Matrix.one_mul] at heA
    exact heA
end PI.SqPair.LCP
