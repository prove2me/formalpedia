-- Prove2me | solution 1 for PI.SqPair.LCP.sel_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:27:21.309837+00:00
-- url     : https://prove2.me/submissions/88acbb4b-2dad-4302-baa5-5f073791c8de

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_SelCore
import Theorems.Thm_PI_SqPair_LCP_sel_star_smul
import Theorems.Thm_PI_SqPair_LCP_sel_smul_cancel

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
variable {R : Type} [CommRing R] [IsDomain R]
namespace PI.SqPair.LCP
theorem _root_.solution (σ : R ≃+* R) (ϖ : R) (hϖ0 : ϖ ≠ 0) (hϖ : ¬ IsUnit ϖ) (hσϖ : σ ϖ = ϖ)
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A A' h₁ : Matrix ι ι R) (hA' : IsUnit A'.det) (m k : ℕ)
    (hrel : ((ϖ ^ m • h₁).map σ)ᵀ * A * (ϖ ^ m • h₁) = ϖ ^ (2 * k) • A') :
    m ≤ k ∧ (h₁.map σ)ᵀ * A * h₁ = ϖ ^ (2 * (k - m)) • A' := by
  have hB : ϖ ^ (2 * m) • ((h₁.map σ)ᵀ * A * h₁) = ϖ ^ (2 * k) • A' := by
    rw [← hrel, sel_star_smul σ ϖ hσϖ]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_add, two_mul]
  have hp0 : ∀ t : ℕ, ϖ ^ t ≠ 0 := fun t => pow_ne_zero _ hϖ0
  by_cases hmk : m ≤ k
  · refine ⟨hmk, sel_smul_cancel (hp0 (2 * m)) ?_⟩
    rw [hB, smul_smul, ← pow_add]
    congr 2
    omega
  · exfalso
    push_neg at hmk
    have h2 : ϖ ^ (2 * k) • (ϖ ^ (2 * (m - k)) • ((h₁.map σ)ᵀ * A * h₁)) = ϖ ^ (2 * k) • A' := by
      rw [smul_smul, ← pow_add, ← hB]
      congr 2
      omega
    have h3 := sel_smul_cancel (hp0 (2 * k)) h2
    have h4 := congrArg Matrix.det h3
    rw [Matrix.det_smul] at h4
    rw [← h4] at hA'
    have h5 : IsUnit ((ϖ ^ (2 * (m - k))) ^ Fintype.card ι) := isUnit_of_mul_isUnit_left hA'
    rw [← pow_mul] at h5
    have hpos : 2 * (m - k) * Fintype.card ι ≠ 0 :=
      Nat.pos_iff_ne_zero.mp (Nat.mul_pos (by omega) Fintype.card_pos)
    exact hϖ ((isUnit_pow_iff hpos).mp h5)
end PI.SqPair.LCP
