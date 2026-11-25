-- Prove2me | solution 1 for PI.SqPair.LCP.sel_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:33:32.864797+00:00
-- url     : https://prove2.me/submissions/75655181-58eb-4567-956a-bae6c4fe01c3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_SelCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_SelMain
import Theorems.Thm_PI_SqPair_LCP_sel_dual
import Theorems.Thm_PI_SqPair_LCP_sel_factor
import Theorems.Thm_PI_SqPair_LCP_sel_form
import Theorems.Thm_PI_SqPair_LCP_sel_inv
import Theorems.Thm_PI_SqPair_LCP_sel_le
import Theorems.Thm_PI_SqPair_LCP_sel_unit_of_rel


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
    (hval : ∀ x : R, x ≠ 0 → ∃ n : ℕ, ∃ u : R, IsUnit u ∧ x = ϖ ^ n * u)
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A A' h : Matrix ι ι R) (hA : IsUnit A.det) (hA' : IsUnit A'.det) (k : ℕ)
    (hrel : (h.map σ)ᵀ * A * h = ϖ ^ (2 * k) • A') :
    ∃ (m : ℕ) (h₁ : Matrix ι ι R), h = ϖ ^ m • h₁ ∧ m ≤ k ∧
      (h₁.map σ)ᵀ * A * h₁ = ϖ ^ (2 * (k - m)) • A' ∧
      ((m = k ∧ IsUnit h₁.det) ∨
       (m < k ∧ ∃ (g₁ : Matrix ι ι R) (j : ι) (y : ι → R),
          g₁ * h₁ = ϖ ^ (2 * (k - m)) • 1 ∧ h₁ * g₁ = ϖ ^ (2 * (k - m)) • 1 ∧
          (∃ i, IsUnit ((h₁ *ᵥ Pi.single j 1) i)) ∧
          (fun l => σ ((h₁ *ᵥ Pi.single j 1) l)) ⬝ᵥ (A *ᵥ y) = 1 ∧
          (fun l => σ ((h₁ *ᵥ Pi.single j 1) l)) ⬝ᵥ (A *ᵥ (h₁ *ᵥ Pi.single j 1)) =
            ϖ ^ (2 * (k - m)) * A' j j ∧
          ϖ ^ (2 * (k - m)) • y = h₁ *ᵥ (g₁ *ᵥ y))) := by
  have hc : ∀ n : ℕ, ϖ ^ n ≠ 0 := fun n => pow_ne_zero n hϖ0
  have hh : h ≠ 0 := by
    rintro rfl
    have h0 : ϖ ^ (2 * k) • A' = 0 := by rw [← hrel]; simp
    rcases smul_eq_zero.1 h0 with h2 | h2
    · exact hc _ h2
    · rw [h2, Matrix.det_zero] at hA'
      exact not_isUnit_zero hA'
  obtain ⟨m, h₁, i, j, rfl, hu⟩ := sel_factor ϖ hϖ0 hval h hh
  obtain ⟨hmk, hrel₁⟩ := sel_le σ ϖ hϖ0 hϖ hσϖ A A' h₁ hA' m k hrel
  refine ⟨m, h₁, rfl, hmk, hrel₁, ?_⟩
  rcases Nat.lt_or_ge m k with hlt | hge
  · right
    refine ⟨hlt, ?_⟩
    obtain ⟨hg1, hg2⟩ := sel_inv σ A A' h₁ hA' (hc _) hrel₁
    have hxi : IsUnit ((h₁ *ᵥ Pi.single j 1) i) := by simpa [Matrix.mulVec_single] using hu
    obtain ⟨y, hy⟩ := sel_dual σ A hA (h₁ *ᵥ Pi.single j 1) i hxi
    refine ⟨A'⁻¹ * (h₁.map σ)ᵀ * A, j, y, hg1, hg2, ⟨i, hxi⟩, hy, ?_, ?_⟩
    · rw [sel_form σ A h₁ (Pi.single j 1) (Pi.single j 1), hrel₁]
      have hs : (fun l : ι => σ ((Pi.single j (1 : R) : ι → R) l)) = (Pi.single j 1 : ι → R) := by
        funext l
        by_cases hl : l = j
        · subst hl
          simp
        · simp [Pi.single_apply, hl]
      rw [hs]
      simp [Matrix.mulVec_single, dotProduct, Pi.single_apply]
    · rw [Matrix.mulVec_mulVec, hg2, Matrix.smul_mulVec, Matrix.one_mulVec]
  · left
    have hm : m = k := le_antisymm hmk hge
    subst hm
    refine ⟨rfl, ?_⟩
    rw [Nat.sub_self, mul_zero, pow_zero, one_smul] at hrel₁
    exact sel_unit_of_rel σ A A' h₁ hA' hrel₁
end PI.SqPair.LCP
