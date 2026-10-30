-- Prove2me | solution 1 for SLPEPricing.Regret.containment
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T04:30:49.772052+00:00
-- url     : https://prove2.me/submissions/3b60b722-4bb1-40ef-b3b7-75bc37f0467d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SLPEPricing_Regret_Model
import Theorems.Thm_SLPEPricing_Regret_lemma_4

open SLPEPricing.Regret

theorem solution (d : ℝ → ℝ) (pstar κ K₁ c μ ρ : ℝ) (h : Standing d pstar κ K₁ c μ ρ)
    (amax : (ℝ → ℝ) → ℝ → ℝ → ℝ) (hamax : IsArgmaxSelector amax)
    (sel : ℕ → ℕ × ℕ × ℕ × ℕ) (ε : ℕ → ℝ) (T : ℕ) (hT : 2 ≤ T) (i : ℕ) (hi : 1 ≤ i)
    (hgood : ∀ j ∈ Finset.Ico 1 i,
      Assumption2At μ ρ T sel ε j ∧ ConcentrationAt d μ ρ amax sel ε T j) :
    pL d μ ρ amax sel ε T i ≤ pstar ∧ pstar ≤ pH d μ ρ amax sel ε T i := by
  rcases Nat.lt_or_ge i 2 with hlt | hge
  · have hi1 : i = 1 := by omega
    subst hi1
    have hc : centre d μ ρ amax sel ε T 1 = 1 / 2 := rfl
    have hD : Delta μ 1 = 1 / 2 := rfl
    unfold pL pH
    rw [hc, hD]
    constructor <;> linarith [h.pstar_pos, h.pstar_lt_one]
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have hj1 : 1 ≤ j := by omega
    have hgood' : ∀ j' ∈ Finset.Icc 1 j,
        Assumption2At μ ρ T sel ε j' ∧ ConcentrationAt d μ ρ amax sel ε T j' := by
      intro j' hj'
      apply hgood
      simp only [Finset.mem_Icc, Finset.mem_Ico] at hj' ⊢
      omega
    have h4 := lemma_4 d pstar κ K₁ c μ ρ h amax hamax sel ε T hT j hj1 hgood'
    have hcen : ptilde d μ ρ amax sel ε T j = centre d μ ρ amax sel ε T (j + 1) := rfl
    rw [hcen] at h4
    have hDs : Delta μ (j + 1) = μ * Delta μ j ^ 2 := by
      obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      rfl
    have hMle : Mconst c ρ K₁ κ * Delta μ j ^ 2 ≤ Delta μ (j + 1) := by
      rw [hDs]; exact mul_le_mul_of_nonneg_right h.mu_ge (sq_nonneg _)
    have habs := abs_le.mp (le_trans h4 hMle)
    unfold pL pH
    constructor <;> linarith [habs.1, habs.2]
