-- Prove2me | solution 1 for SmallGainISS.OmegaPath.lemma_8_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:37:35.736481+00:00
-- url     : https://prove2.me/submissions/3d98cfb6-40aa-48fd-a686-7be43e6151a1

import Mathlib
import Definitions.Def_SmallGainISS_OmegaPath_GainOperator

open scoped NNReal
open Filter Topology

open SmallGainISS.OmegaPath in
theorem solution {n : ℕ} (Γ : SmallGainISS.Lyapunov.GainMatrix n) (μ : Fin n → (Fin n → ℝ≥0) → ℝ≥0)
    (hΓ : ∀ i j, SmallGainISS.Lyapunov.IsKOrZero (Γ i j)) (hdiag : SmallGainISS.Lyapunov.ZeroDiagonal Γ) (hrows : NoZeroRows Γ)
    (hμ : ∀ i, SmallGainISS.Lyapunov.IsMAF (μ i)) (hcomp : Compatible Γ μ)
    (s : Fin n → ℝ≥0) (hpos : SPos s) (hs : s ∈ SmallGainISS.Lyapunov.Omega (gainOp Γ μ)) :
    (SPos (gainOp Γ μ s) ∧ gainOp Γ μ s ∈ SmallGainISS.Lyapunov.Omega (gainOp Γ μ)) ∧
    ∀ l : ℝ≥0, l ≤ 1 → l • s + (1 - l) • gainOp Γ μ s ∈ SmallGainISS.Lyapunov.Omega (gainOp Γ μ) := by
  have hK : ∀ i j, Γ i j ≠ 0 → SmallGainISS.Lyapunov.IsK (Γ i j) := by
    intro i j h
    rcases hΓ i j with h1 | h1
    · exact h1
    · exact absurd h1 h
  have hTmono : ∀ v w : Fin n → ℝ≥0, (∀ j, v j < w j) → ∀ i, gainOp Γ μ v i < gainOp Γ μ w i := by
    intro v w hvw i
    apply hcomp i (hrows i)
    · intro j hj; rw [hj]; rfl
    · intro j hj; rw [hj]; rfl
    · intro j hj; exact (hK i j hj).2.1 (hvw j)
  have hs' : ∀ i, gainOp Γ μ s i < s i := hs
  have hTpos : SPos (gainOp Γ μ s) := by
    intro i
    obtain ⟨j, hj⟩ := hrows i
    apply (hμ i).2.1
    intro h0
    have := congrFun h0 j
    simp only [Pi.zero_apply] at this
    have hk := hK i j hj
    have : Γ i j 0 < Γ i j (s j) := hk.2.1 (hpos j)
    rw [hk.2.2] at this
    simp_all
  have hTT : gainOp Γ μ s ∈ SmallGainISS.Lyapunov.Omega (gainOp Γ μ) := hTmono _ _ hs'
  refine ⟨⟨hTpos, hTT⟩, ?_⟩
  intro l hl
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ l) with h0 | h0
  · subst h0
    simp only [zero_smul, tsub_zero, one_smul, zero_add]
    exact hTT
  rcases eq_or_lt_of_le hl with h1 | h1
  · subst h1
    simp only [one_smul, tsub_self, zero_smul, add_zero]
    exact hs
  -- 0 < l < 1
  set sl := l • s + (1 - l) • gainOp Γ μ s with hsl
  have hlow : ∀ j, gainOp Γ μ s j < sl j := by
    intro j
    simp only [hsl, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← NNReal.coe_lt_coe]
    push_cast [NNReal.coe_sub hl]
    have := NNReal.coe_lt_coe.mpr (hs' j)
    have hl0 : (0 : ℝ) < l := NNReal.coe_pos.mpr h0
    nlinarith
  have hup : ∀ j, sl j < s j := by
    intro j
    simp only [hsl, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← NNReal.coe_lt_coe]
    push_cast [NNReal.coe_sub hl]
    have := NNReal.coe_lt_coe.mpr (hs' j)
    have hl1 : (l : ℝ) < 1 := by exact_mod_cast h1
    nlinarith
  intro i
  exact lt_trans (hTmono sl s hup i) (hlow i)
