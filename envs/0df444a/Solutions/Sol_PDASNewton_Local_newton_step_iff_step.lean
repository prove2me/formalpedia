-- Prove2me | solution 1 for PDASNewton.Local.newton_step_iff_step
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:23:05.659218+00:00
-- url     : https://prove2.me/submissions/00a3df5d-c5bf-4f69-9c29-aed3071dd8aa

import Mathlib
import Definitions.Def_PDASNewton_Local_Setting
set_option autoImplicit false
open PDASNewton.Local Matrix

theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (f ψ : Fin n → ℝ)
    (c : ℝ) (hc : 0 < c) (y lam y' lam' : Fin n → ℝ) :
    GF A ψ c (y, lam) ((y', lam') - (y, lam)) = -Fmap A f ψ c (y, lam) ↔
      IsStep A f ψ c y lam y' lam' := by
  have hG : ∀ i, (GF A ψ c (y, lam) ((y', lam') - (y, lam))).2 i =
      (lam' i - lam i) - gm 0 (lam + c • (y - ψ)) i * ((lam' i - lam i) + c * (y' i - y i)) := by
    intro i
    simp [GF, Gm]
    ring
  have hF : ∀ i, (-Fmap A f ψ c (y, lam)).2 i = -(lam i - max 0 (lam i + c * (y i - ψ i))) := by
    intro i; simp [Fmap]
  have hG1 : (GF A ψ c (y, lam) ((y', lam') - (y, lam))).1 = A *ᵥ (y' - y) + (lam' - lam) := by
    simp [GF]
  have hF1 : (-Fmap A f ψ c (y, lam)).1 = -(A *ᵥ y + lam - f) := by simp [Fmap]
  have hz : ∀ i, (lam + c • (y - ψ)) i = lam i + c * (y i - ψ i) := by
    intro i; simp
  have hgpos : ∀ i, 0 < lam i + c * (y i - ψ i) → gm 0 (lam + c • (y - ψ)) i = 1 := by
    intro i h
    unfold gm
    rw [hz i, if_neg (not_lt.mpr h.le), if_pos h]
  have hgnp : ∀ i, lam i + c * (y i - ψ i) ≤ 0 → gm 0 (lam + c • (y - ψ)) i = 0 := by
    intro i h
    unfold gm
    rw [hz i]
    by_cases h' : lam i + c * (y i - ψ i) < 0
    · rw [if_pos h']
    · rw [if_neg h', if_neg (not_lt.mpr h)]; rfl
  have hmul : ∀ i, (A *ᵥ (y' - y) + (lam' - lam)) i = (A *ᵥ y') i - (A *ᵥ y) i + (lam' i - lam i) := by
    intro i; simp [Matrix.mulVec_sub]
  constructor
  · intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    rw [hG1, hF1] at h1
    refine ⟨?_, ?_, ?_⟩
    · funext i
      have := congrFun h1 i
      rw [hmul] at this
      simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply] at this ⊢
      linarith
    · intro i hi
      have := congrFun h2 i
      rw [hG, hF, hgpos i hi, max_eq_right hi.le] at this
      have h3 : c * (y' i - ψ i) = 0 := by nlinarith
      rcases mul_eq_zero.mp h3 with h4 | h4
      · exact absurd h4 hc.ne'
      · linarith
    · intro i hi
      have := congrFun h2 i
      rw [hG, hF, hgnp i hi, max_eq_left hi] at this
      linarith
  · rintro ⟨h1, h2, h3⟩
    refine Prod.ext ?_ ?_
    · rw [hG1, hF1]
      funext i
      have := congrFun h1 i
      rw [hmul]
      simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply] at this ⊢
      linarith
    · funext i
      rw [hG, hF]
      by_cases hi : 0 < lam i + c * (y i - ψ i)
      · rw [hgpos i hi, max_eq_right hi.le]
        have := h2 i hi
        rw [this]; ring
      · push_neg at hi
        rw [hgnp i hi, max_eq_left hi]
        have := h3 i hi
        rw [this]; ring
