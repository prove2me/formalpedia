-- Prove2me | solution 1 for RobustSDP.Uniqueness.feasible_tau_pos
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T01:42:30.737437+00:00
-- url     : https://prove2.me/submissions/ba218ae1-585f-4072-b126-8a736659e727

import Mathlib
import Definitions.Def_RobustSDP_Uniqueness_Model
import Definitions.Def_RobustSDP_Uniqueness_Hypotheses

open Matrix
open RobustSDP.Uniqueness

private theorem block_quad {n q : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (Rm : Matrix (Fin q) (Fin n) ℝ) (τ : ℝ) (ξ : Fin n → ℝ) (w : Fin q → ℝ) :
    Sum.elim ξ w ⬝ᵥ
        ((fromBlocks A Rmᵀ Rm (τ • (1 : Matrix (Fin q) (Fin q) ℝ))) *ᵥ Sum.elim ξ w)
      = ξ ⬝ᵥ (A *ᵥ ξ) + 2 * (w ⬝ᵥ (Rm *ᵥ ξ)) + τ * (w ⬝ᵥ w) := by
  rw [fromBlocks_mulVec, dotProduct_block]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, dotProduct_add, dotProduct_smul,
    smul_eq_mul]
  have h1 : ξ ⬝ᵥ (Rmᵀ *ᵥ w) = w ⬝ᵥ (Rm *ᵥ ξ) := by
    rw [dotProduct_mulVec, vecMul_transpose, dotProduct_comm]
  have h2 : w ⬝ᵥ ((τ • (1 : Matrix (Fin q) (Fin q) ℝ)) *ᵥ w) = τ * (w ⬝ᵥ w) := by
    rw [smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]
  rw [h1, h2]
  ring

theorem solution {m n p q : ℕ} (D : SDPData m n p q) (h3a : D.H3a)
    (y : (Fin m → ℝ) × ℝ) (hy : D.Feasible y) :
    0 < y.2 := by
  obtain ⟨N, hN, hker⟩ := h3a
  by_contra hτ
  rw [not_lt] at hτ
  have hlmi : D.lmi y.1 y.2
      = fromBlocks (D.F y.1 - y.2 • (D.L * D.Lᵀ)) (D.R y.1)ᵀ (D.R y.1)
          (y.2 • (1 : Matrix (Fin q) (Fin q) ℝ)) := rfl
  have hRzero : ∀ ξ : Fin n → ℝ, (D.R y.1) *ᵥ ξ = 0 := by
    intro ξ
    have hann : 0 ≤ ((D.R y.1) *ᵥ ξ) ⬝ᵥ ((D.R y.1) *ᵥ ξ) := by
      simp only [dotProduct]
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    by_contra hne
    have hapos : 0 < ((D.R y.1) *ᵥ ξ) ⬝ᵥ ((D.R y.1) *ᵥ ξ) := by
      rcases hann.lt_or_eq with h | h
      · exact h
      · exact absurd (dotProduct_self_eq_zero.mp h.symm) hne
    set a := ((D.R y.1) *ᵥ ξ) ⬝ᵥ ((D.R y.1) *ᵥ ξ) with hadef
    set c0 := ξ ⬝ᵥ ((D.F y.1 - y.2 • (D.L * D.Lᵀ)) *ᵥ ξ) with hc0def
    set t : ℝ := -((|c0| + 1) / (2 * a)) with htdef
    have hps := hy.dotProduct_mulVec_nonneg (Sum.elim ξ (t • ((D.R y.1) *ᵥ ξ)))
    rw [star_trivial, hlmi, block_quad] at hps
    have e1 : (t • ((D.R y.1) *ᵥ ξ)) ⬝ᵥ ((D.R y.1) *ᵥ ξ) = t * a := by
      rw [smul_dotProduct, smul_eq_mul, hadef]
    have e2 : (t • ((D.R y.1) *ᵥ ξ)) ⬝ᵥ (t • ((D.R y.1) *ᵥ ξ)) = t ^ 2 * a := by
      rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, hadef]
      ring
    rw [e1, e2, ← hc0def] at hps
    have hta : 2 * (t * a) = -(|c0| + 1) := by
      rw [htdef]
      field_simp
    have hneg : y.2 * (t ^ 2 * a) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hτ (by positivity)
    have habs : c0 ≤ |c0| := le_abs_self c0
    linarith [hps, hta, hneg, habs]
  have hpencil : D.pencil 1 y.1 = D.R y.1 := by
    unfold SDPData.pencil SDPData.R
    rw [one_smul]
  have hzero : Matrix.toLin' (D.pencil 1 y.1) = 0 := by
    refine LinearMap.ext fun ξ => ?_
    show (D.pencil 1 y.1) *ᵥ ξ = 0
    rw [hpencil]
    exact hRzero ξ
  have htop : LinearMap.ker (Matrix.toLin' (D.pencil 1 y.1)) = ⊤ :=
    LinearMap.ker_eq_top.mpr hzero
  have := hker 1 y.1 (Or.inl one_ne_zero)
  rw [htop] at this
  exact hN this.symm
