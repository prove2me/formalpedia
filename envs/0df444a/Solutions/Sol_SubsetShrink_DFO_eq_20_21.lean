-- Prove2me | solution 1 for SubsetShrink.DFO.eq_20_21
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:11:15.991029+00:00
-- url     : https://prove2.me/submissions/916239a5-c9fc-4a19-a4ac-86e8f70a7f3c

import Mathlib
import Definitions.Def_SubsetShrink_DFO_Model

set_option autoImplicit false
open SubsetShrink.DFO

theorem solution {p : ℕ} (f : E p → ℝ) (L lam : ℝ) (q k : ℕ)
    (hq : q = 1 ∨ q = 2) (hk : 1 ≤ k) (hLpos : 0 < L) (β : E p) :
    (∀ η : E p, QL f L η β + lam * lq q η =
        L / 2 * ‖η - (β - (1 / L) • gradient f β)‖ ^ 2 - 1 / (2 * L) * ‖gradient f β‖ ^ 2
          + f β + lam * lq q η) ∧
    (∀ ηhat : E p, IsThresh (β - (1 / L) • gradient f β) k (lam / L) q ηhat ↔
        (l0 ηhat ≤ k ∧ ∀ η : E p, l0 η ≤ k →
          QL f L ηhat β + lam * lq q ηhat ≤ QL f L η β + lam * lq q η)) := by
  have h1 : ∀ η : E p, QL f L η β + lam * lq q η =
        L / 2 * ‖η - (β - (1 / L) • gradient f β)‖ ^ 2 - 1 / (2 * L) * ‖gradient f β‖ ^ 2
          + f β + lam * lq q η := by
    intro η
    unfold QL
    have e : η - (β - (1 / L) • gradient f β) = (η - β) + (1 / L) • gradient f β := by abel
    rw [e, norm_add_sq_real, inner_smul_right, norm_smul, real_inner_comm]
    have hL : L ≠ 0 := hLpos.ne'
    rw [mul_pow, Real.norm_eq_abs, sq_abs]
    field_simp
    ring
  refine ⟨h1, ?_⟩
  intro ηhat
  have key : ∀ η : E p, QL f L η β + lam * lq q η =
      L * (1 / 2 * ‖η - (β - (1 / L) • gradient f β)‖ ^ 2 + lam / L * lq q η)
        + (f β - 1 / (2 * L) * ‖gradient f β‖ ^ 2) := by
    intro η
    rw [h1 η]
    have hL : L ≠ 0 := hLpos.ne'
    field_simp
    ring
  unfold IsThresh
  apply and_congr Iff.rfl
  apply forall_congr'
  intro η
  apply imp_congr Iff.rfl
  rw [key, key]
  constructor
  · intro h
    have := mul_le_mul_of_nonneg_left h hLpos.le
    linarith
  · intro h
    have := le_of_add_le_add_right h
    exact le_of_mul_le_mul_left this hLpos
