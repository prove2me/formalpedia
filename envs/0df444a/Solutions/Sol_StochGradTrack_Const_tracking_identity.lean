-- Prove2me | solution 1 for StochGradTrack.Const.tracking_identity
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:24:34.956713+00:00
-- url     : https://prove2.me/submissions/0fa6b966-6714-4788-b231-2508e63afeb2

import Mathlib
import Definitions.Def_StochGradTrack_Const_Model

set_option autoImplicit false
open StochGradTrack.Const

theorem solution {n p m : ℕ} {Ω : Type*} (α : ℝ) (W : Matrix (Fin n) (Fin n) ℝ)
    (g : Fin n → E p → E m → E p) (ξ : ℕ → Fin n → Ω → E m) (x0 : Stack n p)
    (hcol : ∀ j, ∑ i, W i j = 1) :
    ∀ k ω, avg (ys (fun _ => α) W g ξ x0 k ω) =
      (n : ℝ)⁻¹ • ∑ i, g i (xs (fun _ => α) W g ξ x0 k ω i) (ξ k i ω) := by
  have hmix : ∀ y : Stack n p, ∑ i, mix W y i = ∑ j, y j := by
    intro y
    unfold mix
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_smul, hcol j, one_smul]
  intro k
  induction k with
  | zero =>
    intro ω
    show avg (fun i => g i (x0 i) (ξ 0 i ω)) = _
    rfl
  | succ k ih =>
    intro ω
    have h := ih ω
    have e1 : ys (fun _ => α) W g ξ x0 (k + 1) ω = fun i => mix W (ys (fun _ => α) W g ξ x0 k ω) i +
        (g i (xs (fun _ => α) W g ξ x0 (k + 1) ω i) (ξ (k + 1) i ω)
          - g i (xs (fun _ => α) W g ξ x0 k ω i) (ξ k i ω)) := rfl
    rw [e1]
    unfold avg at h ⊢
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hmix, smul_add, smul_sub, h]
    abel
