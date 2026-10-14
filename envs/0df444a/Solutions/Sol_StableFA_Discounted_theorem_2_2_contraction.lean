-- Prove2me | solution 1 for StableFA.Discounted.theorem_2_2_contraction
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T02:53:20.222125+00:00
-- url     : https://prove2.me/submissions/212a54de-d9b7-4592-aa87-c36ee36dded5

import Mathlib
import Definitions.Def_BertsekasSSPModel
import Definitions.Def_StableFA_Discounted_Setting

open Filter Topology
open StableFA.Discounted


theorem solution {n : ℕ} {C : Type} [Fintype C] (M : BertsekasSSPModel n C)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hp1 : ∀ i, ∀ u ∈ M.U i, ∑ j, M.p i u j = 1) :
    ∀ V W : Fin n → ℝ,
      ‖BertsekasDiscountedBellmanOp M γ V - BertsekasDiscountedBellmanOp M γ W‖ ≤
        γ * ‖V - W‖ := by
  classical
  have hdir (V W : Fin n → ℝ) (i : Fin n) :
      BertsekasDiscountedBellmanOp M γ V i ≤
        BertsekasDiscountedBellmanOp M γ W i + γ * ‖V - W‖ := by
    obtain ⟨u, hu, hmin⟩ := Finset.exists_mem_eq_inf' (M.hU i)
      (fun u => M.g i u + γ * ∑ j, M.p i u j * W j)
    have hsum : (∑ j, M.p i u j * V j) ≤
        (∑ j, M.p i u j * W j) + ‖V - W‖ := by
      calc
        (∑ j, M.p i u j * V j) =
            (∑ j, M.p i u j * W j) + ∑ j, M.p i u j * (V j - W j) := by
          simp only [mul_sub, Finset.sum_sub_distrib]
          ring
        _ ≤ (∑ j, M.p i u j * W j) + ∑ j, M.p i u j * ‖V - W‖ := by
          gcongr with j
          exact (M.hp_nonneg i u j)
          exact (le_abs_self (V j - W j)).trans (by simpa using norm_le_pi_norm (V-W) j)
        _ = (∑ j, M.p i u j * W j) + ‖V - W‖ := by
          rw [← Finset.sum_mul, hp1 i u hu, one_mul]
    calc
      BertsekasDiscountedBellmanOp M γ V i ≤ M.g i u + γ * ∑ j, M.p i u j * V j :=
        Finset.inf'_le _ hu
      _ ≤ M.g i u + γ * ∑ j, M.p i u j * W j + γ * ‖V-W‖ := by
        nlinarith
      _ = BertsekasDiscountedBellmanOp M γ W i + γ * ‖V-W‖ := by
        rw [BertsekasDiscountedBellmanOp, hmin]
  intro V W
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hγ0 (norm_nonneg _))).2
  intro i
  change ‖BertsekasDiscountedBellmanOp M γ V i - BertsekasDiscountedBellmanOp M γ W i‖ ≤ _
  rw [Real.norm_eq_abs, abs_sub_le_iff]
  constructor
  · linarith [hdir V W i]
  · have h := hdir W V i
    rw [norm_sub_rev W V] at h
    linarith


