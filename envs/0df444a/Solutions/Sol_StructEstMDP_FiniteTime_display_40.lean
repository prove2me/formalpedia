-- Prove2me | solution 1 for StructEstMDP.FiniteTime.display_40
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:38:53.072736+00:00
-- url     : https://prove2.me/submissions/b17fcec9-142c-4e94-a00b-429f96cf46e2

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_StructEstMDP_FiniteTime_Setting
set_option autoImplicit false

open FoundationsML.ReinforcementLearning MeasureTheory StructEstMDP.FiniteTime

theorem solution {S A : Type*} (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    {p : ℕ} (r : S → A → EuclideanSpace ℝ (Fin p) → ℝ) (Lr Lg : ℝ)
    (h3 : Assumption3 r Lr Lg)
    (θ : EuclideanSpace ℝ (Fin p)) (τ τ' : Traj S A) :
    ‖hGrad γ r θ τ - hGrad γ r θ τ'‖ ≤ 2 * (Lr / (1 - γ)) := by
  obtain ⟨hLr, -, h⟩ := h3
  have hb : ∀ (σ : Traj S A) (t : ℕ),
      ‖γ ^ t • gradient (r (σ t).1 (σ t).2) θ‖ ≤ Lr * γ ^ t := by
    intro σ t
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hγ0 t), mul_comm]
    exact mul_le_mul_of_nonneg_right ((h (σ t).1 (σ t).2).2.1 θ) (pow_nonneg hγ0 t)
  have hg : Summable (fun t : ℕ => Lr * γ ^ t) :=
    (summable_geometric_of_lt_one hγ0 hγ1).mul_left Lr
  have hs : ∀ σ : Traj S A,
      Summable (fun t : ℕ => γ ^ t • gradient (r (σ t).1 (σ t).2) θ) := fun σ =>
    Summable.of_norm_bounded hg (hb σ)
  unfold hGrad
  rw [← Summable.tsum_sub (hs τ) (hs τ')]
  have hG : HasSum (fun t : ℕ => 2 * Lr * γ ^ t) (2 * Lr * (1 - γ)⁻¹) :=
    (hasSum_geometric_of_lt_one hγ0 hγ1).mul_left (2 * Lr)
  have := tsum_of_norm_bounded hG (f := fun t : ℕ =>
    γ ^ t • gradient (r (τ t).1 (τ t).2) θ - γ ^ t • gradient (r (τ' t).1 (τ' t).2) θ) (fun t => by
    calc _ ≤ ‖γ ^ t • gradient (r (τ t).1 (τ t).2) θ‖ + ‖γ ^ t • gradient (r (τ' t).1 (τ' t).2) θ‖ := norm_sub_le _ _
      _ ≤ Lr * γ ^ t + Lr * γ ^ t := add_le_add (hb τ t) (hb τ' t)
      _ = 2 * Lr * γ ^ t := by ring)
  calc _ ≤ 2 * Lr * (1 - γ)⁻¹ := this
    _ = 2 * (Lr / (1 - γ)) := by rw [div_eq_mul_inv]; ring
