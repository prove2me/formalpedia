-- Prove2me | solution 1 for SuttonBartoRL.LinearTD.expected_td_update
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T14:04:55.610753+00:00
-- url     : https://prove2.me/submissions/59f00fa6-58b8-4a3b-b50c-3fb6669e545c

import Mathlib
import Definitions.Def_SuttonBartoRL_LinearTD_MDP
import Definitions.Def_SuttonBartoRL_LinearTD_LinearTD

set_option autoImplicit false

open Matrix SuttonBartoRL.LinearTD in
theorem solution {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] {d : ℕ}
    (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (μ : S → ℝ) (X : Matrix S (Fin d) ℝ) (γ α : ℝ)
    (hμsum : ∑ s, μ s = 1) (w : Fin d → ℝ) :
    ∑ s, μ s • ∑ a, π.prob s a • ∑ s', ∑ r ∈ M.R, M.p s a s' r • tdUpdate X γ α w s r s' =
      (1 - α • tdA M π μ X γ) *ᵥ w + α • tdB M π μ X := by
  have hAw : tdA M π μ X γ *ᵥ w = ∑ s, μ s • ∑ a, π.prob s a • ∑ s', ∑ r ∈ M.R,
      M.p s a s' r • (((X s - γ • X s') ⬝ᵥ w) • X s) := by
    simp only [tdA, Matrix.sum_mulVec, Matrix.smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul]
  have hp : ∀ s a (c : ℝ), ∑ s', ∑ r ∈ M.R, M.p s a s' r * c = c := fun s a c => by
    simp_rw [← Finset.sum_mul, M.p_sum, one_mul]
  have hπ : ∀ s (c : ℝ), ∑ a, π.prob s a * c = c := fun s c => by
    rw [← Finset.sum_mul, π.sum_one, one_mul]
  have hμ : ∀ (c : ℝ), ∑ s, μ s * c = c := fun c => by
    rw [← Finset.sum_mul, hμsum, one_mul]
  rw [sub_mulVec, one_mulVec, smul_mulVec, hAw]
  ext i
  have hw : w i = ∑ s, μ s * ∑ a, π.prob s a * ∑ s', ∑ r ∈ M.R, M.p s a s' r * w i := by
    simp only [hp, hπ, hμ]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, tdB, tdUpdate, smul_eq_mul]
  conv_rhs => rw [hw]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun s' _ => Finset.sum_congr rfl fun r _ => ?_
  simp only [sub_dotProduct, smul_dotProduct, smul_eq_mul, dotProduct_comm w]
  ring
