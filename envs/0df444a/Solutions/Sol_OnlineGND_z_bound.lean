-- Prove2me | solution 1 for OnlineGND.z_bound
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T21:01:50.189821+00:00
-- url     : https://prove2.me/submissions/b4584430-3cb8-45c6-a9bb-2a286b604d47

import Definitions.Def_OnlineGND_DualFitting

namespace Aux_OnlineGND_z_bound

theorem edge (c a M ρ A : ℝ) (hc : 0 ≤ c) (ha : 1 < a) (haM : a ≤ M) (hρ : 1 ≤ ρ) (hA : 0 ≤ A) :
    c * a / (a / (a - 1)) * (1 / ρ * A ^ (a - 1)) ^ (a / (a - 1)) ≤
      ρ ^ (-(M / (M - 1))) * (M - 1) * (c * A ^ a) := by
  have ha1 : 0 < a - 1 := by linarith
  have hne : a - 1 ≠ 0 := ne_of_gt ha1
  have ha0 : a ≠ 0 := by linarith
  have hρ0 : 0 ≤ ρ := by linarith
  have hexp : (a - 1) * (a / (a - 1)) = a := by
    rw [mul_div_assoc']; exact mul_div_cancel_left₀ a hne
  have hz : (1 / ρ * A ^ (a - 1)) ^ (a / (a - 1)) = ρ ^ (-(a / (a - 1))) * A ^ a := by
    rw [Real.mul_rpow (show (0 : ℝ) ≤ 1 / ρ by rw [one_div]; exact inv_nonneg.mpr hρ0) (Real.rpow_nonneg hA _), ← Real.rpow_mul hA, one_div,
      Real.inv_rpow hρ0, ← Real.rpow_neg hρ0, hexp]
  have hcoef : c * a / (a / (a - 1)) = c * (a - 1) := by
    rw [div_div_eq_mul_div, mul_comm c a, mul_assoc, mul_div_cancel_left₀ _ ha0]
  rw [hcoef, hz]
  have hB : M / (M - 1) ≤ a / (a - 1) := by
    rw [div_le_div_iff₀ (by linarith) ha1]
    nlinarith
  have h1 : ρ ^ (-(a / (a - 1))) ≤ ρ ^ (-(M / (M - 1))) :=
    Real.rpow_le_rpow_of_exponent_le hρ (neg_le_neg hB)
  have h2 : 0 ≤ ρ ^ (-(a / (a - 1))) := Real.rpow_nonneg hρ0 _
  have h3 : 0 ≤ c * A ^ a := mul_nonneg hc (Real.rpow_nonneg hA _)
  calc c * (a - 1) * (ρ ^ (-(a / (a - 1))) * A ^ a)
      = ((a - 1) * ρ ^ (-(a / (a - 1)))) * (c * A ^ a) := by ring
    _ ≤ ((M - 1) * ρ ^ (-(M / (M - 1)))) * (c * A ^ a) := by
        apply mul_le_mul_of_nonneg_right _ h3
        exact mul_le_mul (by linarith) h1 h2 (by linarith)
    _ = ρ ^ (-(M / (M - 1))) * (M - 1) * (c * A ^ a) := by ring

end Aux_OnlineGND_z_bound

open OnlineGND in
theorem solution {E : Type*} [Fintype E] [DecidableEq E] (c α : E → ℝ) (hc : ∀ e, 0 ≤ c e)
    (hα : ∀ e, 1 ≤ α e) (ρ : ℝ) (hρ : 1 ≤ ρ) (A : E → ℝ) (hA : ∀ e, 0 ≤ A e) :
    ∑ e ∈ Finset.univ.filter (fun e => α e ≠ 1),
        c e * α e / conjExp α e * zVar α ρ A e ^ conjExp α e ≤
      ρ ^ (-(alphaMax α / (alphaMax α - 1))) * (alphaMax α - 1) * costH c α A := by
  unfold costH
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e he
  have hne : α e ≠ 1 := (Finset.mem_filter.mp he).2
  have ha : 1 < α e := lt_of_le_of_ne (hα e) (Ne.symm hne)
  have haM : α e ≤ alphaMax α := by
    unfold alphaMax
    rw [Finset.le_fold_max]
    exact Or.inr ⟨e, Finset.mem_univ _, le_rfl⟩
  unfold conjExp zVar
  rw [if_neg hne]
  exact Aux_OnlineGND_z_bound.edge (c e) (α e) (alphaMax α) ρ (A e) (hc e) ha haM hρ (hA e)
