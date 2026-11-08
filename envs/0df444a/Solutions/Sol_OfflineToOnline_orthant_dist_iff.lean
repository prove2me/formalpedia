-- Prove2me | solution 1 for OfflineToOnline.orthant_dist_iff
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:43:21.442062+00:00
-- url     : https://prove2.me/submissions/d40d24fc-1542-4253-b283-a8a4079683b7

import Mathlib
import Definitions.Def_OfflineToOnline_orthant

open OfflineToOnline in
theorem solution (d T : ℕ) (hT : 1 ≤ T) (g : ℝ) (hg : 0 ≤ g) (u : ℕ → Fin d → ℝ) :
    Metric.infDist ((T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, u t) (OfflineToOnline.orthant d) ≤ g ↔
      ∀ j, -(T * g) ≤ ∑ t ∈ Finset.range T, u t j := by
  have hT0 : (0:ℝ) < T := by exact_mod_cast hT
  obtain ⟨v, hvdef⟩ : ∃ v : Fin d → ℝ, v = (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, u t := ⟨_, rfl⟩
  rw [← hvdef]
  have hv : ∀ j, v j = (T:ℝ)⁻¹ * ∑ t ∈ Finset.range T, u t j := by
    intro j; rw [hvdef]; simp [Finset.sum_apply]
  have hiff : ∀ j, (-(T * g) ≤ ∑ t ∈ Finset.range T, u t j ↔ -g ≤ v j) := by
    intro j
    rw [hv, le_inv_mul_iff₀ hT0]
    constructor <;> intro h <;> linarith
  simp only [hiff]
  constructor
  · intro h j
    by_contra hlt
    push_neg at hlt
    have hne : (OfflineToOnline.orthant d).Nonempty := ⟨0, fun j => le_rfl⟩
    have hlow : -(v j) ≤ Metric.infDist v (OfflineToOnline.orthant d) := by
      rw [Metric.le_infDist hne]
      intro y hy
      have hyj : 0 ≤ y j := hy j
      calc -(v j) ≤ y j - v j := by linarith
        _ ≤ |v j - y j| := by rw [abs_sub_comm]; exact le_abs_self _
        _ = dist (v j) (y j) := (Real.dist_eq _ _).symm
        _ ≤ dist v y := dist_le_pi_dist v y j
    linarith
  · intro h
    have hp : (fun j => max (v j) 0) ∈ OfflineToOnline.orthant d := fun j => le_max_right _ _
    calc Metric.infDist v (OfflineToOnline.orthant d) ≤ dist v (fun j => max (v j) 0) :=
          Metric.infDist_le_dist_of_mem hp
      _ ≤ g := by
        refine (dist_pi_le_iff hg).2 (fun j => ?_)
        rw [Real.dist_eq]
        rcases le_total (v j) 0 with h1 | h1
        · rw [max_eq_right h1, sub_zero, abs_of_nonpos h1]
          linarith [h j]
        · rw [max_eq_left h1, sub_self, abs_zero]
          exact hg
