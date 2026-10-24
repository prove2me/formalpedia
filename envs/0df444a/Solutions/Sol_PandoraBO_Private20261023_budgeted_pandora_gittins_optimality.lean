-- Prove2me | solution 1 for PandoraBO.Private20261023.budgeted_pandora_gittins_optimality
-- status  : ACCEPTED   (prove)
-- author  : @QianJaneXie
-- created : 2026-10-24T00:22:02.179123+00:00
-- url     : https://prove2.me/submissions/f972dd3b-741c-4b11-8c92-608348c71a1d

import Definitions.Def_PandoraBO_Model
import Theorems.Thm_PandoraBO_Private20261023_dual_convex_and_attains_minimum
import Theorems.Thm_PandoraBO_Private20261023_interior_dual_minimum_matches_budget
import Theorems.Thm_PandoraBO_Private20261023_optimal_face_gittins_cost_extrema
import Theorems.Thm_PandoraBO_Private20261023_weitzman_optimality
import Theorems.Thm_PandoraBO_Private20261023_zero_dual_minimum_feasible_gittins
import Theorems.Thm_PandoraBO_Private20261023_complementary_lagrangian_certificate
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
This is a tracked reduction, not an independent proof of the main theorem.
Its imported platform milestones remain proof obligations until independently
verified. In particular, neither exact budget matching nor the existence of a
feasible zero-index policy is added as an assumption to the target statement.
-/

set_option autoImplicit false

open PandoraBO

namespace PandoraBO.Private20261023.Reduction

/-- Every point of a real interval is a convex combination of its endpoints. -/
private theorem interval_combination (L B H : ℝ) (hL : L ≤ B) (hH : B ≤ H) :
    ∃ a : ℝ, 0 ≤ a ∧ a ≤ 1 ∧ a * L + (1 - a) * H = B := by
  by_cases hLH : L = H
  · refine ⟨1, zero_le_one, le_rfl, ?_⟩
    have hLB : L = B := by linarith
    simpa only [one_mul, sub_self, zero_mul, add_zero] using hLB
  · have hden : 0 < H - L := by
      have hstrict : L < H := lt_of_le_of_ne (le_trans hL hH) hLH
      exact sub_pos.mpr hstrict
    refine ⟨(H - B) / (H - L), div_nonneg (sub_nonneg.mpr hH) hden.le,
      (div_le_one hden).mpr (sub_le_sub_left hL H), ?_⟩
    field_simp [ne_of_gt hden]
    <;> ring

end PandoraBO.Private20261023.Reduction

/-- The full budgeted theorem follows from the listed private milestones. -/
theorem solution {n : ℕ} (M : Instance n)
    (B : ℝ) (hslater : ∃ i : Box n, M.cost i < B) :
    ∃ multiplier : ℝ, dualMinimizer M B multiplier ∧ ∃ π : Policy n,
      isGeneralizedGittinsPolicy M multiplier π ∧ optimal M multiplier π ∧
      complementarySlackness M B multiplier π ∧ budgetOptimal M B π := by
  obtain ⟨multiplier, hmin⟩ :=
    (PandoraBO.Private20261023.dual_convex_and_attains_minimum M B hslater).2
  by_cases hzero : multiplier = 0
  · subst multiplier
    obtain ⟨π, hindex, hfeasible, _hfull, hopt⟩ :=
      PandoraBO.Private20261023.zero_dual_minimum_feasible_gittins M B hmin
    have hcomp : complementarySlackness M B 0 π := by
      simp only [complementarySlackness, zero_mul]
    refine ⟨0, hmin, π, Or.inr ⟨rfl, hindex⟩, hopt, hcomp, ?_⟩
    exact PandoraBO.Private20261023.complementary_lagrangian_certificate
      M B 0 le_rfl π hopt hfeasible hcomp
  · have hpos : 0 < multiplier := lt_of_le_of_ne hmin.1 (Ne.symm hzero)
    obtain ⟨ρ, hρopt, hρcost⟩ :=
      PandoraBO.Private20261023.interior_dual_minimum_matches_budget
        M B multiplier hslater hmin hpos
    obtain ⟨low, high, _hlow, _hhigh, hextrema, hmix⟩ :=
      PandoraBO.Private20261023.optimal_face_gittins_cost_extrema M multiplier hpos
    have hbounds := hextrema ρ hρopt
    rw [hρcost] at hbounds
    obtain ⟨a, ha0, ha1, haB⟩ :=
      PandoraBO.Private20261023.Reduction.interval_combination
        (expectedCost M low) B (expectedCost M high) hbounds.1 hbounds.2
    obtain ⟨π, hindex, hcost⟩ := hmix a ha0 ha1
    have htight : expectedCost M π = B := hcost.trans haB
    have hopt : optimal M multiplier π :=
      (PandoraBO.Private20261023.weitzman_optimality M multiplier hpos).2 π hindex
    have hfeasible : budgetFeasible M B π := htight.le
    have hcomp : complementarySlackness M B multiplier π := by
      simp only [complementarySlackness, htight, sub_self, mul_zero]
    refine ⟨multiplier, hmin, π, Or.inl ⟨hpos, hindex⟩, hopt, hcomp, ?_⟩
    exact PandoraBO.Private20261023.complementary_lagrangian_certificate
      M B multiplier hpos.le π hopt hfeasible hcomp
