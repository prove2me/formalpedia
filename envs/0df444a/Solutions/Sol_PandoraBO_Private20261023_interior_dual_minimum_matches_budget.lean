-- Prove2me | solution 1 for PandoraBO.Private20261023.interior_dual_minimum_matches_budget
-- status  : ACCEPTED   (prove)
-- author  : @QianJaneXie
-- created : 2026-10-24T00:48:43.656281+00:00
-- url     : https://prove2.me/submissions/00095dde-48f7-40f9-8ac7-536081985545

import Definitions.Def_PandoraBO_Model
import Theorems.Thm_PandoraBO_Private20261023_monotone_multiplier_optimal_policy_limit
import Theorems.Thm_PandoraBO_Private20261023_optimal_face_gittins_cost_extrema
import Theorems.Thm_PandoraBO_Private20261023_weitzman_optimality
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Tracked reduction of interior budget matching to two-sided monotone policy
limits, Weitzman optimality, and mixing within the Gittins optimal face.
The open limit and extremal-policy milestones remain independent obligations.
-/

set_option autoImplicit false

open PandoraBO Filter

namespace PandoraBO.Private20261023.Reduction

private theorem optimalValue_eq {n : ℕ} (M : Instance n)
    (multiplier : ℝ) (π : Policy n) (hopt : optimal M multiplier π) :
    optimalValue M multiplier = value M multiplier π := by
  unfold optimalValue
  apply le_antisymm
  · refine csSup_le ?_ ?_
    · exact ⟨value M multiplier π, π, rfl⟩
    · rintro r ⟨ρ, rfl⟩
      exact hopt ρ
  · apply le_csSup
    · refine ⟨value M multiplier π, ?_⟩
      rintro r ⟨ρ, rfl⟩
      exact hopt ρ
    · exact ⟨π, rfl⟩

private theorem cost_side {n : ℕ} (M : Instance n) (B multiplier t : ℝ)
    (hmin : dualMinimizer M B multiplier) (ht : 0 ≤ t)
    (π ρ : Policy n) (hπ : optimal M multiplier π) (hρ : optimal M t ρ) :
    (t - multiplier) * (expectedCost M ρ - B) ≤ 0 := by
  have hdual := hmin.2 t ht
  change optimalValue M multiplier + multiplier * B ≤
    optimalValue M t + t * B at hdual
  rw [optimalValue_eq M multiplier π hπ, optimalValue_eq M t ρ hρ] at hdual
  have hcomparison := hπ ρ
  simp only [value] at hdual hcomparison
  nlinarith

private theorem interval_combination (L B H : ℝ) (hL : L ≤ B) (hH : B ≤ H) :
    ∃ a : ℝ, 0 ≤ a ∧ a ≤ 1 ∧ a * L + (1 - a) * H = B := by
  by_cases hLH : L = H
  · refine ⟨1, zero_le_one, le_rfl, ?_⟩
    have hLB : L = B := by linarith
    simpa only [one_mul, sub_self, zero_mul, add_zero] using hLB
  · have hden : 0 < H - L := sub_pos.mpr (lt_of_le_of_ne (le_trans hL hH) hLH)
    refine ⟨(H - B) / (H - L), div_nonneg (sub_nonneg.mpr hH) hden.le,
      (div_le_one hden).mpr (sub_le_sub_left hL H), ?_⟩
    field_simp [ne_of_gt hden]
    <;> ring

end PandoraBO.Private20261023.Reduction

theorem solution {n : ℕ} (M : Instance n)
    (B multiplier : ℝ) (_hslater : ∃ i : Box n, M.cost i < B)
    (hmin : dualMinimizer M B multiplier) (hpos : 0 < multiplier) :
    ∃ π : Policy n, optimal M multiplier π ∧ expectedCost M π = B := by
  let q : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hqpos : ∀ k, 0 < q k := by
    intro k
    dsimp [q]
    positivity
  have hqle : ∀ k, q k ≤ 1 := by
    intro k
    apply (div_le_one (by positivity : 0 < (k : ℝ) + 1)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hqmono : Antitone q := by
    intro i j hij
    apply one_div_le_one_div_of_le (by positivity)
    have hcast : (i : ℝ) ≤ (j : ℝ) := Nat.cast_le.mpr hij
    linarith
  have hqlim : Tendsto q atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let eps : ℕ → ℝ := fun k => (multiplier / 2) * q k
  have hhalf : 0 < multiplier / 2 := by linarith
  have hepspos : ∀ k, 0 < eps k := fun k => mul_pos hhalf (hqpos k)
  have hepsle : ∀ k, eps k ≤ multiplier / 2 := by
    intro k
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hqle k) hhalf.le
  have hepsmono : Antitone eps := by
    intro i j hij
    exact mul_le_mul_of_nonneg_left (hqmono hij) hhalf.le
  have hepslim : Tendsto eps atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hqlim : Tendsto
        (fun k => (multiplier / 2) * q k) atTop (nhds ((multiplier / 2) * 0)))
  let above : ℕ → ℝ := fun k => multiplier + eps k
  let below : ℕ → ℝ := fun k => multiplier - eps k
  have habovepos : ∀ k, 0 < above k := fun k => add_pos hpos (hepspos k)
  have hbelowpos : ∀ k, 0 < below k := by
    intro k
    change 0 < multiplier - eps k
    linarith [hepsle k]
  have habovemono : Antitone above := by
    intro i j hij
    change multiplier + eps j ≤ multiplier + eps i
    linarith [hepsmono hij]
  have hbelowmono : Monotone below := by
    intro i j hij
    exact sub_le_sub_left (hepsmono hij) multiplier
  have habovelim : Tendsto above atTop (nhds multiplier) := by
    simpa only [add_zero] using
      (tendsto_const_nhds.add hepslim : Tendsto
        (fun k => multiplier + eps k) atTop (nhds (multiplier + 0)))
  have hbelowlim : Tendsto below atTop (nhds multiplier) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds.sub hepslim : Tendsto
        (fun k => multiplier - eps k) atTop (nhds (multiplier - 0)))
  obtain ⟨refPolicy, hrefindex⟩ :=
    (PandoraBO.Private20261023.weitzman_optimality M multiplier hpos).1
  have hrefopt : optimal M multiplier refPolicy :=
    (PandoraBO.Private20261023.weitzman_optimality M multiplier hpos).2
      refPolicy hrefindex
  obtain ⟨cheapSeq, cheap, hcheapindices, hcheapindex, hcheaplim, _hcheapreward⟩ :=
    PandoraBO.Private20261023.monotone_multiplier_optimal_policy_limit
      M above multiplier habovepos hpos (Or.inr habovemono) habovelim
  obtain ⟨expensiveSeq, expensive, hexpindices, hexpindex, hexplim, _hexpreward⟩ :=
    PandoraBO.Private20261023.monotone_multiplier_optimal_policy_limit
      M below multiplier hbelowpos hpos (Or.inl hbelowmono) hbelowlim
  have hcheapbound : ∀ k, expectedCost M (cheapSeq k) ≤ B := by
    intro k
    have hopt := (PandoraBO.Private20261023.weitzman_optimality
      M (above k) (habovepos k)).2 (cheapSeq k) (hcheapindices k)
    have hside := PandoraBO.Private20261023.Reduction.cost_side
      M B multiplier (above k) hmin (habovepos k).le
        refPolicy (cheapSeq k) hrefopt hopt
    have hdiff : 0 < above k - multiplier := by
      change 0 < multiplier + eps k - multiplier
      linarith [hepspos k]
    exact sub_nonpos.mp (nonpos_of_mul_nonpos_right hside hdiff)
  have hexpbound : ∀ k, B ≤ expectedCost M (expensiveSeq k) := by
    intro k
    have hopt := (PandoraBO.Private20261023.weitzman_optimality
      M (below k) (hbelowpos k)).2 (expensiveSeq k) (hexpindices k)
    have hside := PandoraBO.Private20261023.Reduction.cost_side
      M B multiplier (below k) hmin (hbelowpos k).le
        refPolicy (expensiveSeq k) hrefopt hopt
    have hdiff : below k - multiplier < 0 := by
      change multiplier - eps k - multiplier < 0
      linarith [hepspos k]
    exact sub_nonneg.mp (nonneg_of_mul_nonpos_right hside hdiff)
  have hcheapB : expectedCost M cheap ≤ B :=
    le_of_tendsto_of_tendsto' hcheaplim tendsto_const_nhds hcheapbound
  have hBexp : B ≤ expectedCost M expensive :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hexplim hexpbound
  obtain ⟨low, high, _hlow, _hhigh, hextrema, hmix⟩ :=
    PandoraBO.Private20261023.optimal_face_gittins_cost_extrema M multiplier hpos
  have hcheapopt :=
    (PandoraBO.Private20261023.weitzman_optimality M multiplier hpos).2 cheap hcheapindex
  have hexpopt :=
    (PandoraBO.Private20261023.weitzman_optimality M multiplier hpos).2 expensive hexpindex
  have hlowB := le_trans (hextrema cheap hcheapopt).1 hcheapB
  have hBhigh := le_trans hBexp (hextrema expensive hexpopt).2
  obtain ⟨a, ha0, ha1, haB⟩ :=
    PandoraBO.Private20261023.Reduction.interval_combination
      (expectedCost M low) B (expectedCost M high) hlowB hBhigh
  obtain ⟨π, hindex, hcost⟩ := hmix a ha0 ha1
  exact ⟨π, (PandoraBO.Private20261023.weitzman_optimality
    M multiplier hpos).2 π hindex, hcost.trans haB⟩
