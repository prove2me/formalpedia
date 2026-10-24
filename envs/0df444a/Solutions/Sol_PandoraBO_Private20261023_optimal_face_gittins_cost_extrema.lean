-- Prove2me | solution 1 for PandoraBO.Private20261023.optimal_face_gittins_cost_extrema
-- status  : ACCEPTED   (prove)
-- author  : @QianJaneXie
-- created : 2026-10-24T00:54:21.542281+00:00
-- url     : https://prove2.me/submissions/ea3d0599-d33c-4f2c-b98d-6b38620ad7bf

import Definitions.Def_PandoraBO_Model
import Theorems.Thm_PandoraBO_Private20261023_monotone_multiplier_optimal_policy_limit
import Theorems.Thm_PandoraBO_Private20261023_weitzman_optimality
import Theorems.Thm_PandoraBO_Private20261023_gittins_policy_mixture
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
Tracked reduction: one-sided monotone limits of positive-cost optimizers
minimize and maximize expected cost on the entire optimal face. The remaining
convex-combination clause uses the explicit uniform-seed policy mixture lemma.
-/

set_option autoImplicit false

open PandoraBO Filter

namespace PandoraBO.Private20261023.Reduction

private theorem optimal_cost_side {n : ℕ} (M : Instance n) (multiplier t : ℝ)
    (π ρ : Policy n) (hπ : optimal M multiplier π) (hρ : optimal M t ρ) :
    (t - multiplier) * (expectedCost M ρ - expectedCost M π) ≤ 0 := by
  have hleft := hπ ρ
  have hright := hρ π
  simp only [value] at hleft hright
  nlinarith

end PandoraBO.Private20261023.Reduction

theorem solution {n : ℕ} (M : Instance n)
    (multiplier : ℝ) (hpos : 0 < multiplier) :
    ∃ low high : Policy n,
      isGittinsPolicy M multiplier low ∧ isGittinsPolicy M multiplier high ∧
      (∀ π : Policy n, optimal M multiplier π →
        expectedCost M low ≤ expectedCost M π ∧ expectedCost M π ≤ expectedCost M high) ∧
      ∀ a : ℝ, 0 ≤ a → a ≤ 1 → ∃ π : Policy n,
        isGittinsPolicy M multiplier π ∧
        expectedCost M π = a * expectedCost M low + (1 - a) * expectedCost M high := by
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
  obtain ⟨lowSeq, low, hlowindices, hlowindex, hlowlim, _hlowreward⟩ :=
    PandoraBO.Private20261023.monotone_multiplier_optimal_policy_limit
      M above multiplier habovepos hpos (Or.inr habovemono) habovelim
  obtain ⟨highSeq, high, hhighindices, hhighindex, hhighlim, _hhighreward⟩ :=
    PandoraBO.Private20261023.monotone_multiplier_optimal_policy_limit
      M below multiplier hbelowpos hpos (Or.inl hbelowmono) hbelowlim
  refine ⟨low, high, hlowindex, hhighindex, ?_, ?_⟩
  · intro π hπ
    constructor
    · have hbound : ∀ k, expectedCost M (lowSeq k) ≤ expectedCost M π := by
        intro k
        have hopt := (PandoraBO.Private20261023.weitzman_optimality
          M (above k) (habovepos k)).2 (lowSeq k) (hlowindices k)
        have hside := PandoraBO.Private20261023.Reduction.optimal_cost_side
          M multiplier (above k) π (lowSeq k) hπ hopt
        have hdiff : 0 < above k - multiplier := by
          change 0 < multiplier + eps k - multiplier
          linarith [hepspos k]
        exact sub_nonpos.mp (nonpos_of_mul_nonpos_right hside hdiff)
      exact le_of_tendsto_of_tendsto' hlowlim tendsto_const_nhds hbound
    · have hbound : ∀ k, expectedCost M π ≤ expectedCost M (highSeq k) := by
        intro k
        have hopt := (PandoraBO.Private20261023.weitzman_optimality
          M (below k) (hbelowpos k)).2 (highSeq k) (hhighindices k)
        have hside := PandoraBO.Private20261023.Reduction.optimal_cost_side
          M multiplier (below k) π (highSeq k) hπ hopt
        have hdiff : below k - multiplier < 0 := by
          change multiplier - eps k - multiplier < 0
          linarith [hepspos k]
        exact sub_nonneg.mp (nonneg_of_mul_nonpos_right hside hdiff)
      exact le_of_tendsto_of_tendsto' tendsto_const_nhds hhighlim hbound
  · intro a ha0 ha1
    obtain ⟨π, hindex, hcost, _hreward⟩ :=
      PandoraBO.Private20261023.gittins_policy_mixture
        M multiplier hpos low high hlowindex hhighindex a ha0 ha1
    exact ⟨π, hindex, hcost⟩
