-- Prove2me | solution 1 for Paper.Hypergraph.twoTerminal_independence_rounding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:21:08.359551+00:00
-- url     : https://prove2.me/submissions/e5e45104-e81a-4e74-8e0a-e227de8ce57f

import Definitions.Def_Paper_RoundingAveraging
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_Paper_RoundingIndependence
import Theorems.Thm_Paper_Hypergraph_independent_card_le
import Theorems.Thm_Paper_Hypergraph_trimDemand_support
import Theorems.Thm_Paper_Hypergraph_trimDemand_cost_le
import Theorems.Thm_Paper_Hypergraph_trimDemand_fractionalSeparator
import Theorems.Thm_Paper_Hypergraph_log_nat_nonneg
import Theorems.Thm_Paper_Hypergraph_support_integralSeparator
import Theorems.Thm_Paper_Hypergraph_twoTerminal_minimum_weight_rounding


set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {A B : Finset ℕ} {x : ℕ → ℝ}
    (hA : A ⊆ H.vertices) (hB : B ⊆ H.vertices) (hx : H.FractionalSeparator A B x) :
    ∃ S ⊆ H.vertices.filter (fun v => x v ≠ 0), H.IntegralSeparator A B S ∧
      H.setCoverCost S ≤
        (8 + 4 * Real.log ((H.induce (H.vertices.filter (fun v => x v ≠ 0))).independenceNumber : ℝ)) *
          H.coverCost x := by
  let R := H.vertices.filter (fun v => x v ≠ 0)
  let α : ℝ := (H.induce R).independenceNumber
  by_cases hR : R.Nonempty
  swap
  · have hR0 := Finset.not_nonempty_iff_eq_empty.mp hR
    refine ⟨R, Subset.refl _, H.support_integralSeparator hA hx, ?_⟩
    have hempty : H.setCoverCost ∅ = 0 := H.coverCost_eq_zero_of_nonpos (fun v hv => by simp [indicator])
    rw [hR0, hempty]
    apply mul_nonneg _ (H.coverCost_nonneg x)
    have := log_nat_nonneg (H.induce R).independenceNumber
    change 0 ≤ 8 + 4 * Real.log α
    dsimp [α]
    linarith
  have hα1 : 1 ≤ α := by
    obtain ⟨v, hv⟩ := hR
    have hcard : ({v} : Finset ℕ).card ≤ (H.induce R).independenceNumber := by
      apply (H.induce R).independent_card_le
      · intro w hw
        have hwv := mem_singleton.mp hw
        subst w
        exact mem_inter.mpr ⟨(mem_filter.mp hv).1, hv⟩
      · intro a ha b hb
        have ha' := mem_singleton.mp ha
        have hb' := mem_singleton.mp hb
        subst a b
        exact fun h => h.ne rfl
    simpa [α] using (show (1 : ℝ) ≤ (H.induce R).independenceNumber by exact_mod_cast hcard)
  have hα : 0 < α := by linarith
  let ε : ℝ := 1 / (4 * α)
  have hε : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := (div_le_one (by positivity : 0 < 4 * α)).2 (by linarith)
  have hbudget : ε * (2 * (H.induce R).independenceNumber : ℝ) ≤ 1 / 2 := by
    change (1 / (4 * α)) * (2 * α) ≤ 1 / 2
    field_simp
    linarith
  have hz := H.trimDemand_fractionalSeparator hA hx hε hbudget
  have hsmall : ∀ v ∈ H.vertices, trimDemand x ε v = 0 ∨ ε ≤ trimDemand x ε v := by
    intro v hv
    dsimp [trimDemand]
    split_ifs with h
    · exact Or.inr (le_min (by linarith) hε1)
    · exact Or.inl rfl
  obtain ⟨S, hS, hsep, hcost⟩ := H.twoTerminal_minimum_weight_rounding hA hB hz hε hε1 hsmall
  refine ⟨S, hS.trans (H.trimDemand_support x hε), hsep, ?_⟩
  have hlog : Real.log (1 / ε) = Real.log 4 + Real.log α := by
    rw [show 1 / ε = 4 * α by simp [ε], Real.log_mul (by norm_num) (ne_of_gt hα)]
  have hlog4 : Real.log 4 < 3 / 2 := by
    have h := Real.log_two_lt_d9
    have heq : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      ring
    linarith
  have hc : 0 ≤ 1 + 2 * Real.log (1 / ε) := by
    have h := Real.log_nonneg ((le_div_iff₀ hε).2 (by simpa using hε1))
    linarith
  calc
    H.setCoverCost S ≤ (1 + 2 * Real.log (1 / ε)) * (2 * H.coverCost x) :=
      hcost.trans (mul_le_mul_of_nonneg_left (H.trimDemand_cost_le hx.1 ε) hc)
    _ = ((1 + 2 * Real.log (1 / ε)) * 2) * H.coverCost x := by ring
    _ ≤ (8 + 4 * Real.log α) * H.coverCost x := by
      apply mul_le_mul_of_nonneg_right _ (H.coverCost_nonneg x)
      rw [hlog]
      linarith
end Paper.Hypergraph
