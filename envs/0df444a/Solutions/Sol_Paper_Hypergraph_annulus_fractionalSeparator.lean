-- Prove2me | solution 1 for Paper.Hypergraph.annulus_fractionalSeparator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:16:00.934777+00:00
-- url     : https://prove2.me/submissions/1e5ed393-a807-4cfe-acaf-d7d791dd6db6

import Definitions.Def_Paper_RoundingEstimates
import Definitions.Def_Paper_RoundingGeometry
import Theorems.Thm_Paper_Hypergraph_vertexDistance_step
import Theorems.Thm_Paper_Hypergraph_annulusPotential_step
import Theorems.Thm_Paper_Hypergraph_walk_potential_le

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {x : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) {c : ℕ} (hc : c ∈ H.vertices)
    {a b q : ℝ} (hq : ∀ v ∈ H.vertices, x v ≤ q) (hgap : q < (b - a) / 2)
    (hq0 : 0 ≤ q) :
    let d := H.vertexDistance x c
    let A := H.vertices.filter (fun v => d v ≤ a)
    let B := H.vertices.filter (fun v => b < d v)
    let z := fun v => if a < d v ∧ d v ≤ b then x v / (b - a - q) else 0
    H.FractionalSeparator A B z := by
  dsimp
  let d := H.vertexDistance x c
  let z := fun v => if a < d v ∧ d v ≤ b then x v / (b - a - q) else 0
  let f := fun v => annulusPotential a b q (d v)
  have hg : 0 < b - a - q := by linarith
  have hz : H.UnitDemand z := by
    intro v hv
    dsimp [z]
    split_ifs
    · exact ⟨div_nonneg (hx v hv) hg.le,
        (div_le_one hg).2 (by have := hq v hv; linarith)⟩
    · norm_num
  refine ⟨hz, ?_⟩
  intro u hu v hv
  have huV := (mem_filter.mp hu).1
  have hud : d u ≤ a := (mem_filter.mp hu).2
  have hvd : b < d v := (mem_filter.mp hv).2
  have hfu : f u = 0 := by simp [f, annulusPotential, max_eq_left (by linarith : d u - a ≤ 0), hg.le]
  have hfv : f v = b - a - q := by
    dsimp [f, annulusPotential]
    rw [max_eq_right (by linarith : 0 ≤ d v - a), min_eq_left (by linarith)]
  have hzu : z u = 0 := by simp [z, not_lt.mpr hud]
  apply le_csInf ⟨1, Set.mem_insert _ _⟩
  rintro t (rfl | ⟨p, hp, rfl⟩)
  · exact le_rfl
  · have hstep : ∀ w ∈ H.vertices, ∀ t ∈ H.vertices, H.primal.Adj w t →
        f t ≤ f w + (b - a - q) * z t := by
      intro w hw t ht hwt
      have hs := annulusPotential_step hg (hx t ht) (hq t ht)
        (H.vertexDistance_step hx hc ht hwt)
      dsimp [f, z, d]
      split_ifs with hm
      · simpa [hm, mul_div_cancel₀ _ hg.ne'] using hs
      · simpa [hm] using hs
    have hs := H.walk_potential_le hstep huV p hp
    rw [hfu, hfv, hzu, mul_zero, sub_zero, zero_add, ← mul_sum] at hs
    exact (mul_le_mul_iff_right₀ hg).mp (by simpa [mul_comm] using hs)
end Paper.Hypergraph
