-- Prove2me | solution 1 for Rudin.ch08_double_series
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T17:43:13.273979+00:00
-- url     : https://prove2.me/submissions/8aeecb67-d8ca-4c85-bd08-d82563d119ac

import Mathlib
import Definitions.Def_Rudin_ch03_series
open Filter Topology Rudin
noncomputable section
/-- Rudin, Theorem 8.3: given a double sequence `a i j`, if `∑_j |a i j| = b i` for each `i`
and `∑ b i` converges, then the two iterated sums of `a i j` converge and are equal. -/
theorem solution (a : ℕ → ℕ → ℝ) (b : ℕ → ℝ)
    (hb : ∀ i, SeriesConvergesTo (fun j => |a i j|) (b i)) (hbsum : SeriesConverges b) :
    ∃ S : ℝ,
      SeriesConvergesTo (fun i => ∑' j, a i j) S ∧
      SeriesConvergesTo (fun j => ∑' i, a i j) S := by
  have hrow (i : ℕ) : HasSum (fun j => |a i j|) (b i) := by
    apply (hasSum_iff_tendsto_nat_of_nonneg (fun j => abs_nonneg (a i j)) (b i)).2
    exact hb i
  have hbn (i : ℕ) : 0 ≤ b i := by
    rw [← (hrow i).tsum_eq]
    exact tsum_nonneg (fun j => abs_nonneg (a i j))
  obtain ⟨B, hB⟩ := hbsum
  have hbs : Summable b := by
    apply HasSum.summable (a := B)
    apply (hasSum_iff_tendsto_nat_of_nonneg hbn B).2
    exact hB
  have habs : Summable (fun p : ℕ × ℕ => |a p.1 p.2|) := by
    apply (summable_prod_of_nonneg (fun p => abs_nonneg (a p.1 p.2))).2
    refine ⟨fun i => (hrow i).summable, ?_⟩
    simpa only [(hrow _).tsum_eq] using hbs
  have ha : Summable (fun p : ℕ × ℕ => a p.1 p.2) := by
    apply Summable.of_norm
    simpa only [Real.norm_eq_abs] using habs
  refine ⟨∑' i, ∑' j, a i j, ?_, ?_⟩
  · exact ha.prod.hasSum.tendsto_sum_nat
  · have hc := ha.prod_symm.prod.hasSum.tendsto_sum_nat
    change Tendsto (fun n => ∑ j ∈ Finset.range n, ∑' i, a i j) atTop (𝓝 (∑' j, ∑' i, a i j)) at hc
    rw [ha.tsum_comm] at hc
    exact hc
#print axioms solution
