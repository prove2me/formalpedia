-- Prove2me | solution 1 for PlankProblem.sum_smul_mem_of_abs_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:47:18.763777+00:00
-- url     : https://prove2.me/submissions/3a71068e-ba33-48f1-a1bb-0bf78a02bec5

module
public import Definitions.Def_BallPlank_ShiftedPlanks
public import Definitions.Def_BallPlank_BallPlankFinal

set_option autoImplicit true
@[expose] public section
public section
open Set
open scoped BigOperators InnerProductSpace Pointwise
noncomputable section
open PlankProblem
variable {n : ℕ}
local notation "Rn" => EuclideanSpace ℝ (Fin n)
namespace PlankProblem
theorem _root_.solution {ι : Type*} [Fintype ι] {S : Set Rn} (hS : Convex ℝ S)
    (h0 : (0 : Rn) ∈ S) (hneg : ∀ x ∈ S, -x ∈ S) (v : ι → Rn) (hv : ∀ i, v i ∈ S)
    (a : ι → ℝ) (ha : ∑ i, |a i| ≤ 1) : ∑ i, a i • v i ∈ S := by
  classical
  set W := ∑ i, |a i| with hW
  let u : ι → Rn := fun i => if 0 ≤ a i then v i else -v i
  have hu : ∀ i, u i ∈ S := fun i => by
    simp only [u]; split_ifs
    · exact hv i
    · exact hneg _ (hv i)
  have hau : ∀ i, a i • v i = |a i| • u i := fun i => by
    simp only [u]; split_ifs with h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (not_le.mp h), smul_neg, neg_smul, neg_neg]
  simp_rw [hau]
  by_cases hW0 : W = 0
  · have : ∀ i, |a i| = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => abs_nonneg (a i))).mp hW0 i (Finset.mem_univ _)
    simp [this, h0]
  have hWpos : 0 < W := lt_of_le_of_ne (Finset.sum_nonneg fun i _ => abs_nonneg _) (Ne.symm hW0)
  have hmem : ∑ i, (|a i| / W) • u i ∈ S := by
    refine hS.sum_mem (fun i _ => div_nonneg (abs_nonneg _) hWpos.le) ?_ (fun i _ => hu i)
    rw [← Finset.sum_div, div_self hW0]
  have : ∑ i, |a i| • u i = W • ∑ i, (|a i| / W) • u i := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, mul_div_cancel₀ _ hW0]
  rw [this]
  exact hS.smul_mem_of_zero_mem h0 hmem ⟨hWpos.le, ha⟩
end PlankProblem
