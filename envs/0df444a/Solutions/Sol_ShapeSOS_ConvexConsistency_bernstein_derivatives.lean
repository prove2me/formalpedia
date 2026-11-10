-- Prove2me | solution 1 for ShapeSOS.ConvexConsistency.bernstein_derivatives
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T10:51:31.335814+00:00
-- url     : https://prove2.me/submissions/630ca588-11eb-4b23-b448-4dc6b82b8452

import Definitions.Def_ShapeSOS_ConvexConsistency_Approximation

set_option autoImplicit false
open Filter MeasureTheory
open scoped BigOperators Topology MeasureTheory
open ShapeSOS.ConvexConsistency

def fConst : Vec 1 → ℝ := fun _ => 1
def kZero : Fin 1 → ℕ := fun _ => 0

private lemma mixedPartial_kZero (g : Vec 1 → ℝ) :
    mixedPartial (cube 1 0 1) kZero g = g := by
  unfold mixedPartial kZero
  have hfr : List.finRange 1 = [(0 : Fin 1)] := by decide
  rw [hfr]
  rfl

private lemma filter_eq_singleton (d : ℕ) :
    (Finset.univ : Finset (Fin 1 → Fin (d + 1))).filter (fun j => ∑ i, (j i).val = d) =
      {fun _ => Fin.last d} := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.sum_univ_one, Finset.mem_singleton]
  constructor
  · intro hj
    funext i
    rw [Subsingleton.elim i 0]
    ext
    exact hj
  · intro hj
    rw [hj]
    rfl

private lemma value_bernstein_fConst (d : ℕ) (x : Vec 1) :
    value (ShapeSOS.ConvexConsistency.bernstein d fConst) x = x 0 ^ d := by
  unfold value ShapeSOS.ConvexConsistency.bernstein
  rw [filter_eq_singleton d, Finset.sum_singleton, Fin.prod_univ_one]
  simp [fConst, Fin.last]

private lemma bddAbove_err (d : ℕ) :
    BddAbove ((fun x : Vec 1 => |value (ShapeSOS.ConvexConsistency.bernstein d fConst) x - fConst x|) '' cube 1 0 1) := by
  refine ⟨1, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  dsimp only
  rw [value_bernstein_fConst]
  simp only [fConst]
  have hx0 : 0 ≤ x 0 ∧ x 0 ≤ 1 := hx 0
  have hpow0 : 0 ≤ x 0 ^ d := pow_nonneg hx0.1 d
  have hpow1 : x 0 ^ d ≤ 1 := pow_le_one₀ hx0.1 hx0.2
  rw [abs_le]
  constructor <;> linarith

private lemma one_le_uniformError (d : ℕ) (hd : 1 ≤ d) :
    1 ≤ uniformError (cube 1 0 1) (value (ShapeSOS.ConvexConsistency.bernstein d fConst)) fConst := by
  unfold uniformError
  have h0_mem : (0 : Vec 1) ∈ cube 1 0 1 := by
    intro i
    simp
  have hval0 : |(value (ShapeSOS.ConvexConsistency.bernstein d fConst) (0 : Vec 1)) - fConst (0 : Vec 1)| = 1 := by
    rw [value_bernstein_fConst]
    have hd0 : d ≠ 0 := by omega
    simp [fConst, zero_pow hd0]
  exact le_trans (le_of_eq hval0.symm) (le_csSup (bddAbove_err d) ⟨0, h0_mem, rfl⟩)

theorem solution :
    ¬ (∀ (n : ℕ) (_hn : 0 < n) (m : ℕ)
      (f : Vec n → ℝ) (_hf : ContDiffOn ℝ m f (cube n 0 1)),
      ∀ k : Fin n → ℕ, (∑ i, k i) ≤ m →
        Tendsto (fun d => uniformError (cube n 0 1)
          (mixedPartial (cube n 0 1) k (value (ShapeSOS.ConvexConsistency.bernstein d f)))
          (mixedPartial (cube n 0 1) k f)) atTop (𝓝 0)) := by
  intro h
  have hf : ContDiffOn ℝ 0 fConst (cube 1 0 1) := contDiffOn_const
  have hk : (∑ i : Fin 1, kZero i) ≤ 0 := by simp [kZero]
  have ht := h 1 Nat.one_pos 0 fConst hf kZero hk
  simp only [mixedPartial_kZero] at ht
  rw [Metric.tendsto_atTop] at ht
  obtain ⟨N, hN⟩ := ht (1 / 2) (by norm_num)
  have hge := one_le_uniformError (max N 1) (le_max_right N 1)
  have hlt := hN (max N 1) (le_max_left N 1)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by linarith)] at hlt
  linarith
