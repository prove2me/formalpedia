-- Prove2me | solution 1 for SampleCRS.AlmostGreedy.Supplement.theorem_b_3
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-23T23:36:49.29374+00:00
-- url     : https://prove2.me/submissions/a30a0e82-4b49-4675-9a94-ae2a3ed650d0

import Mathlib
import Definitions.Def_SampleCRS_AlmostGreedy_Supplement_discreteOrder

open MeasureTheory Filter Topology SampleCRS.AlmostGreedy.Supplement

namespace B3Aux

noncomputable def sl (j x : ℕ) : ℝ := max ((x : ℝ) - j - 1) 0

noncomputable def F (f : ℕ → ℝ) (N x : ℕ) : ℝ :=
  f 0 + delta f 0 * x + ∑ j ∈ Finset.range N, delta2 f j * sl j x

lemma taylor (f : ℕ → ℝ) (x : ℕ) :
    f x = f 0 + delta f 0 * x + ∑ j ∈ Finset.range x, delta2 f j * ((x : ℝ) - j - 1) := by
  induction x with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hs : ∑ j ∈ Finset.range n, delta2 f j * (((n + 1 : ℕ) : ℝ) - j - 1) =
        ∑ j ∈ Finset.range n, delta2 f j * ((n : ℝ) - j - 1) + ∑ j ∈ Finset.range n, delta2 f j := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      push_cast
      ring
    have htel : ∑ j ∈ Finset.range n, delta2 f j = delta f n - delta f 0 := by
      simp only [delta2]
      exact Finset.sum_range_sub (delta f) n
    rw [hs, htel]
    have hstep : f (n + 1) = f n + delta f n := by unfold delta; ring
    rw [hstep, ih]
    push_cast
    ring

lemma F_eq (f : ℕ → ℝ) (N x : ℕ) (hx : x ≤ N) : F f N x = f x := by
  conv_rhs => rw [taylor f x]
  unfold F
  congr 1
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr hx)]
  · apply Finset.sum_congr rfl
    intro j hj
    have hj' : j + 1 ≤ x := Finset.mem_range.mp hj
    have : (j : ℝ) + 1 ≤ x := by exact_mod_cast hj'
    unfold sl
    rw [max_eq_left (by linarith)]
  · intro j _ hj
    have hj' : x ≤ j := by simpa using hj
    have : (x : ℝ) ≤ j := by exact_mod_cast hj'
    unfold sl
    rw [max_eq_right (by linarith), mul_zero]

lemma F_mono (f : ℕ → ℝ) (hf : DiscreteConvex f) {N M : ℕ} (h : N ≤ M) (x : ℕ) :
    F f N x ≤ F f M x := by
  unfold F
  have := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr h)
    (fun j _ _ => mul_nonneg (hf j) (le_max_right _ _)) (f := fun j => delta2 f j * sl j x)
  linarith

lemma F_le (f : ℕ → ℝ) (hf : DiscreteConvex f) (N x : ℕ) : F f N x ≤ f x :=
  le_trans (F_mono f hf (le_max_left N x) x) (F_eq f _ x (le_max_right _ _)).le

lemma L_le (f : ℕ → ℝ) (hf : DiscreteConvex f) (N x : ℕ) :
    f 0 + delta f 0 * x ≤ F f N x := by
  unfold F
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => mul_nonneg (hf j) (le_max_right _ _)))

lemma sl_int (μ : NatLaw) (j : ℕ) : Integrable (sl j) μ.law := by
  refine Integrable.mono' μ.finiteMean measurable_from_nat.aestronglyMeasurable
    (ae_of_all _ (fun x => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  exact max_le (by linarith) (Nat.cast_nonneg x)

lemma sl_convex (j : ℕ) : DiscreteConvex (sl j) := by
  have hmax : ∀ s t u : ℝ, s + u = 2 * t → 2 * max t 0 ≤ max s 0 + max u 0 := by
    intro s t u h
    rcases le_total t 0 with ht | ht
    · rw [max_eq_right ht]; linarith [le_max_right s 0, le_max_right u 0]
    · rw [max_eq_left ht]; linarith [le_max_left s 0, le_max_left u 0]
  intro i
  simp only [delta2, delta, sl]
  have := hmax ((i : ℝ) - j - 1) (((i + 1 : ℕ) : ℝ) - j - 1) (((i + 1 + 1 : ℕ) : ℝ) - j - 1)
    (by push_cast; ring)
  linarith

lemma L_int (f : ℕ → ℝ) (μ : NatLaw) :
    Integrable (fun x : ℕ => f 0 + delta f 0 * (x : ℝ)) μ.law :=
  (integrable_const _).add (μ.finiteMean.const_mul _)

lemma F_int (f : ℕ → ℝ) (μ : NatLaw) (N : ℕ) : Integrable (F f N) μ.law := by
  unfold F
  exact (L_int f μ).add (integrable_finsetSum _ (fun j _ => (sl_int μ j).const_mul _))

lemma F_integral (f : ℕ → ℝ) (μ : NatLaw) (N : ℕ) :
    ∫ x, F f N x ∂μ.law =
      f 0 + delta f 0 * mean μ + ∑ j ∈ Finset.range N, delta2 f j * stopLoss μ j := by
  unfold F
  rw [integral_add (L_int f μ) (integrable_finsetSum _ (fun j _ => (sl_int μ j).const_mul _)),
    integral_add (integrable_const _) (μ.finiteMean.const_mul _), integral_const,
    integral_const_mul, integral_finsetSum _ (fun j _ => (sl_int μ j).const_mul _)]
  simp only [probReal_univ, one_smul, integral_const_mul]
  rfl

lemma tendsto_int (f : ℕ → ℝ) (hf : DiscreteConvex f) (μ : NatLaw)
    (hfi : Integrable f μ.law) :
    Tendsto (fun N => ∫ x, F f N x ∂μ.law) atTop (𝓝 (∫ x, f x ∂μ.law)) := by
  refine tendsto_integral_of_dominated_convergence
    (fun x => |f x| + |f 0 + delta f 0 * (x : ℝ)|)
    (fun N => (F_int f μ N).aestronglyMeasurable)
    (hfi.abs.add (L_int f μ).abs)
    (fun N => ae_of_all _ (fun x => ?_))
    (ae_of_all _ (fun x => tendsto_atTop_of_eventually_const (fun N hN => F_eq f N x hN)))
  rw [Real.norm_eq_abs, abs_le]
  have h1 := F_le f hf N x
  have h2 := L_le f hf N x
  constructor
  · linarith [neg_abs_le (f 0 + delta f 0 * (x : ℝ)), abs_nonneg (f x)]
  · linarith [le_abs_self (f x), abs_nonneg (f 0 + delta f 0 * (x : ℝ))]

end B3Aux

theorem solution (P Q : NatLaw) :
    ConvexDominates P Q ↔ mean P - mean Q = 0 ∧ ∀ j : ℕ, 0 ≤ stopDifference P Q j := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have hc1 : DiscreteConvex (fun j : ℕ => (j : ℝ)) := by
        intro j; simp only [delta2, delta]; push_cast; linarith
      have hc2 : DiscreteConvex (fun j : ℕ => -(j : ℝ)) := by
        intro j; simp only [delta2, delta]; push_cast; linarith
      have h1 : ∫ j, (j : ℝ) ∂Q.law ≤ ∫ j, (j : ℝ) ∂P.law :=
        h (fun j : ℕ => (j : ℝ)) hc1 P.finiteMean Q.finiteMean
      have h2 : ∫ j, -(j : ℝ) ∂Q.law ≤ ∫ j, -(j : ℝ) ∂P.law :=
        h (fun j : ℕ => -(j : ℝ)) hc2 P.finiteMean.neg Q.finiteMean.neg
      rw [integral_neg, integral_neg] at h2
      unfold mean
      linarith
    · intro j
      have hj : ∫ x, B3Aux.sl j x ∂Q.law ≤ ∫ x, B3Aux.sl j x ∂P.law :=
        h (B3Aux.sl j) (B3Aux.sl_convex j) (B3Aux.sl_int P j) (B3Aux.sl_int Q j)
      unfold stopDifference stopLoss
      unfold B3Aux.sl at hj
      linarith
  · rintro ⟨hm, hD⟩ f hf hfP hfQ
    have hdiff := (B3Aux.tendsto_int f hf P hfP).sub (B3Aux.tendsto_int f hf Q hfQ)
    have hnn : ∀ N, 0 ≤ ∫ x, B3Aux.F f N x ∂P.law - ∫ x, B3Aux.F f N x ∂Q.law := by
      intro N
      rw [B3Aux.F_integral, B3Aux.F_integral]
      have hm' : mean P = mean Q := by linarith
      rw [hm']
      have hs : ∑ j ∈ Finset.range N, delta2 f j * stopLoss P j -
          ∑ j ∈ Finset.range N, delta2 f j * stopLoss Q j =
          ∑ j ∈ Finset.range N, delta2 f j * stopDifference P Q j := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j _
        unfold stopDifference
        ring
      have h0 : 0 ≤ ∑ j ∈ Finset.range N, delta2 f j * stopDifference P Q j :=
        Finset.sum_nonneg (fun j _ => mul_nonneg (hf j) (hD j))
      linarith
    have := ge_of_tendsto' hdiff hnn
    linarith
