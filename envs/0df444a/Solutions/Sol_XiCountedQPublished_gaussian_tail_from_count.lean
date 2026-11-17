-- Prove2me | solution 1 for XiCountedQPublished.gaussian_tail_from_count
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-16T08:32:33.270327+00:00
-- url     : https://prove2.me/submissions/5e22f36b-3eb1-4fef-8d4e-408ad42fcd12

import Mathlib
open MeasureTheory Set Filter Topology
open scoped BigOperators
noncomputable section
namespace CountingTail

theorem weight_integrable (t A : ℝ) (ht : 0 < t) (hA : 0 ≤ A) :
    IntegrableOn (fun y : ℝ => t*y*Real.exp (-(t*y))) (Ioi A) := by
  have hi : IntegrableOn (fun y : ℝ => y*Real.exp (-(t*y))) (Ioi 0) := by
    by_contra h
    have hg := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := t) (by norm_num) ht
    norm_num at hg
    rw [integral_undef h] at hg
    have hp : 0 < (t^2)⁻¹ := by positivity
    linarith
  have hj : IntegrableOn (fun y : ℝ => t*(y*Real.exp (-(t*y)))) (Ioi 0) := hi.const_mul t
  simpa only [mul_assoc] using hj.mono_set (Ioi_subset_Ioi hA)

theorem integral_weight (t A : ℝ) (ht : 0 < t) (hA : 0 ≤ A) :
    (∫ y : ℝ in Ioi A, t*y*Real.exp (-(t*y))) =
      (A+t⁻¹)*Real.exp (-(t*A)) := by
  have hd (y : ℝ) : HasDerivAt (fun y : ℝ => -(y+t⁻¹)*Real.exp (-(t*y)))
      (t*y*Real.exp (-(t*y))) y := by
    have he := (Real.hasDerivAt_exp (-t*y)).comp y ((hasDerivAt_id y).const_mul (-t))
    have hh := (((hasDerivAt_id y).add_const t⁻¹).neg).mul he
    convert! hh using 1
    · funext x
      simp only [Pi.mul_apply, Pi.neg_apply, Function.comp_apply, id_eq, neg_mul]
    · dsimp
      field_simp
      <;> ring
  have h0 : Tendsto (fun y : ℝ => Real.exp (-(t*y))) atTop (𝓝 0) := by
    simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (0:ℝ) t ht
  have h1 : Tendsto (fun y : ℝ => y*Real.exp (-(t*y))) atTop (𝓝 0) := by
    simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1:ℝ) t ht
  have hz : Tendsto (fun y : ℝ => -(y+t⁻¹)*Real.exp (-(t*y))) atTop (𝓝 0) := by
    convert (h1.add (h0.const_mul t⁻¹)).neg using 1 <;> simp <;> ring
  have hh := integral_Ioi_of_hasDerivAt_of_tendsto' (fun y _ => hd y)
    (weight_integrable t A ht hA) hz
  rw [hh]
  ring

theorem indicator_integrable (t A a : ℝ) (ht : 0 < t) :
    IntegrableOn ((Ioi a).indicator (fun y : ℝ => t*Real.exp (-(t*y)))) (Ioi A) := by
  apply Integrable.indicator _ measurableSet_Ioi
  simpa only [neg_mul] using (integrableOn_exp_mul_Ioi (neg_neg_of_pos ht) A).const_mul t

theorem indicator_integral (t A a : ℝ) (ht : 0 < t) (hAa : A ≤ a) :
    (∫ y : ℝ in Ioi A, (Ioi a).indicator (fun y : ℝ => t*Real.exp (-(t*y))) y) =
      Real.exp (-(t*a)) := by
  rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.mpr (Ioi_subset_Ioi hAa), integral_const_mul]
  have he := integral_exp_mul_Ioi (neg_neg_of_pos ht) a
  simp only [neg_mul] at he
  rw [he]
  field_simp

theorem finite_tail_bound (a : ℕ → ℝ) (F : Finset ℕ) (t A : ℝ)
    (ht : 0 < t) (hA : 0 ≤ A) (hF : ∀ j ∈ F, A < a j)
    (hcount : ∀ y ≥ A, ((F.filter (fun j => a j < y)).card : ℝ) ≤ y) :
    (∑ j ∈ F, Real.exp (-(t*a j))) ≤ (A+t⁻¹)*Real.exp (-(t*A)) := by
  classical
  have hi := fun j (_ : j ∈ F) => indicator_integrable t A (a j) ht
  calc
    _ = ∑ j ∈ F, ∫ y : ℝ in Ioi A,
        (Ioi (a j)).indicator (fun y : ℝ => t*Real.exp (-(t*y))) y := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (indicator_integral t A (a j) ht (hF j hj).le).symm
    _ = ∫ y : ℝ in Ioi A, ∑ j ∈ F,
        (Ioi (a j)).indicator (fun y : ℝ => t*Real.exp (-(t*y))) y :=
      (integral_finsetSum F hi).symm
    _ ≤ ∫ y : ℝ in Ioi A, t*y*Real.exp (-(t*y)) := by
      apply integral_mono_ae (integrable_finset_sum F hi) (weight_integrable t A ht hA)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      have he : (∑ j ∈ F, (Ioi (a j)).indicator
          (fun y : ℝ => t*Real.exp (-(t*y))) y) =
          ((F.filter (fun j => a j < y)).card : ℝ) * (t*Real.exp (-(t*y))) := by
        simp only [Set.indicator, mem_Ioi]
        rw [← Finset.sum_filter]
        simp
      rw [he]
      have hh := mul_le_mul_of_nonneg_right (hcount y (mem_Ioi.mp hy).le)
        (mul_nonneg ht.le (Real.exp_pos (-(t*y))).le)
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hh
    _ = _ := integral_weight t A ht hA

theorem tail_summable_and_bound (a : ℕ → ℝ) (t A : ℝ)
    (ht : 0 < t) (hA : 0 ≤ A)
    (hcount : ∀ y ≥ A, ∀ F : Finset ℕ,
      (∀ j ∈ F, a j ≤ y) → (F.card : ℝ) ≤ y) :
    Summable (fun j => if A < a j then Real.exp (-(t*a j)) else 0) ∧
    (∑' j, if A < a j then Real.exp (-(t*a j)) else 0) ≤
      (A+t⁻¹)*Real.exp (-(t*A)) := by
  classical
  have hb (F : Finset ℕ) :
      (∑ j ∈ F, if A < a j then Real.exp (-(t*a j)) else 0) ≤
        (A+t⁻¹)*Real.exp (-(t*A)) := by
    rw [← Finset.sum_filter]
    apply finite_tail_bound a _ t A ht hA
    · intro j hj
      exact (Finset.mem_filter.mp hj).2
    · intro y hy
      apply hcount y hy
      intro j hj
      exact ((Finset.mem_filter.mp hj).2).le
  have hs := summable_of_sum_le (fun j => by split_ifs <;> positivity) hb
  exact ⟨hs, hs.tsum_le_of_sum_le hb⟩

theorem full_summable (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (t A : ℝ)
    (ht : 0 < t) (hA : 0 ≤ A)
    (hcount : ∀ y ≥ A, ∀ F : Finset ℕ,
      (∀ j ∈ F, a j ≤ y) → (F.card : ℝ) ≤ y) :
    Summable (fun j => Real.exp (-(t*a j))) := by
  classical
  apply summable_of_sum_le (fun j => (Real.exp_pos _).le)
    (c := A+(A+t⁻¹)*Real.exp (-(t*A)))
  intro F
  rw [← Finset.sum_filter_add_sum_filter_not F (fun j => A < a j)]
  have htail : (∑ j ∈ F.filter (fun j => A < a j), Real.exp (-(t*a j))) ≤
      (A+t⁻¹)*Real.exp (-(t*A)) := by
    apply finite_tail_bound a _ t A ht hA
    · intro j hj; exact (Finset.mem_filter.mp hj).2
    · intro y hy
      apply hcount y hy
      intro j hj; exact ((Finset.mem_filter.mp hj).2).le
  have hhead : (∑ j ∈ F.filter (fun j => ¬ A < a j), Real.exp (-(t*a j))) ≤ A := by
    calc
      _ ≤ ∑ j ∈ F.filter (fun j => ¬ A < a j), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        apply Real.exp_le_one_iff.mpr
        exact neg_nonpos.mpr (mul_nonneg ht.le (ha j))
      _ = ((F.filter (fun j => ¬ A < a j)).card : ℝ) := by simp
      _ ≤ A := hcount A le_rfl _ (fun j hj => le_of_not_gt (Finset.mem_filter.mp hj).2)
  linarith

theorem gaussian_from_counting (gamma : ℕ → ℝ) (hg : ∀ j, 0 ≤ gamma j)
    (hcount : ∀ T ≥ (10 : ℝ), ∀ F : Finset ℕ,
      (∀ j ∈ F, gamma j ≤ T) → (F.card : ℝ) ≤ T^2) :
    (∀ t > 0, Summable (fun j => Real.exp (-(gamma j)^2*t))) ∧
    (∀ t > 0, ∀ L ≥ (10 : ℝ),
      (∑' j, if L < gamma j then Real.exp (-(gamma j)^2*t) else 0) ≤
        (L^2+t⁻¹)*Real.exp (-L^2*t)) := by
  have hc (L : ℝ) (hL : 10 ≤ L) :
      ∀ y ≥ L^2, ∀ F : Finset ℕ,
      (∀ j ∈ F, (gamma j)^2 ≤ y) → (F.card : ℝ) ≤ y := by
    intro y hy F hF
    have hy0 : 0 ≤ y := le_trans (sq_nonneg L) hy
    have hs : (Real.sqrt y)^2 = y := Real.sq_sqrt hy0
    have hs0 := Real.sqrt_nonneg y
    have hs10 : 10 ≤ Real.sqrt y := by nlinarith
    have hh := hcount (Real.sqrt y) hs10 F (by
      intro j hj
      have hjj := hF j hj
      nlinarith [hg j])
    simpa only [hs] using hh
  constructor
  · intro t ht
    have hh := full_summable (fun j => (gamma j)^2) (fun j => sq_nonneg _) t 100
      ht (by norm_num) (by simpa only [show (10:ℝ)^2=100 by norm_num] using hc 10 le_rfl)
    simpa only [neg_mul, mul_comm t] using hh
  · intro t ht L hL
    have hh := (tail_summable_and_bound (fun j => (gamma j)^2) t (L^2)
      ht (sq_nonneg L) (hc L hL)).2
    have he (j : ℕ) : L^2 < (gamma j)^2 ↔ L < gamma j := by
      constructor <;> intro h <;> nlinarith [hg j]
    simpa only [he, neg_mul, mul_comm t] using hh

end CountingTail

theorem solution (gamma : ℕ → ℝ) (hg : ∀ j, 0 ≤ gamma j)
    (hcount : ∀ T ≥ (10 : ℝ), ∀ F : Finset ℕ,
      (∀ j ∈ F, gamma j ≤ T) → (F.card : ℝ) ≤ T^2) :
    (∀ t > 0, Summable (fun j => Real.exp (-(gamma j)^2*t))) ∧
    (∀ t > 0, ∀ L ≥ (10 : ℝ),
      (∑' j, if L < gamma j then Real.exp (-(gamma j)^2*t) else 0) ≤
        (L^2+t⁻¹)*Real.exp (-L^2*t)) := by
  exact CountingTail.gaussian_from_counting gamma hg hcount
