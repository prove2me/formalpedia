-- Prove2me | solution 1 for PoissonDepTrials.MixSqrt.variance_identity_4_7
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T22:24:17.77014+00:00
-- url     : https://prove2.me/submissions/69b97b6d-e2fa-409a-91f5-ef41f1bc5f74

import Mathlib
import Definitions.Def_PoissonDepTrials_MixSqrt_Setting

open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Finset

namespace PoissonDepTrials.MixSqrt

def Sc (n : ℕ) (a : ℤ) (c : ℕ → ℕ) (T : ℤ) : ℕ :=
  ∑ k ∈ (Icc 1 n).filter (fun k : ℕ => a ≤ (k:ℤ) ∧ (k:ℤ) ≤ T), c k

lemma sum_eqT {M : Type*} [AddCommMonoid M] (n : ℕ) (T : ℤ) (g : ℕ → M) :
    ∑ k ∈ (Icc 1 n).filter (fun k : ℕ => (k:ℤ) = T), g k =
      if 1 ≤ T ∧ T ≤ n then g T.toNat else 0 := by
  split_ifs with hT
  · have : (Icc 1 n).filter (fun k : ℕ => (k:ℤ) = T) = {T.toNat} := by
      ext k; simp only [mem_filter, mem_Icc, mem_singleton]; omega
    rw [this, sum_singleton]
  · have : (Icc 1 n).filter (fun k : ℕ => (k:ℤ) = T) = ∅ := by
      ext k; simp only [mem_filter, mem_Icc, Finset.notMem_empty, iff_false]; omega
    rw [this, sum_empty]

lemma Sc_succ (n : ℕ) (a : ℤ) (c : ℕ → ℕ) (T : ℤ) (hT : a - 1 ≤ T) :
    Sc n a c (T + 1) = Sc n a c T + if 1 ≤ T + 1 ∧ T + 1 ≤ n then c (T + 1).toNat else 0 := by
  unfold Sc
  rw [← sum_eqT, ← sum_union]
  · congr 1; ext k; simp only [mem_filter, mem_union, mem_Icc]; omega
  · rw [disjoint_left]; intro k h1 h2; simp only [mem_filter] at h1 h2; omega

lemma Sc_empty (n : ℕ) (a : ℤ) (c : ℕ → ℕ) : Sc n a c (a - 1) = 0 := by
  unfold Sc
  apply sum_eq_zero; intro k hk; simp only [mem_filter] at hk; omega

lemma tele (n : ℕ) (a : ℤ) (c : ℕ → ℕ) (hc : ∀ k, c k ≤ 1) (f : ℕ → ℝ) (V : ℕ) (L : ℕ) :
    f (V + Sc n a c (a - 1 + L) + 1) - f (V + 1) =
    ∑ j ∈ (Icc 1 n).filter (fun j : ℕ => a ≤ (j:ℤ) ∧ (j:ℤ) ≤ a - 1 + L),
      (c j : ℝ) * delta f (V + Sc n a c ((j:ℤ) - 1) + 1) := by
  induction L with
  | zero =>
    simp only [CharP.cast_eq_zero, add_zero, Sc_empty]
    rw [sum_eq_zero]
    · simp
    · intro k hk; simp only [mem_filter] at hk; omega
  | succ L ih =>
    have hset : (Icc 1 n).filter (fun j : ℕ => a ≤ (j:ℤ) ∧ (j:ℤ) ≤ a - 1 + ((L+1:ℕ):ℤ)) =
       (Icc 1 n).filter (fun j : ℕ => a ≤ (j:ℤ) ∧ (j:ℤ) ≤ a - 1 + L) ∪
         (Icc 1 n).filter (fun j : ℕ => (j:ℤ) = a - 1 + L + 1) := by
      ext k; simp only [mem_filter, mem_union, mem_Icc]; push_cast; omega
    have hdisj : Disjoint ((Icc 1 n).filter (fun j : ℕ => a ≤ (j:ℤ) ∧ (j:ℤ) ≤ a - 1 + L))
         ((Icc 1 n).filter (fun j : ℕ => (j:ℤ) = a - 1 + L + 1)) := by
      rw [disjoint_left]; intro k h1 h2; simp only [mem_filter] at h1 h2; omega
    rw [hset, sum_union hdisj, ← ih, sum_eqT]
    have e1 : a - 1 + ((L + 1 : ℕ) : ℤ) = a - 1 + L + 1 := by push_cast; ring
    rw [e1, Sc_succ n a c _ (by omega)]
    split_ifs with hT
    · have e2 : (((a - 1 + L + 1).toNat : ℕ) : ℤ) - 1 = a - 1 + L := by omega
      rw [e2]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hc (a - 1 + L + 1).toNat) with h0 | h1
      · rw [h0]; simp
      · rw [h1]; simp only [delta]; push_cast
        have : V + (Sc n a c (a - 1 + ↑L) + 1) + 1 = V + Sc n a c (a - 1 + ↑L) + 1 + 1 := by ring
        rw [this]; ring
    · simp

lemma W_split {Ω : Type*} (n m : ℕ) (X : ℕ → Ω → ℕ) (i : ℕ) (ω : Ω) :
    W n X ω = V n m X i ω + Sc n ((i:ℤ) - m) (fun k => X k ω) ((i:ℤ) + m) := by
  unfold W V Sc
  rw [← sum_filter_add_sum_filter_not (Icc 1 n) (fun k : ℕ => m < Int.natAbs ((k:ℤ) - i))]
  congr 1
  apply sum_congr _ (fun _ _ => rfl)
  apply filter_congr; intro k _; omega

lemma Y_eq {Ω : Type*} (n m : ℕ) (X : ℕ → Ω → ℕ) (i : ℕ) (t : ℤ) (ω : Ω) :
    Y n m X i t ω = V n m X i ω + Sc n ((i:ℤ) - m) (fun k => X k ω) t := rfl

lemma Y'_eq {Ω : Type*} (n m : ℕ) (X : ℕ → Ω → ℕ) (i : ℕ) (t : ℤ) (ω : Ω) :
    Y' n m X i t ω = V n m X i ω + Sc n ((i:ℤ) - m) (fun k => if k = i then 0 else X k ω) t := by
  unfold Y' Sc
  congr 1
  rw [sum_filter, sum_filter]
  apply sum_congr rfl; intro k _
  by_cases hk : k = i
  · simp [hk]
  · simp [hk]

lemma Sc_split (n : ℕ) (a : ℤ) (x : ℕ → ℕ) (T : ℤ) (i : ℕ) (hi : i ∈ Icc 1 n)
    (hai : a ≤ i) (hiT : (i:ℤ) ≤ T) :
    Sc n a x T = x i + Sc n a (fun k => if k = i then 0 else x k) T := by
  unfold Sc
  have : ∀ k, x k = (if k = i then 0 else x k) + (if i = k then x k else 0) := by
    intro k; by_cases hk : k = i
    · subst hk; simp
    · simp [hk, Ne.symm hk]
  conv_lhs => rw [sum_congr rfl (fun k _ => this k)]
  rw [sum_add_distrib, sum_ite_eq, if_pos]
  · ring
  · simp only [mem_filter]; exact ⟨hi, hai, hiT⟩

lemma ptA {Ω : Type*} (n m : ℕ) (X : ℕ → Ω → ℕ) (f : ℕ → ℝ) (ω : Ω) (hx : ∀ k, X k ω ≤ 1)
    (i : ℕ) (hi : i ∈ Icc 1 n) :
    (X i ω : ℝ) * f (W n X ω) = (X i ω : ℝ) * f (V n m X i ω + 1) +
      ∑ j ∈ Finset.Icc 1 n with 0 < |(i : ℤ) - (j : ℕ)| ∧ |(i : ℤ) - (j : ℕ)| ≤ m,
        (X i ω : ℝ) * X j ω * delta f (Y' n m X i ((j : ℤ) - 1) ω + 1) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hx i) with h0 | h1
  · simp [h0]
  · rw [h1, W_split n m X i ω, Sc_split n _ _ _ i hi (by omega) (by omega), h1]
    set x' : ℕ → ℕ := fun k => if k = i then 0 else X k ω with hx'
    have hc : ∀ k, x' k ≤ 1 := by
      intro k; simp only [hx']; split_ifs
      · omega
      · exact hx k
    have ht := tele n ((i:ℤ) - m) x' hc f (V n m X i ω) (2*m+1)
    have e : (i:ℤ) - m - 1 + ((2*m+1 : ℕ):ℤ) = i + m := by push_cast; ring
    rw [e] at ht
    simp only [Nat.cast_one, one_mul]
    have e2 : V n m X i ω + (1 + Sc n (↑i - ↑m) x' (↑i + ↑m)) = V n m X i ω + Sc n (↑i - ↑m) x' (↑i + ↑m) + 1 := by ring
    rw [e2, ← sub_eq_iff_eq_add', ht, sum_filter, sum_filter]
    apply sum_congr rfl; intro j _
    rw [Y'_eq]
    by_cases hji : j = i
    · subst hji; simp [hx']
    · have : x' j = X j ω := by simp [hx', hji]
      rw [this]
      have hji' : (i:ℤ) - j ≠ 0 := by omega
      by_cases hc1 : (i:ℤ) - m ≤ j ∧ (j:ℤ) ≤ i + m
      · rw [if_pos hc1, if_pos]
        rw [abs_pos, abs_le]; exact ⟨hji', by omega, by omega⟩
      · rw [if_neg hc1, if_neg]
        rw [abs_pos, abs_le]; omega

lemma ptB {Ω : Type*} (n m : ℕ) (X : ℕ → Ω → ℕ) (f : ℕ → ℝ) (ω : Ω) (hx : ∀ k, X k ω ≤ 1)
    (i : ℕ) :
    f (W n X ω + 1) = f (V n m X i ω + 1) +
      ∑ j ∈ Finset.Icc 1 n with |(i : ℤ) - (j : ℕ)| ≤ m,
        (X j ω : ℝ) * delta f (Y n m X i ((j : ℤ) - 1) ω + 1) := by
  have ht := tele n ((i:ℤ) - m) (fun k => X k ω) hx f (V n m X i ω) (2*m+1)
  have e : (i:ℤ) - m - 1 + ((2*m+1 : ℕ):ℤ) = i + m := by push_cast; ring
  rw [e] at ht
  rw [W_split n m X i ω, ← sub_eq_iff_eq_add', ht]
  apply sum_congr _ (fun _ _ => rfl)
  apply filter_congr; intro j _; rw [abs_le]; omega

lemma sub_le_n (n : ℕ) (x : ℕ → ℕ) (hx : ∀ k, x k ≤ 1) (s : Finset ℕ) (hs : s ⊆ Icc 1 n) :
    ∑ k ∈ s, x k ≤ n := by
  calc ∑ k ∈ s, x k ≤ ∑ k ∈ s, 1 := sum_le_sum (fun k _ => hx k)
    _ = s.card := by simp
    _ ≤ (Icc 1 n).card := card_le_card hs
    _ = n := by simp

lemma V_le {Ω : Type*} (n m : ℕ) (X : ℕ → Ω → ℕ) (ω : Ω) (hx : ∀ k, X k ω ≤ 1) (i : ℕ) :
    V n m X i ω ≤ n := sub_le_n n (fun k => X k ω) hx _ (filter_subset _ _)

lemma Y_le {Ω : Type*} (n m : ℕ) (X : ℕ → Ω → ℕ) (ω : Ω) (hx : ∀ k, X k ω ≤ 1) (i : ℕ) (t : ℤ) :
    Y n m X i t ω ≤ 2 * n := by
  have := V_le n m X ω hx i
  have := sub_le_n n (fun k => X k ω) hx _ (filter_subset (fun k : ℕ => (i : ℤ) - m ≤ k ∧ (k : ℤ) ≤ t) (Icc 1 n))
  unfold Y; omega

lemma Y'_le {Ω : Type*} (n m : ℕ) (X : ℕ → Ω → ℕ) (ω : Ω) (hx : ∀ k, X k ω ≤ 1) (i : ℕ) (t : ℤ) :
    Y' n m X i t ω ≤ 2 * n := by
  have := V_le n m X ω hx i
  have := sub_le_n n (fun k => X k ω) hx _ (filter_subset (fun k : ℕ => k ≠ i ∧ (i : ℤ) - m ≤ k ∧ (k : ℤ) ≤ t) (Icc 1 n))
  unfold Y'; omega

lemma W_le {Ω : Type*} (n : ℕ) (X : ℕ → Ω → ℕ) (ω : Ω) (hx : ∀ k, X k ω ≤ 1) :
    W n X ω ≤ n := sub_le_n n (fun k => X k ω) hx _ (subset_refl _)

lemma fb_le (f : ℕ → ℝ) (N k : ℕ) (hk : k < N) : |f k| ≤ ∑ j ∈ range N, |f j| :=
  single_le_sum (f := fun j => |f j|) (fun j _ => abs_nonneg _) (mem_range.mpr hk)

lemma cast_le_one' (a : ℕ) (h : a ≤ 1) : |(a:ℝ)| ≤ 1 := by
  rw [abs_of_nonneg (by positivity)]; exact_mod_cast h

lemma integ_bdd {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Ω → ℝ) (hg : Measurable g) (C : ℝ) (hC : ∀ᵐ ω ∂P, |g ω| ≤ C) : Integrable g P :=
  Integrable.of_bound hg.aestronglyMeasurable C (by filter_upwards [hC] with ω h; simpa using h)

lemma meas_V {Ω : Type*} [MeasurableSpace Ω] (n m : ℕ) (X : ℕ → Ω → ℕ) (hX : ∀ i, Measurable (X i)) (i : ℕ) :
    Measurable (V n m X i) := by
  unfold V; apply Finset.measurable_sum; intro k _; exact hX k

lemma meas_Y {Ω : Type*} [MeasurableSpace Ω] (n m : ℕ) (X : ℕ → Ω → ℕ) (hX : ∀ i, Measurable (X i)) (i : ℕ) (t : ℤ) :
    Measurable (Y n m X i t) := by
  unfold Y V; apply Measurable.add <;> apply Finset.measurable_sum <;> intro k _ <;> exact hX k

lemma meas_Y' {Ω : Type*} [MeasurableSpace Ω] (n m : ℕ) (X : ℕ → Ω → ℕ) (hX : ∀ i, Measurable (X i)) (i : ℕ) (t : ℤ) :
    Measurable (Y' n m X i t) := by
  unfold Y' V; apply Measurable.add <;> apply Finset.measurable_sum <;> intro k _ <;> exact hX k

lemma meas_W {Ω : Type*} [MeasurableSpace Ω] (n : ℕ) (X : ℕ → Ω → ℕ) (hX : ∀ i, Measurable (X i)) :
    Measurable (W n X) := by
  unfold W; apply Finset.measurable_sum; intro k _; exact hX k

lemma mcast {Ω : Type*} [MeasurableSpace Ω] (g : Ω → ℕ) (hg : Measurable g) (F : ℕ → ℝ) :
    Measurable (fun ω => F (g ω)) := (measurable_from_top (f := F)).comp hg

theorem basic_identity_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (m : ℕ) (f : ℕ → ℝ) :
    ∫ ω, ((W n X ω : ℝ) * f (W n X ω) - lam P n X * f (W n X ω + 1)) ∂P =
      (∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with 0 < |(i : ℤ) - (j : ℕ)| ∧ |(i : ℤ) - (j : ℕ)| ≤ m,
          ∫ ω, (X i ω : ℝ) * X j ω * delta f (Y' n m X i ((j : ℤ) - 1) ω + 1) ∂P)
      + (∑ i ∈ Finset.Icc 1 n, ∫ ω, ((X i ω : ℝ) - prob P X i) * f (V n m X i ω + 1) ∂P)
      - ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with |(i : ℤ) - (j : ℕ)| ≤ m,
          prob P X i * ∫ ω, (X j ω : ℝ) * delta f (Y n m X i ((j : ℤ) - 1) ω + 1) ∂P := by
  obtain ⟨hXm, _, hX1⟩ := hX
  have hgood : ∀ᵐ ω ∂P, ∀ k, X k ω ≤ 1 := ae_all_iff.mpr hX1
  set Fb := ∑ j ∈ range (2 * n + 3), |f j| with hFb
  have hF : ∀ k, k < 2 * n + 3 → |f k| ≤ Fb := fun k hk => fb_le f _ k hk
  have hD : ∀ y, y ≤ 2 * n → |delta f (y + 1)| ≤ 2 * Fb := by
    intro y hy; unfold delta
    have h1 := hF (y + 1 + 1) (by omega); have h2 := hF (y + 1) (by omega)
    calc |f (y + 1 + 1) - f (y + 1)| ≤ |f (y + 1 + 1)| + |f (y + 1)| := abs_sub _ _
      _ ≤ 2 * Fb := by linarith
  have iA : ∀ i j : ℕ, Integrable (fun ω => (X i ω : ℝ) * X j ω * delta f (Y' n m X i ((j : ℤ) - 1) ω + 1)) P := by
    intro i j
    refine integ_bdd P _ (((mcast _ (hXm i) _).mul (mcast _ (hXm j) _)).mul (mcast _ (meas_Y' n m X hXm i _) (fun y => delta f (y + 1)))) (2 * Fb) ?_
    filter_upwards [hgood] with ω hx
    rw [abs_mul, abs_mul]
    have := hD _ (Y'_le n m X ω hx i ((j:ℤ) - 1))
    have a1 := cast_le_one' _ (hx i); have a2 := cast_le_one' _ (hx j)
    calc |(X i ω : ℝ)| * |(X j ω : ℝ)| * |delta f (Y' n m X i (↑j - 1) ω + 1)| ≤ 1 * 1 * (2 * Fb) := by
          gcongr
      _ = 2 * Fb := by ring
  have iC : ∀ i j : ℕ, Integrable (fun ω => (X j ω : ℝ) * delta f (Y n m X i ((j : ℤ) - 1) ω + 1)) P := by
    intro i j
    refine integ_bdd P _ ((mcast _ (hXm j) _).mul (mcast _ (meas_Y n m X hXm i _) (fun y => delta f (y + 1)))) (2 * Fb) ?_
    filter_upwards [hgood] with ω hx
    rw [abs_mul]
    have := hD _ (Y_le n m X ω hx i ((j:ℤ) - 1))
    have a2 := cast_le_one' _ (hx j)
    calc |(X j ω : ℝ)| * |delta f (Y n m X i (↑j - 1) ω + 1)| ≤ 1 * (2 * Fb) := by
          gcongr
      _ = 2 * Fb := by ring
  have iB : ∀ i : ℕ, Integrable (fun ω => ((X i ω : ℝ) - prob P X i) * f (V n m X i ω + 1)) P := by
    intro i
    refine integ_bdd P _ (((mcast _ (hXm i) _).sub measurable_const).mul (mcast _ (meas_V n m X hXm i) (fun y => f (y + 1)))) ((1 + |prob P X i|) * Fb) ?_
    filter_upwards [hgood] with ω hx
    rw [abs_mul]
    have := hF (V n m X i ω + 1) (by have := V_le n m X ω hx i; omega)
    have a1 := cast_le_one' _ (hx i)
    have : |(X i ω : ℝ) - prob P X i| ≤ 1 + |prob P X i| := (abs_sub _ _).trans (by linarith)
    gcongr
  -- pointwise identity
  have hpt : ∀ᵐ ω ∂P, ((W n X ω : ℝ) * f (W n X ω) - lam P n X * f (W n X ω + 1)) =
      (∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with 0 < |(i : ℤ) - (j : ℕ)| ∧ |(i : ℤ) - (j : ℕ)| ≤ m,
          (X i ω : ℝ) * X j ω * delta f (Y' n m X i ((j : ℤ) - 1) ω + 1))
      + (∑ i ∈ Finset.Icc 1 n, ((X i ω : ℝ) - prob P X i) * f (V n m X i ω + 1))
      - ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with |(i : ℤ) - (j : ℕ)| ≤ m,
          prob P X i * ((X j ω : ℝ) * delta f (Y n m X i ((j : ℤ) - 1) ω + 1)) := by
    filter_upwards [hgood] with ω hx
    have hW : (W n X ω : ℝ) = ∑ i ∈ Icc 1 n, (X i ω : ℝ) := by unfold W; push_cast; rfl
    rw [hW, lam, sum_mul, sum_mul]
    rw [sum_congr rfl (fun i hi => ptA n m X f ω hx i hi)]
    rw [sum_congr rfl (fun i _ => congrArg (fun z => prob P X i * z) (ptB n m X f ω hx i))]
    simp only [mul_add, sum_add_distrib, mul_sum, sub_mul]
    rw [sum_sub_distrib]
    ring
  rw [integral_congr_ae hpt]
  rw [integral_sub, integral_add, integral_finset_sum, integral_finset_sum, integral_finset_sum]
  · congr 1; congr 1
    · apply sum_congr rfl; intro i _; rw [integral_finset_sum]; intro j _; exact iA i j
    · apply sum_congr rfl; intro i _; rw [integral_finset_sum]
      · apply sum_congr rfl; intro j _; rw [integral_const_mul]
      · intro j _; exact (iC i j).const_mul _
  · intro i _; exact integrable_finset_sum _ (fun j _ => (iC i j).const_mul _)
  · intro i _; exact iB i
  · intro i _; exact integrable_finset_sum _ (fun j _ => iA i j)
  · exact integrable_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => iA i j))
  · exact integrable_finset_sum _ (fun i _ => iB i)
  · exact (integrable_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => iA i j))).add
      (integrable_finset_sum _ (fun i _ => iB i))
  · exact integrable_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => (iC i j).const_mul _))

lemma ae_X_eq_ind {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℕ)
    (hX1 : ∀ i, ∀ᵐ ω ∂P, X i ω ≤ 1) (i : ℕ) :
    (fun ω => (X i ω : ℝ)) =ᵐ[P] {ω | X i ω = 1}.indicator 1 := by
  filter_upwards [hX1 i] with ω hω
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hω with h0 | h1
  · simp [Set.indicator, h0]
  · simp [Set.indicator, h1]

lemma meas_set_eq1 {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℕ) (hXm : ∀ i, Measurable (X i)) (i : ℕ) :
    MeasurableSet {ω | X i ω = 1} := hXm i (measurableSet_singleton 1)

lemma int_X {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℕ) (hXm : ∀ i, Measurable (X i))
    (hX1 : ∀ i, ∀ᵐ ω ∂P, X i ω ≤ 1) (i : ℕ) :
    ∫ ω, (X i ω : ℝ) ∂P = prob P X i := by
  rw [integral_congr_ae (ae_X_eq_ind P X hX1 i), integral_indicator_one (meas_set_eq1 X hXm i)]
  rfl

lemma integ_X {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℕ) (hXm : ∀ i, Measurable (X i))
    (hX1 : ∀ i, ∀ᵐ ω ∂P, X i ω ≤ 1) (i : ℕ) : Integrable (fun ω => (X i ω : ℝ)) P :=
  integ_bdd P _ (mcast _ (hXm i) _) 1 (by filter_upwards [hX1 i] with ω h; exact cast_le_one' _ h)

theorem variance_identity_4_7_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (m : ℕ) :
    Var[fun ω => (W n X ω : ℝ); P] = lam P n X
      + (∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with 0 < |(i : ℤ) - (j : ℕ)| ∧ |(i : ℤ) - (j : ℕ)| ≤ m,
          ∫ ω, (X i ω : ℝ) * X j ω ∂P)
      - (∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with |(i : ℤ) - (j : ℕ)| ≤ m,
          prob P X i * prob P X j)
      + ∑ i ∈ Finset.Icc 1 n, ∫ ω, ((X i ω : ℝ) - prob P X i) * (V n m X i ω : ℝ) ∂P := by
  have hb := basic_identity_core P n X hX m (fun w => (w : ℝ))
  obtain ⟨hXm, _, hX1⟩ := hX
  have hgood : ∀ᵐ ω ∂P, ∀ k, X k ω ≤ 1 := ae_all_iff.mpr hX1
  have hd : ∀ y : ℕ, delta (fun w => (w : ℝ)) y = 1 := by intro y; simp [delta]
  simp only [hd, mul_one] at hb
  have hWm : Measurable (fun ω => (W n X ω : ℝ)) := mcast _ (meas_W n X hXm) _
  have hWb : ∀ᵐ ω ∂P, |(W n X ω : ℝ)| ≤ n := by
    filter_upwards [hgood] with ω hx
    rw [abs_of_nonneg (by positivity)]; exact_mod_cast W_le n X ω hx
  have iW : Integrable (fun ω => (W n X ω : ℝ)) P := integ_bdd P _ hWm n hWb
  have iW2 : Integrable (fun ω => (W n X ω : ℝ) * (W n X ω : ℝ)) P :=
    integ_bdd P _ (hWm.mul hWm) (n * n) (by
      filter_upwards [hWb] with ω h; rw [abs_mul]; exact mul_le_mul h h (abs_nonneg _) (by positivity))
  have hEW : ∫ ω, (W n X ω : ℝ) ∂P = lam P n X := by
    have : (fun ω => (W n X ω : ℝ)) = fun ω => ∑ i ∈ Icc 1 n, (X i ω : ℝ) := by
      funext ω; unfold W; push_cast; rfl
    rw [this, integral_finset_sum _ (fun i _ => integ_X P X hXm hX1 i), lam]
    exact sum_congr rfl (fun i _ => int_X P X hXm hX1 i)
  have hmem : MemLp (fun ω => (W n X ω : ℝ)) 2 P :=
    MemLp.of_bound hWm.aestronglyMeasurable n (by filter_upwards [hWb] with ω h; simpa using h)
  rw [variance_eq_sub hmem]
  have e1 : ∀ ω, (W n X ω : ℝ) * ((W n X ω : ℕ) : ℝ) - lam P n X * (((W n X ω + 1 : ℕ)) : ℝ) =
      (W n X ω : ℝ) * (W n X ω : ℝ) - lam P n X * (W n X ω : ℝ) - lam P n X := by
    intro ω; push_cast; ring
  simp only [e1] at hb
  have hL : ∫ ω, ((W n X ω : ℝ) * (W n X ω : ℝ) - lam P n X * (W n X ω : ℝ) - lam P n X) ∂P =
      ∫ ω, (W n X ω : ℝ) * (W n X ω : ℝ) ∂P - lam P n X * lam P n X - lam P n X := by
    rw [integral_sub ?_ (integrable_const _), integral_sub iW2 (iW.const_mul _),
      integral_const_mul, hEW, integral_const]
    · simp
    · exact iW2.sub (iW.const_mul _)
  rw [hL] at hb
  have e2 : ∀ i, ∫ ω, ((X i ω : ℝ) - prob P X i) * ((V n m X i ω + 1 : ℕ) : ℝ) ∂P =
      ∫ ω, ((X i ω : ℝ) - prob P X i) * (V n m X i ω : ℝ) ∂P := by
    intro i
    have iXp : Integrable (fun ω => (X i ω : ℝ) - prob P X i) P := (integ_X P X hXm hX1 i).sub (integrable_const _)
    have iXV : Integrable (fun ω => ((X i ω : ℝ) - prob P X i) * (V n m X i ω : ℝ)) P := by
      refine integ_bdd P _ (((mcast _ (hXm i) _).sub measurable_const).mul (mcast _ (meas_V n m X hXm i) _))
        ((1 + |prob P X i|) * n) ?_
      filter_upwards [hgood] with ω hx
      rw [abs_mul]
      have a1 := cast_le_one' _ (hx i)
      have : |(X i ω : ℝ) - prob P X i| ≤ 1 + |prob P X i| := (abs_sub _ _).trans (by linarith)
      have hv : |(V n m X i ω : ℝ)| ≤ n := by
        rw [abs_of_nonneg (by positivity)]; exact_mod_cast V_le n m X ω hx i
      gcongr
    have : (fun ω => ((X i ω : ℝ) - prob P X i) * ((V n m X i ω + 1 : ℕ) : ℝ)) =
        fun ω => ((X i ω : ℝ) - prob P X i) * (V n m X i ω : ℝ) + ((X i ω : ℝ) - prob P X i) := by
      funext ω; push_cast; ring
    rw [this, integral_add iXV iXp, integral_sub (integ_X P X hXm hX1 i) (integrable_const _),
      int_X P X hXm hX1 i, integral_const]
    simp
  simp only [e2] at hb
  have e3 : ∀ j : ℕ, ∫ ω, (X j ω : ℝ) ∂P = prob P X j := fun j => int_X P X hXm hX1 j
  simp only [e3] at hb
  have hW2 : (∫ ω, ((fun ω => (W n X ω : ℝ)) ^ 2) ω ∂P) = ∫ ω, (W n X ω : ℝ) * (W n X ω : ℝ) ∂P := by
    congr 1; funext ω; simp [sq]
  rw [hW2, hEW]
  linarith

end PoissonDepTrials.MixSqrt

open PoissonDepTrials.MixSqrt


theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (m : ℕ) :
    Var[fun ω => (W n X ω : ℝ); P] = lam P n X
      + (∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with 0 < |(i : ℤ) - (j : ℕ)| ∧ |(i : ℤ) - (j : ℕ)| ≤ m,
          ∫ ω, (X i ω : ℝ) * X j ω ∂P)
      - (∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with |(i : ℤ) - (j : ℕ)| ≤ m,
          prob P X i * prob P X j)
      + ∑ i ∈ Finset.Icc 1 n, ∫ ω, ((X i ω : ℝ) - prob P X i) * (V n m X i ω : ℝ) ∂P := by
  exact variance_identity_4_7_core P n X hX m
