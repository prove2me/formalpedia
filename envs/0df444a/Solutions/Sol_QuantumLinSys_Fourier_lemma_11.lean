-- Prove2me | solution 1 for QuantumLinSys.Fourier.lemma_11
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-14T20:34:50.528926+00:00
-- url     : https://prove2.me/submissions/13f58062-d2a6-4562-acbb-a06c3d01c9db

import Mathlib
import Definitions.Def_QuantumLinSys_Fourier_Setting
import Theorems.Thm_QuantumLinSys_Fourier_eq_28
import Theorems.Thm_QuantumLinSys_Fourier_lemma_13
import Theorems.Thm_QuantumLinSys_Fourier_bound_p13

section Helpers

open scoped BigOperators
open MeasureTheory

private lemma log_two_gt_half : (1 / 2 : ℝ) < Real.log 2 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have hexp_pos : 0 < Real.exp (1 / 2 : ℝ) := Real.exp_pos _
  have hsq : (Real.exp (1 / 2 : ℝ)) ^ 2 < 2 ^ 2 := by
    rw [← Real.exp_nat_mul]
    norm_num
    linarith [Real.exp_one_lt_d9]
  nlinarith

private lemma exp_neg_one_lt_half : Real.exp (-1 : ℝ) < 1 / 2 := by
  rw [Real.exp_neg]
  have h1 : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  rw [inv_eq_one_div]
  exact div_lt_div_of_pos_left (by norm_num) (by norm_num) h1

private lemma exp_neg_nat_mul_log {n : ℕ} {q : ℝ} (hq : 0 < q) :
    Real.exp (-(n : ℝ) * Real.log q) = q⁻¹ ^ n := by
  rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hq, inv_pow]

private lemma exp_neg_eight_mul_log {q : ℝ} (hq : 0 < q) :
    Real.exp (-8 * Real.log q) = q⁻¹ ^ 8 := by
  convert exp_neg_nat_mul_log (n := 8) hq using 2
  norm_num

private lemma exp_neg_sixteen_mul_log {q : ℝ} (hq : 0 < q) :
    Real.exp (-16 * Real.log q) = q⁻¹ ^ 16 := by
  convert exp_neg_nat_mul_log (n := 16) hq using 2
  norm_num

private lemma abs_mul_exp_neg_sq_div_two_le (t : ℝ) :
    |t| * Real.exp (-t ^ 2 / 2) ≤ Real.exp (-t ^ 2 / 4) := by
  have h1 : |t| ≤ t ^ 2 / 4 + 1 := by
    have hsq := sq_nonneg (|t| / 2 - 1)
    have htabs := sq_abs t
    nlinarith
  have h2 : |t| ≤ Real.exp (t ^ 2 / 4) := le_trans h1 (Real.add_one_le_exp (t ^ 2 / 4))
  have h3 : |t| * Real.exp (-t ^ 2 / 2) ≤ Real.exp (t ^ 2 / 4) * Real.exp (-t ^ 2 / 2) :=
    mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
  refine h3.trans_eq ?_
  rw [← Real.exp_add]
  ring_nf

private lemma riemann_sum_antitone_le {f : ℝ → ℝ} {a δ : ℝ} (hδ : 0 ≤ δ) (N : ℕ)
    (hf_anti : AntitoneOn f (Set.Ici a))
    (hf_cont : Continuous f) :
    ∑ n ∈ Finset.range N, δ * f (a + ((n + 1 : ℕ) : ℝ) * δ) ≤
      ∫ x in a..(a + (N : ℝ) * δ), f x := by
  induction N with
  | zero =>
      simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have hN_nonneg : a ≤ a + (N : ℝ) * δ := by
        have : 0 ≤ (N : ℝ) * δ := mul_nonneg (Nat.cast_nonneg N) hδ
        linarith
      have h_step : a + (N : ℝ) * δ ≤ a + ((N + 1 : ℕ) : ℝ) * δ := by
        push_cast
        linarith
      have h_const :
          δ * f (a + ((N + 1 : ℕ) : ℝ) * δ) =
            ∫ _ in (a + (N : ℝ) * δ)..(a + ((N + 1 : ℕ) : ℝ) * δ),
              f (a + ((N + 1 : ℕ) : ℝ) * δ) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        have hdiff : (a + ((N + 1 : ℕ) : ℝ) * δ) - (a + (N : ℝ) * δ) = δ := by
          push_cast; ring
        rw [hdiff]
      have h_mono :
          ∫ _ in (a + (N : ℝ) * δ)..(a + ((N + 1 : ℕ) : ℝ) * δ),
              f (a + ((N + 1 : ℕ) : ℝ) * δ) ≤
            ∫ x in (a + (N : ℝ) * δ)..(a + ((N + 1 : ℕ) : ℝ) * δ), f x := by
        apply intervalIntegral.integral_mono_on h_step
        · exact continuous_const.intervalIntegrable _ _
        · exact hf_cont.intervalIntegrable _ _
        · intro x hx
          apply hf_anti
          · exact le_trans hN_nonneg hx.1
          · exact le_trans hN_nonneg h_step
          · exact hx.2
      have h_adj :
          (∫ x in a..(a + (N : ℝ) * δ), f x) +
              (∫ x in (a + (N : ℝ) * δ)..(a + ((N + 1 : ℕ) : ℝ) * δ), f x) =
            ∫ x in a..(a + ((N + 1 : ℕ) : ℝ) * δ), f x :=
        intervalIntegral.integral_add_adjacent_intervals
          (hf_cont.intervalIntegrable (μ := volume) a (a + (N : ℝ) * δ))
          (hf_cont.intervalIntegrable (μ := volume) (a + (N : ℝ) * δ) (a + ((N + 1 : ℕ) : ℝ) * δ))
      have h_step2 :
          δ * f (a + ((N + 1 : ℕ) : ℝ) * δ) ≤
            ∫ x in (a + (N : ℝ) * δ)..(a + ((N + 1 : ℕ) : ℝ) * δ), f x :=
        h_const.trans_le h_mono
      calc
        ∑ n ∈ Finset.range N, δ * f (a + ((n + 1 : ℕ) : ℝ) * δ) +
            δ * f (a + ((N + 1 : ℕ) : ℝ) * δ)
            ≤ (∫ x in a..(a + (N : ℝ) * δ), f x) +
                (∫ x in (a + (N : ℝ) * δ)..(a + ((N + 1 : ℕ) : ℝ) * δ), f x) :=
              add_le_add ih h_step2
        _ = ∫ x in a..(a + ((N + 1 : ℕ) : ℝ) * δ), f x := h_adj

private lemma gaussian_half_integral_quarter (B : ℝ) (hB : 0 ≤ B) :
    ∫ x in (0 : ℝ)..B, Real.exp (-x ^ 2 / 4) ≤ Real.sqrt Real.pi := by
  let g : ℝ → ℝ := fun x => Real.exp (-(1 / 4 : ℝ) * x ^ 2)
  have hg_eq : (fun x => Real.exp (-x ^ 2 / 4)) = g := by
    ext x; dsimp [g]; ring_nf
  rw [hg_eq]
  have hg_int : Integrable g volume := integrable_exp_neg_mul_sq (by norm_num)
  have hneg : ∫ x in (-B)..0, g x = ∫ x in (0 : ℝ)..B, g x := by
    have hcomp := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := B) g
    have heven : (fun x => g (-x)) = g := by
      ext x; dsimp [g]; ring_nf
    simpa [heven] using hcomp.symm
  have hadd :
      (∫ x in (-B)..0, g x) + (∫ x in (0 : ℝ)..B, g x) = ∫ x in (-B)..B, g x :=
    intervalIntegral.integral_add_adjacent_intervals
      (hg_int.intervalIntegrable (μ := volume)) (hg_int.intervalIntegrable (μ := volume))
  have hle_total : ∫ x in (-B)..B, g x ≤ ∫ x : ℝ, g x := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    apply MeasureTheory.setIntegral_le_integral hg_int
    filter_upwards with x
    exact (Real.exp_pos _).le
  have hgauss : ∫ x : ℝ, g x = 2 * Real.sqrt Real.pi := by
    dsimp [g]
    rw [integral_gaussian (1 / 4 : ℝ)]
    have h4 : Real.pi / (1 / 4 : ℝ) = 2 ^ 2 * Real.pi := by ring
    rw [h4, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  have h2 : 2 * ∫ x in (0 : ℝ)..B, g x ≤ 2 * Real.sqrt Real.pi := by
    calc
      2 * ∫ x in (0 : ℝ)..B, g x = (∫ x in (0 : ℝ)..B, g x) + (∫ x in (0 : ℝ)..B, g x) :=
        two_mul _
      _ = (∫ x in (-B)..0, g x) + (∫ x in (0 : ℝ)..B, g x) := by rw [← hneg]
      _ = ∫ x in (-B)..B, g x := hadd
      _ ≤ ∫ x : ℝ, g x := hle_total
      _ = 2 * Real.sqrt Real.pi := hgauss
  linarith

private lemma antitone_exp_neg_sq_div (c : ℝ) (hc : 0 < c) :
    AntitoneOn (fun t : ℝ => Real.exp (-t ^ 2 / c)) (Set.Ici 0) := by
  intro x hx y hy hxy
  rw [Real.exp_le_exp]
  have hx0 : 0 ≤ x := hx
  have hsq : x ^ 2 ≤ y ^ 2 := by nlinarith
  exact div_le_div_of_nonneg_right (by linarith) hc.le

private lemma sum_Icc_int_even_zero {K : ℕ} {g : ℤ → ℝ}
    (hg_even : ∀ k : ℤ, g (-k) = g k) (hg0 : g 0 = 0) :
    ∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), g k =
      2 * ∑ n ∈ Finset.range K, g ((n + 1 : ℕ) : ℤ) := by
  induction K with
  | zero =>
      simp [hg0]
  | succ K ih =>
      have hset :
          Finset.Icc (-((K + 1 : ℕ) : ℤ)) ((K + 1 : ℕ) : ℤ) =
            insert ((K + 1 : ℕ) : ℤ)
              (insert (-((K + 1 : ℕ) : ℤ)) (Finset.Icc (-(K : ℤ)) (K : ℤ))) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hmem1 : ((K + 1 : ℕ) : ℤ) ∉
          insert (-((K + 1 : ℕ) : ℤ)) (Finset.Icc (-(K : ℤ)) (K : ℤ)) := by
        simp only [Finset.mem_insert, Finset.mem_Icc]
        omega
      have hmem2 : (-((K + 1 : ℕ) : ℤ)) ∉ Finset.Icc (-(K : ℤ)) (K : ℤ) := by
        simp only [Finset.mem_Icc]
        omega
      rw [hset, Finset.sum_insert hmem1, Finset.sum_insert hmem2, ih, Finset.sum_range_succ]
      rw [hg_even ((K + 1 : ℕ) : ℤ)]
      ring

private def intTailEquiv (s : Finset ℤ) (K : ℕ)
    (hs : ∀ k : ℤ, k ∈ s ↔ -(K : ℤ) ≤ k ∧ k ≤ (K : ℤ)) :
    ℕ ⊕ ℕ ≃ {k : ℤ // k ∉ s} where
  toFun p := match p with
    | Sum.inl n => ⟨((n + 1 + K : ℕ) : ℤ), by
        rw [hs]; omega⟩
    | Sum.inr n => ⟨-((n + 1 + K : ℕ) : ℤ), by
        rw [hs]; omega⟩
  invFun k :=
    if k.1 < 0 then Sum.inr (k.1.natAbs - (K + 1)) else Sum.inl (k.1.natAbs - (K + 1))
  left_inv p := by
    cases p with
    | inl n =>
        have h1 : ¬(((n + 1 + K : ℕ) : ℤ) < 0) := by omega
        simp only [h1, ↓reduceIte, Int.natAbs_natCast]
        congr 1
        omega
    | inr n =>
        have h1 : (-((n + 1 + K : ℕ) : ℤ)) < 0 := by omega
        simp only [h1, ↓reduceIte, Int.natAbs_neg, Int.natAbs_natCast]
        congr 1
        omega
  right_inv k := by
    ext
    have hk := k.2
    rw [hs] at hk
    by_cases hneg : k.1 < 0
    · simp only [hneg, ↓reduceIte]
      omega
    · simp only [hneg, ↓reduceIte]
      omega

private lemma exp_neg_sq_summable_shift (K : ℕ) (c : ℝ) (hc : 0 < c) :
    Summable (fun n : ℕ => Real.exp (-c * ((K + 1 + n : ℕ) : ℝ) ^ 2)) := by
  have hr0 : 0 ≤ Real.exp (-c) := (Real.exp_pos _).le
  have hr1 : Real.exp (-c) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hgeom : Summable (fun n : ℕ => (Real.exp (-c)) ^ (n + 1)) := by
    have := (summable_geometric_of_lt_one hr0 hr1).mul_left (Real.exp (-c))
    simpa [pow_succ'] using this
  refine Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) ?_ hgeom
  intro n
  have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.succ_pos n)
  have hkn : ((n + 1 : ℕ) : ℝ) ≤ ((K + 1 + n : ℕ) : ℝ) := by
    exact_mod_cast (show n + 1 ≤ K + 1 + n by omega)
  have hsq : ((n + 1 : ℕ) : ℝ) ≤ ((K + 1 + n : ℕ) : ℝ) ^ 2 := by nlinarith
  have hexp : -c * ((K + 1 + n : ℕ) : ℝ) ^ 2 ≤ ((n + 1 : ℕ) : ℝ) * (-c) := by nlinarith
  calc
    Real.exp (-c * ((K + 1 + n : ℕ) : ℝ) ^ 2)
        ≤ Real.exp (((n + 1 : ℕ) : ℝ) * (-c)) := Real.exp_le_exp.mpr hexp
    _ = (Real.exp (-c)) ^ (n + 1) := Real.exp_nat_mul (-c) (n + 1)

private lemma summable_int_of_shift {f : ℤ → ℝ}
    (h1 : Summable (fun n : ℕ => f ((n + 1 : ℕ) : ℤ)))
    (h2 : Summable (fun n : ℕ => f (-((n + 1 : ℕ) : ℤ)))) :
    Summable f := by
  let s0 : Finset ℤ := {0}
  have hs0 : ∀ k : ℤ, k ∈ s0 ↔ -(0 : ℕ) ≤ k ∧ k ≤ (0 : ℕ) := by
    intro k; simp only [s0, Finset.mem_singleton, Nat.cast_zero, neg_zero]; omega
  let e := intTailEquiv s0 0 hs0
  have ha : Summable ((fun p : ℕ ⊕ ℕ => f (e p).1) ∘ Sum.inl) := by
    change Summable (fun n : ℕ => f ((n + 1 + 0 : ℕ) : ℤ))
    exact h1
  have hb : Summable ((fun p : ℕ ⊕ ℕ => f (e p).1) ∘ Sum.inr) := by
    change Summable (fun n : ℕ => f (-((n + 1 + 0 : ℕ) : ℤ)))
    exact h2
  have hsum_e : Summable (fun p : ℕ ⊕ ℕ => f (e p).1) :=
    (HasSum.sum ha.hasSum hb.hasSum).summable
  have hc : Summable (fun k : {k : ℤ // k ∉ s0} => f k.1) := (e.summable_iff).mp hsum_e
  exact (Finset.summable_compl_iff s0).mp hc

private lemma exp_neg_int_sq_summable (c : ℝ) (hc : 0 < c) :
    Summable (fun k : ℤ => Real.exp (-c * (k : ℝ) ^ 2)) := by
  have h0 := exp_neg_sq_summable_shift 0 c hc
  have heq : (fun n : ℕ => Real.exp (-c * ((0 + 1 + n : ℕ) : ℝ) ^ 2)) =
      (fun n : ℕ => Real.exp (-c * ((n + 1 : ℕ) : ℝ) ^ 2)) := by
    ext n
    rw [show 0 + 1 + n = n + 1 by omega]
  have hs : Summable (fun n : ℕ => Real.exp (-c * ((n + 1 : ℕ) : ℝ) ^ 2)) := by
    rwa [heq] at h0
  apply summable_int_of_shift
  · simpa only [Int.cast_natCast] using hs
  · simpa only [Int.cast_neg, Int.cast_natCast, neg_sq] using hs

private lemma tsum_compl_even_eq {s : Finset ℤ} {K : ℕ}
    (hs : ∀ k : ℤ, k ∈ s ↔ -(K : ℤ) ≤ k ∧ k ≤ (K : ℤ))
    {g : ℤ → ℝ} (hg_even : ∀ k : ℤ, g (-k) = g k) (hg_sum : Summable g) :
    ∑' k : {k : ℤ // k ∉ s}, g k.1 = 2 * ∑' n : ℕ, g ((K + 1 + n : ℕ) : ℤ) := by
  let e := intTailEquiv s K hs
  have hc : Summable (fun k : {k : ℤ // k ∉ s} => g k.1) :=
    (Finset.summable_compl_iff s).mpr hg_sum
  have hsum_e : Summable (fun p : ℕ ⊕ ℕ => g (e p).1) := (e.summable_iff).mpr hc
  have h1 : Summable ((fun p : ℕ ⊕ ℕ => g (e p).1) ∘ Sum.inl) :=
    hsum_e.comp_injective Sum.inl_injective
  have h2 : Summable ((fun p : ℕ ⊕ ℕ => g (e p).1) ∘ Sum.inr) :=
    hsum_e.comp_injective Sum.inr_injective
  rw [← e.tsum_eq (fun k => g k.1), Summable.tsum_sum h1 h2]
  have heq1 : (fun n : ℕ => g (e (Sum.inl n)).1) =
      (fun n : ℕ => g ((K + 1 + n : ℕ) : ℤ)) := by
    ext n; dsimp [e, intTailEquiv]; congr 1; ring
  have heq2 : (fun n : ℕ => g (e (Sum.inr n)).1) =
      (fun n : ℕ => g ((K + 1 + n : ℕ) : ℤ)) := by
    ext n; dsimp [e, intTailEquiv]; rw [hg_even]; congr 1; ring
  change (∑' n : ℕ, g (e (Sum.inl n)).1) + (∑' n : ℕ, g (e (Sum.inr n)).1) = _
  rw [heq1, heq2, two_mul]

private lemma tsum_compl_Icc_norm_bound {K : ℕ} {f : ℤ → ℂ} {g : ℤ → ℝ}
    (hf_sum : Summable f) (hf_norm_sum : Summable (fun k : ℤ => ‖f k‖))
    (hg_sum : Summable g) (hg_even : ∀ k : ℤ, g (-k) = g k)
    (hfg : ∀ k : ℤ, ‖f k‖ ≤ g k) :
    ‖∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), f k - ∑' k : ℤ, f k‖ ≤
      2 * ∑' n : ℕ, g ((K + 1 + n : ℕ) : ℤ) := by
  let s : Finset ℤ := Finset.Icc (-(K : ℤ)) (K : ℤ)
  have hs : ∀ k : ℤ, k ∈ s ↔ -(K : ℤ) ≤ k ∧ k ≤ (K : ℤ) := fun k => Finset.mem_Icc
  let eqv : {k : ℤ // k ∉ s} ≃ ↑((s : Set ℤ)ᶜ) :=
    Equiv.subtypeEquivRight (fun k => by simp [Set.mem_compl_iff])
  have hdiff :
      ∑ k ∈ s, f k - ∑' k : ℤ, f k = - ∑' k : {k : ℤ // k ∉ s}, f k.1 := by
    have hcomp := hf_sum.sum_add_tsum_compl (s := s)
    have hts : ∑' k : ↑((s : Set ℤ)ᶜ), f k.1 = ∑' k : {k : ℤ // k ∉ s}, f k.1 :=
      (eqv.tsum_eq (fun k => f k.1)).symm
    calc
      ∑ k ∈ s, f k - ∑' k : ℤ, f k
          = ∑ k ∈ s, f k - (∑ k ∈ s, f k + ∑' k : ↑((s : Set ℤ)ᶜ), f k.1) := by rw [hcomp]
      _ = - ∑' k : {k : ℤ // k ∉ s}, f k.1 := by rw [hts]; ring
  have hc_norm : Summable (fun k : {k : ℤ // k ∉ s} => ‖f k.1‖) :=
    (Finset.summable_compl_iff s).mpr hf_norm_sum
  have hc_g : Summable (fun k : {k : ℤ // k ∉ s} => g k.1) :=
    (Finset.summable_compl_iff s).mpr hg_sum
  have h1 : ‖∑' k : {k : ℤ // k ∉ s}, f k.1‖ ≤ ∑' k : {k : ℤ // k ∉ s}, ‖f k.1‖ :=
    norm_tsum_le_tsum_norm hc_norm
  have h2 : ∑' k : {k : ℤ // k ∉ s}, ‖f k.1‖ ≤ ∑' k : {k : ℤ // k ∉ s}, g k.1 :=
    hc_norm.tsum_le_tsum (fun k => hfg k.1) hc_g
  have h3 : ∑' k : {k : ℤ // k ∉ s}, g k.1 = 2 * ∑' n : ℕ, g ((K + 1 + n : ℕ) : ℤ) :=
    tsum_compl_even_eq hs hg_even hg_sum
  rw [hdiff, norm_neg]
  exact le_trans h1 (h2.trans_eq h3)

private lemma tsum_int_split_zero_bound {g h : ℤ → ℝ}
    (hg_nonneg : ∀ k : ℤ, 0 ≤ g k) (hh_sum : Summable h)
    (hh_even : ∀ k : ℤ, h (-k) = h k) (hgh : ∀ k : ℤ, k ≠ 0 → g k ≤ h k) :
    Summable g ∧ ∑' k : ℤ, g k ≤ g 0 + 2 * ∑' n : ℕ, h ((n + 1 : ℕ) : ℤ) := by
  let s0 : Finset ℤ := {0}
  have hs0 : ∀ k : ℤ, k ∈ s0 ↔ -(0 : ℕ) ≤ k ∧ k ≤ (0 : ℕ) := by
    intro k; simp only [s0, Finset.mem_singleton, Nat.cast_zero, neg_zero]; omega
  let eqv : {k : ℤ // k ∉ s0} ≃ ↑((s0 : Set ℤ)ᶜ) :=
    Equiv.subtypeEquivRight (fun k => by simp [Set.mem_compl_iff])
  have hc_h : Summable (fun k : {k : ℤ // k ∉ s0} => h k.1) :=
    (Finset.summable_compl_iff s0).mpr hh_sum
  have hc_g : Summable (fun k : {k : ℤ // k ∉ s0} => g k.1) := by
    refine Summable.of_nonneg_of_le (fun k => hg_nonneg k.1) ?_ hc_h
    intro k
    have hk : k.1 ≠ 0 := by
      have hk' := k.2
      simp only [s0, Finset.mem_singleton] at hk'
      exact hk'
    exact hgh k.1 hk
  have hg_sum : Summable g := (Finset.summable_compl_iff s0).mp hc_g
  have hsplit := hg_sum.sum_add_tsum_compl (s := s0)
  have hsum0 : ∑ k ∈ s0, g k = g 0 := by simp [s0]
  have hts_eq : ∑' k : ↑((s0 : Set ℤ)ᶜ), g k.1 = ∑' k : {k : ℤ // k ∉ s0}, g k.1 :=
    (eqv.tsum_eq (fun k => g k.1)).symm
  have hle_tail : ∑' k : {k : ℤ // k ∉ s0}, g k.1 ≤ ∑' k : {k : ℤ // k ∉ s0}, h k.1 := by
    apply hc_g.tsum_le_tsum _ hc_h
    intro k
    have hk : k.1 ≠ 0 := by
      have hk' := k.2
      simp only [s0, Finset.mem_singleton] at hk'
      exact hk'
    exact hgh k.1 hk
  have heq_h : ∑' k : {k : ℤ // k ∉ s0}, h k.1 = 2 * ∑' n : ℕ, h ((n + 1 : ℕ) : ℤ) := by
    have ht := tsum_compl_even_eq hs0 hh_even hh_sum
    have heq_n : (fun n : ℕ => h ((0 + 1 + n : ℕ) : ℤ)) =
        (fun n : ℕ => h ((n + 1 : ℕ) : ℤ)) := by
      ext n; congr 2; omega
    rwa [heq_n] at ht
  refine ⟨hg_sum, ?_⟩
  linarith

private lemma exp_neg_i_mul_ne_one {θ : ℝ} (hθ0 : θ ≠ 0) (hθ1 : |θ| ≤ 1) :
    Complex.exp (-Complex.I * (θ : ℂ)) ≠ 1 := by
  intro h
  rcases Complex.exp_eq_one_iff.mp h with ⟨n, hn⟩
  have him := congrArg Complex.im hn
  have him' : -θ = (n : ℝ) * (2 * Real.pi) := by
    simpa [Complex.neg_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im] using him
  by_cases hn0 : n = 0
  · subst hn0
    simp at him'
    exact hθ0 him'
  · have hn_abs : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn0
    have hpi : 3 < Real.pi := Real.pi_gt_three
    have hpi2 : |2 * Real.pi| = 2 * Real.pi := abs_of_pos (by linarith)
    have hθ_abs : |θ| = |(n : ℝ)| * (2 * Real.pi) := by
      calc
        |θ| = |-θ| := (abs_neg θ).symm
        _ = |(n : ℝ) * (2 * Real.pi)| := by rw [him']
        _ = |(n : ℝ)| * |2 * Real.pi| := abs_mul _ _
        _ = |(n : ℝ)| * (2 * Real.pi) := by rw [hpi2]
    nlinarith

private lemma tsum_geom_tail_bound {a : ℝ} (ha : 1 ≤ a) {f : ℕ → ℝ}
    (hf0 : ∀ n : ℕ, 0 ≤ f n)
    (hf_le : ∀ n : ℕ, f n ≤ Real.exp (-(((n + 1 : ℕ) : ℝ) * a))) :
    Summable f ∧ ∑' n : ℕ, f n ≤ 2 * Real.exp (-a) := by
  let r : ℝ := Real.exp (-a)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr_half : r < 1 / 2 := by
    have hle : r ≤ Real.exp (-1 : ℝ) := Real.exp_le_exp.mpr (by linarith)
    exact lt_of_le_of_lt hle exp_neg_one_lt_half
  have hr1 : r < 1 := by linarith
  have hgeom_sum : Summable (fun n : ℕ => r ^ (n + 1)) := by
    have := (summable_geometric_of_lt_one hr0 hr1).mul_left r
    simpa [pow_succ'] using this
  have hle_pow : ∀ n : ℕ, f n ≤ r ^ (n + 1) := by
    intro n
    refine (hf_le n).trans_eq ?_
    have hmul : -(((n + 1 : ℕ) : ℝ) * a) = ((n + 1 : ℕ) : ℝ) * (-a) := by ring
    rw [hmul, Real.exp_nat_mul]
  have hf_sum : Summable f := Summable.of_nonneg_of_le hf0 hle_pow hgeom_sum
  have htsum_le : ∑' n : ℕ, f n ≤ ∑' n : ℕ, r ^ (n + 1) :=
    hf_sum.tsum_le_tsum hle_pow hgeom_sum
  have hgeom_val : ∑' n : ℕ, r ^ (n + 1) = r * (1 - r)⁻¹ := by
    have hpow : (fun n : ℕ => r ^ (n + 1)) = (fun n : ℕ => r * r ^ n) := by
      ext n; rw [pow_succ']
    rw [hpow, tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  have h1mr : 1 / 2 < 1 - r := by linarith
  have hbound : r * (1 - r)⁻¹ ≤ 2 * r := by
    rw [← div_eq_mul_inv, div_le_iff₀ (by linarith)]
    nlinarith
  exact ⟨hf_sum, le_trans htsum_le (hgeom_val ▸ hbound)⟩

private lemma hDisc_eq_geom (J K : ℕ) (Δy Δz x yJ : ℝ)
    (hJ : (J : ℝ) * Δy = yJ)
    (h_ne : ∀ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), k ≠ 0 →
      Complex.exp (-Complex.I * (x : ℂ) * (Δy : ℂ) * ((k : ℂ) * (Δz : ℂ))) ≠ 1) :
    QuantumLinSys.Fourier.hDisc J K Δy Δz x =
      (Complex.I * (Δy : ℂ) / (Real.sqrt (2 * Real.pi) : ℂ)) *
        ∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
          if k = 0 then (0 : ℂ) else
            (Δz : ℂ) * ((k : ℂ) * (Δz : ℂ)) *
              (Real.exp (-((k : ℝ) * Δz) ^ 2 / 2) : ℂ) *
              (1 - Complex.exp (-Complex.I * (x : ℂ) * (yJ : ℂ) * ((k : ℂ) * (Δz : ℂ)))) /
                (1 - Complex.exp (-Complex.I * (x : ℂ) * (Δy : ℂ) * ((k : ℂ) * (Δz : ℂ)))) := by
  unfold QuantumLinSys.Fourier.hDisc
  simp only [Complex.ofReal_mul, Complex.ofReal_intCast, Complex.ofReal_natCast]
  have h1 :
      ∑ j ∈ Finset.range J, (Δy : ℂ) *
        ∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
          (Δz : ℂ) * ((k : ℂ) * (Δz : ℂ)) *
            (Real.exp (-((k : ℝ) * Δz) ^ 2 / 2) : ℂ) *
            Complex.exp (-Complex.I * (x : ℂ) * ((j : ℂ) * (Δy : ℂ)) * ((k : ℂ) * (Δz : ℂ))) =
        (Δy : ℂ) *
          ∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
            ∑ j ∈ Finset.range J,
              (Δz : ℂ) * ((k : ℂ) * (Δz : ℂ)) *
                (Real.exp (-((k : ℝ) * Δz) ^ 2 / 2) : ℂ) *
                Complex.exp (-Complex.I * (x : ℂ) * ((j : ℂ) * (Δy : ℂ)) * ((k : ℂ) * (Δz : ℂ))) := by
    rw [← Finset.mul_sum, Finset.sum_comm]
  rw [h1]
  have hpref :
      (Complex.I / (Real.sqrt (2 * Real.pi) : ℂ)) * ((Δy : ℂ) *
        ∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
          ∑ j ∈ Finset.range J,
            (Δz : ℂ) * ((k : ℂ) * (Δz : ℂ)) *
              (Real.exp (-((k : ℝ) * Δz) ^ 2 / 2) : ℂ) *
              Complex.exp (-Complex.I * (x : ℂ) * ((j : ℂ) * (Δy : ℂ)) * ((k : ℂ) * (Δz : ℂ)))) =
        (Complex.I * (Δy : ℂ) / (Real.sqrt (2 * Real.pi) : ℂ)) *
          ∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
            ∑ j ∈ Finset.range J,
              (Δz : ℂ) * ((k : ℂ) * (Δz : ℂ)) *
                (Real.exp (-((k : ℝ) * Δz) ^ 2 / 2) : ℂ) *
                Complex.exp (-Complex.I * (x : ℂ) * ((j : ℂ) * (Δy : ℂ)) * ((k : ℂ) * (Δz : ℂ))) := by
    ring
  rw [hpref]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hk0 : k = 0
  · subst hk0
    simp
  · simp only [hk0, ↓reduceIte]
    have hpow :
        ∀ j : ℕ,
          Complex.exp (-Complex.I * (x : ℂ) * ((j : ℂ) * (Δy : ℂ)) * ((k : ℂ) * (Δz : ℂ))) =
          (Complex.exp (-Complex.I * (x : ℂ) * (Δy : ℂ) * ((k : ℂ) * (Δz : ℂ)))) ^ j := by
      intro j
      rw [← Complex.exp_nat_mul]
      congr 1
      ring
    simp_rw [hpow, ← Finset.mul_sum]
    rw [geom_sum_eq (h_ne k hk hk0) J]
    have hpowJ :
        (Complex.exp (-Complex.I * (x : ℂ) * (Δy : ℂ) * ((k : ℂ) * (Δz : ℂ)))) ^ J =
        Complex.exp (-Complex.I * (x : ℂ) * (yJ : ℂ) * ((k : ℂ) * (Δz : ℂ))) := by
      rw [← Complex.exp_nat_mul]
      congr 1
      have hJ_c : (J : ℂ) * (Δy : ℂ) = (yJ : ℂ) := by exact_mod_cast hJ
      calc
        (J : ℂ) * (-Complex.I * (x : ℂ) * (Δy : ℂ) * ((k : ℂ) * (Δz : ℂ)))
            = -Complex.I * (x : ℂ) * ((J : ℂ) * (Δy : ℂ)) * ((k : ℂ) * (Δz : ℂ)) := by ring
        _ = -Complex.I * (x : ℂ) * (yJ : ℂ) * ((k : ℂ) * (Δz : ℂ)) := by rw [hJ_c]
    rw [hpowJ]
    have hneg_div :
        ∀ u v : ℂ, v ≠ 1 → (u - 1) / (v - 1) = (1 - u) / (1 - v) := by
      intro u v hv
      have hne : v - 1 ≠ 0 := sub_ne_zero.mpr hv
      have hne' : 1 - v ≠ 0 := sub_ne_zero.mpr hv.symm
      rw [div_eq_div_iff hne hne']
      ring
    rw [hneg_div _ _ (h_ne k hk hk0), mul_div_assoc']

private noncomputable def fbTerm (Δz x yJ : ℝ) (k : ℤ) : ℂ :=
  (Δz : ℂ) * (Real.exp (-((k : ℝ) * Δz) ^ 2 / 2) : ℂ) *
    (1 - Complex.exp (-Complex.I * (x : ℂ) * (yJ : ℂ) * ((k : ℂ) * (Δz : ℂ))))

private lemma fbTerm_norm_le {Δz x yJ : ℝ} (hΔz : 0 < Δz) (k : ℤ) :
    ‖fbTerm Δz x yJ k‖ ≤ 2 * Δz * Real.exp (-(Δz ^ 2 / 2) * (k : ℝ) ^ 2) := by
  dsimp [fbTerm]
  rw [norm_mul, norm_mul, Complex.norm_of_nonneg hΔz.le,
    Complex.norm_of_nonneg (Real.exp_pos _).le]
  have hexp_norm :
      ‖Complex.exp (-Complex.I * (x : ℂ) * (yJ : ℂ) * ((k : ℂ) * (Δz : ℂ)))‖ = 1 := by
    have harg :
        -Complex.I * (x : ℂ) * (yJ : ℂ) * ((k : ℂ) * (Δz : ℂ)) =
          Complex.I * ((-(x * yJ * ((k : ℝ) * Δz)) : ℝ) : ℂ) := by
      push_cast; ring
    rw [harg, Complex.norm_exp_I_mul_ofReal]
  have hsub :
      ‖1 - Complex.exp (-Complex.I * (x : ℂ) * (yJ : ℂ) * ((k : ℂ) * (Δz : ℂ)))‖ ≤ 2 := by
    calc
      ‖1 - Complex.exp (-Complex.I * (x : ℂ) * (yJ : ℂ) * ((k : ℂ) * (Δz : ℂ)))‖
          ≤ ‖(1 : ℂ)‖ +
              ‖Complex.exp (-Complex.I * (x : ℂ) * (yJ : ℂ) * ((k : ℂ) * (Δz : ℂ)))‖ :=
            norm_sub_le _ _
      _ = 2 := by rw [norm_one, hexp_norm]; norm_num
  have hexp_eq :
      Real.exp (-((k : ℝ) * Δz) ^ 2 / 2) = Real.exp (-(Δz ^ 2 / 2) * (k : ℝ) ^ 2) := by
    congr 1; ring
  rw [hexp_eq]
  calc
    Δz * Real.exp (-(Δz ^ 2 / 2) * (k : ℝ) ^ 2) *
        ‖1 - Complex.exp (-Complex.I * (x : ℂ) * (yJ : ℂ) * ((k : ℂ) * (Δz : ℂ)))‖
        ≤ Δz * Real.exp (-(Δz ^ 2 / 2) * (k : ℝ) ^ 2) * 2 := by gcongr
    _ = 2 * Δz * Real.exp (-(Δz ^ 2 / 2) * (k : ℝ) ^ 2) := by ring

private lemma fs1a_bound {J K : ℕ} {Δy Δz x yJ L ε : ℝ}
    (hL : 1 / 2 < L) (hε : 0 < ε) (hΔy_pos : 0 < Δy) (hΔz_pos : 0 < Δz)
    (hΔy_ub : Δy ≤ (1 / 64 : ℝ) * (ε / Real.sqrt L))
    (hx_ne : x ≠ 0) (hJΔy : (J : ℝ) * Δy = yJ) (hKΔz : (K : ℝ) * Δz = 4 * Real.sqrt L)
    (hθ_bound : ∀ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), |x * Δy * ((k : ℝ) * Δz)| ≤ 1) :
    ‖QuantumLinSys.Fourier.hDisc J K Δy Δz x -
        (1 / ((Real.sqrt (2 * Real.pi) : ℂ) * (x : ℂ))) *
          ∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), fbTerm Δz x yJ k‖ ≤ ε / 4 := by
  have hL_pos : 0 < L := by linarith
  have hsqrtL_pos : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL_pos
  have hzK_pos : 0 < (K : ℝ) * Δz := by rw [hKΔz]; positivity
  have hθ_ne_one :
      ∀ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), k ≠ 0 →
        Complex.exp (-Complex.I * (x : ℂ) * (Δy : ℂ) * ((k : ℂ) * (Δz : ℂ))) ≠ 1 := by
    intro k hk hk0
    have hθ_ne : x * Δy * ((k : ℝ) * Δz) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hx_ne hΔy_pos.ne')
        (mul_ne_zero (Int.cast_ne_zero.mpr hk0) hΔz_pos.ne')
    have h1 := exp_neg_i_mul_ne_one hθ_ne (hθ_bound k hk)
    convert h1 using 2
    push_cast; ring
  have hS0_eq := hDisc_eq_geom J K Δy Δz x yJ hJΔy hθ_ne_one
  let term : ℤ → ℂ := fun k =>
    if k = 0 then 0 else
      fbTerm Δz x yJ k * (Complex.I * (Δy : ℂ) * ((k : ℂ) * (Δz : ℂ)) /
          (1 - Complex.exp (-Complex.I * (x : ℂ) * (Δy : ℂ) * ((k : ℂ) * (Δz : ℂ)))) -
        1 / (x : ℂ))
  have hdiff_eq :
      QuantumLinSys.Fourier.hDisc J K Δy Δz x -
          (1 / ((Real.sqrt (2 * Real.pi) : ℂ) * (x : ℂ))) *
            ∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), fbTerm Δz x yJ k =
        (1 / (Real.sqrt (2 * Real.pi) : ℂ)) *
          ∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), term k := by
    rw [hS0_eq]
    have hS1_rew :
        (1 / ((Real.sqrt (2 * Real.pi) : ℂ) * (x : ℂ))) *
            ∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), fbTerm Δz x yJ k =
          (1 / (Real.sqrt (2 * Real.pi) : ℂ)) *
            ∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
              if k = 0 then (0 : ℂ) else fbTerm Δz x yJ k * (1 / (x : ℂ)) := by
      rw [show (1 / ((Real.sqrt (2 * Real.pi) : ℂ) * (x : ℂ))) *
          ∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), fbTerm Δz x yJ k =
          (1 / (Real.sqrt (2 * Real.pi) : ℂ)) *
            ((1 / (x : ℂ)) * ∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), fbTerm Δz x yJ k) by ring]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk0 : k = 0
      · subst hk0; simp [fbTerm]
      · simp [hk0, mul_comm]
    have hS0_rew :
        (Complex.I * (Δy : ℂ) / (Real.sqrt (2 * Real.pi) : ℂ)) *
            ∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
              (if k = 0 then (0 : ℂ) else
                (Δz : ℂ) * ((k : ℂ) * (Δz : ℂ)) *
                  (Real.exp (-((k : ℝ) * Δz) ^ 2 / 2) : ℂ) *
                  (1 - Complex.exp (-Complex.I * (x : ℂ) * (yJ : ℂ) * ((k : ℂ) * (Δz : ℂ)))) /
                    (1 - Complex.exp (-Complex.I * (x : ℂ) * (Δy : ℂ) * ((k : ℂ) * (Δz : ℂ))))) =
          (1 / (Real.sqrt (2 * Real.pi) : ℂ)) *
            ∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
              if k = 0 then (0 : ℂ) else
                fbTerm Δz x yJ k * (Complex.I * (Δy : ℂ) * ((k : ℂ) * (Δz : ℂ)) /
                  (1 - Complex.exp (-Complex.I * (x : ℂ) * (Δy : ℂ) * ((k : ℂ) * (Δz : ℂ))))) := by
      rw [show Complex.I * (Δy : ℂ) / (Real.sqrt (2 * Real.pi) : ℂ) =
          (1 / (Real.sqrt (2 * Real.pi) : ℂ)) * (Complex.I * (Δy : ℂ)) by ring]
      rw [mul_assoc]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk0 : k = 0
      · simp [hk0]
      · simp only [hk0, ↓reduceIte, fbTerm]; ring
    rw [hS0_rew, hS1_rew, ← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk0 : k = 0
    · simp [hk0, term]
    · simp [hk0, term, mul_sub]
  have hterm_norm :
      ∀ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
        ‖term k‖ ≤ 2 * Δy * (Δz * |(k : ℝ) * Δz| * Real.exp (-((k : ℝ) * Δz) ^ 2 / 2)) := by
    intro k hk
    by_cases hk0 : k = 0
    · subst hk0; simp [term]
    · simp only [term, hk0, ↓reduceIte]
      let θ : ℝ := x * Δy * ((k : ℝ) * Δz)
      have hθ_ne : θ ≠ 0 := by
        dsimp [θ]
        exact mul_ne_zero (mul_ne_zero hx_ne hΔy_pos.ne')
          (mul_ne_zero (Int.cast_ne_zero.mpr hk0) hΔz_pos.ne')
      have hθ_mem : θ ∈ Set.Icc (-1 : ℝ) 1 := abs_le.mp (hθ_bound k hk)
      have hbp13 : ‖1 / (1 - Complex.exp (-Complex.I * θ)) - 1 / (Complex.I * θ)‖ ≤ 1 :=
        (QuantumLinSys.Fourier.bound_p13 θ hθ_mem hθ_ne).le
      have hfac :
          Complex.I * (Δy : ℂ) * ((k : ℂ) * (Δz : ℂ)) /
              (1 - Complex.exp (-Complex.I * (x : ℂ) * (Δy : ℂ) * ((k : ℂ) * (Δz : ℂ)))) -
            1 / (x : ℂ) =
          (Complex.I * (Δy : ℂ) * ((k : ℂ) * (Δz : ℂ))) *
            (1 / (1 - Complex.exp (-Complex.I * (θ : ℂ))) - 1 / (Complex.I * (θ : ℂ))) := by
        have hx_c : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx_ne
        have hΔy_c : (Δy : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hΔy_pos.ne'
        have hΔz_c : (Δz : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hΔz_pos.ne'
        have hk_c : (k : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hk0
        have hden : 1 - Complex.exp (-Complex.I * (x : ℂ) * (Δy : ℂ) * ((k : ℂ) * (Δz : ℂ))) ≠ 0 :=
          sub_ne_zero.mpr (hθ_ne_one k hk hk0).symm
        have hθ_c : (θ : ℂ) = (x : ℂ) * (Δy : ℂ) * ((k : ℂ) * (Δz : ℂ)) := by
          dsimp [θ]; push_cast; ring
        rw [hθ_c]
        have hmul_assoc :
            -Complex.I * (x : ℂ) * (Δy : ℂ) * ((k : ℂ) * (Δz : ℂ)) =
              -Complex.I * ((x : ℂ) * (Δy : ℂ) * ((k : ℂ) * (Δz : ℂ))) := by ring
        rw [hmul_assoc]
        field_simp [hx_c, hΔy_c, hΔz_c, hk_c, hden, Complex.I_ne_zero]
      have hfb_le :
          ‖fbTerm Δz x yJ k‖ ≤ 2 * (Δz * Real.exp (-((k : ℝ) * Δz) ^ 2 / 2)) := by
        have h := fbTerm_norm_le (x := x) (yJ := yJ) hΔz_pos k
        have heq : Real.exp (-(Δz ^ 2 / 2) * (k : ℝ) ^ 2) = Real.exp (-((k : ℝ) * Δz) ^ 2 / 2) := by
          congr 1; ring
        rw [heq] at h
        linarith
      have hdiff_norm :
          ‖Complex.I * (Δy : ℂ) * ((k : ℂ) * (Δz : ℂ)) /
              (1 - Complex.exp (-Complex.I * (x : ℂ) * (Δy : ℂ) * ((k : ℂ) * (Δz : ℂ)))) -
            1 / (x : ℂ)‖ ≤ Δy * |(k : ℝ) * Δz| := by
        rw [hfac, norm_mul]
        have hleft :
            ‖Complex.I * (Δy : ℂ) * ((k : ℂ) * (Δz : ℂ))‖ = Δy * |(k : ℝ) * Δz| := by
          have hkcast : ((k : ℂ) * (Δz : ℂ)) = (((k : ℝ) * Δz : ℝ) : ℂ) := by push_cast; ring
          rw [hkcast, norm_mul, norm_mul, Complex.norm_I, one_mul,
            Complex.norm_of_nonneg hΔy_pos.le, Complex.norm_real, Real.norm_eq_abs]
        rw [hleft]
        calc
          Δy * |(k : ℝ) * Δz| *
              ‖1 / (1 - Complex.exp (-Complex.I * (θ : ℂ))) - 1 / (Complex.I * (θ : ℂ))‖
              ≤ Δy * |(k : ℝ) * Δz| * 1 := by gcongr
          _ = Δy * |(k : ℝ) * Δz| := mul_one _
      rw [norm_mul]
      calc
        ‖fbTerm Δz x yJ k‖ *
            ‖Complex.I * (Δy : ℂ) * ((k : ℂ) * (Δz : ℂ)) /
                (1 - Complex.exp (-Complex.I * (x : ℂ) * (Δy : ℂ) * ((k : ℂ) * (Δz : ℂ)))) -
              1 / (x : ℂ)‖
            ≤ 2 * (Δz * Real.exp (-((k : ℝ) * Δz) ^ 2 / 2)) * (Δy * |(k : ℝ) * Δz|) := by gcongr
        _ = 2 * Δy * (Δz * |(k : ℝ) * Δz| * Real.exp (-((k : ℝ) * Δz) ^ 2 / 2)) := by ring
  have hsum_bound :
      ∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
        Δz * |(k : ℝ) * Δz| * Real.exp (-((k : ℝ) * Δz) ^ 2 / 2) ≤ 2 * Real.sqrt Real.pi := by
    let g_even : ℤ → ℝ := fun k =>
      Δz * |(k : ℝ) * Δz| * Real.exp (-((k : ℝ) * Δz) ^ 2 / 2)
    have hg_even : ∀ k : ℤ, g_even (-k) = g_even k := by
      intro k; dsimp [g_even]
      have h1 : ((-k : ℤ) : ℝ) * Δz = -((k : ℝ) * Δz) := by push_cast; ring
      rw [h1, abs_neg, neg_sq]
    have hg0 : g_even 0 = 0 := by simp [g_even]
    change ∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), g_even k ≤ 2 * Real.sqrt Real.pi
    rw [sum_Icc_int_even_zero hg_even hg0]
    have hstep1 :
        ∑ n ∈ Finset.range K, g_even ((n + 1 : ℕ) : ℤ) ≤
          ∑ n ∈ Finset.range K, Δz * Real.exp (-(((n + 1 : ℕ) : ℝ) * Δz) ^ 2 / 4) := by
      apply Finset.sum_le_sum
      intro n _
      dsimp [g_even]
      have hcast : (((n + 1 : ℕ) : ℤ) : ℝ) = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
      have hcast' : ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
      have hle := abs_mul_exp_neg_sq_div_two_le (((n + 1 : ℕ) : ℝ) * Δz)
      have hrew_int : ((↑n + 1 : ℤ) : ℝ) = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
      rw [hrew_int]
      calc
        Δz * |((n + 1 : ℕ) : ℝ) * Δz| * Real.exp (-(((n + 1 : ℕ) : ℝ) * Δz) ^ 2 / 2)
            = Δz * (|((n + 1 : ℕ) : ℝ) * Δz| * Real.exp (-(((n + 1 : ℕ) : ℝ) * Δz) ^ 2 / 2)) := by
                ring
        _ ≤ Δz * Real.exp (-(((n + 1 : ℕ) : ℝ) * Δz) ^ 2 / 4) :=
            mul_le_mul_of_nonneg_left hle hΔz_pos.le
    have hstep2 :
        ∑ n ∈ Finset.range K, Δz * Real.exp (-(((n + 1 : ℕ) : ℝ) * Δz) ^ 2 / 4) ≤
          ∫ z in (0 : ℝ)..((K : ℝ) * Δz), Real.exp (-z ^ 2 / 4) := by
      have hanti := antitone_exp_neg_sq_div 4 (by norm_num)
      have hcont : Continuous (fun t : ℝ => Real.exp (-t ^ 2 / 4)) := by continuity
      have hrs := riemann_sum_antitone_le (a := 0) (δ := Δz) hΔz_pos.le K hanti hcont
      simpa [zero_add] using hrs
    have hstep3 :
        ∫ z in (0 : ℝ)..((K : ℝ) * Δz), Real.exp (-z ^ 2 / 4) ≤ Real.sqrt Real.pi :=
      gaussian_half_integral_quarter ((K : ℝ) * Δz) hzK_pos.le
    linarith
  have hsqrt_2pi_pos : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hS0_S1_norm :
      ‖QuantumLinSys.Fourier.hDisc J K Δy Δz x -
          (1 / ((Real.sqrt (2 * Real.pi) : ℂ) * (x : ℂ))) *
            ∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), fbTerm Δz x yJ k‖ ≤
        2 * Real.sqrt 2 * Δy := by
    rw [hdiff_eq, norm_mul, norm_div, norm_one, Complex.norm_of_nonneg hsqrt_2pi_pos.le]
    have hsum_norm :
        ‖∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), term k‖ ≤
          2 * Δy * (2 * Real.sqrt Real.pi) := by
      calc
        ‖∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), term k‖
            ≤ ∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), ‖term k‖ := norm_sum_le _ _
        _ ≤ ∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
              2 * Δy * (Δz * |(k : ℝ) * Δz| * Real.exp (-((k : ℝ) * Δz) ^ 2 / 2)) :=
            Finset.sum_le_sum hterm_norm
        _ = 2 * Δy * ∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
              Δz * |(k : ℝ) * Δz| * Real.exp (-((k : ℝ) * Δz) ^ 2 / 2) := by
            rw [← Finset.mul_sum]
        _ ≤ 2 * Δy * (2 * Real.sqrt Real.pi) :=
            mul_le_mul_of_nonneg_left hsum_bound (by positivity)
    have hcalc :
        1 / Real.sqrt (2 * Real.pi) * (2 * Δy * (2 * Real.sqrt Real.pi)) =
          2 * Real.sqrt 2 * Δy := by
      rw [Real.sqrt_mul (by norm_num)]
      have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
      have hs2_ne : Real.sqrt 2 ≠ 0 := by positivity
      have hspi_ne : Real.sqrt Real.pi ≠ 0 := by positivity
      field_simp [hs2_ne, hspi_ne]
      nlinarith [hsq2]
    calc
      1 / Real.sqrt (2 * Real.pi) * ‖∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), term k‖
          ≤ 1 / Real.sqrt (2 * Real.pi) * (2 * Δy * (2 * Real.sqrt Real.pi)) := by gcongr
      _ = 2 * Real.sqrt 2 * Δy := hcalc
  have hinv_sqrtL : (Real.sqrt L)⁻¹ < Real.sqrt 2 := by
    rw [inv_lt_iff_one_lt_mul₀ hsqrtL_pos]
    have h2L : 1 < 2 * L := by linarith
    have hsqrt_pos : 0 < Real.sqrt 2 * Real.sqrt L :=
      mul_pos (Real.sqrt_pos.mpr (by norm_num)) hsqrtL_pos
    have hsqrt_sq : (Real.sqrt 2 * Real.sqrt L) ^ 2 = 2 * L := by
      rw [mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt hL_pos.le]
    nlinarith [sq_abs (Real.sqrt 2 * Real.sqrt L - 1)]
  have hfinal : 2 * Real.sqrt 2 * Δy ≤ ε / 4 := by
    have h1 : 2 * Real.sqrt 2 * Δy ≤ 2 * Real.sqrt 2 * ((1 / 64 : ℝ) * (ε / Real.sqrt L)) := by
      gcongr
    have h2 :
        2 * Real.sqrt 2 * ((1 / 64 : ℝ) * (ε / Real.sqrt L)) ≤
          2 * Real.sqrt 2 * ((1 / 64 : ℝ) * (ε * Real.sqrt 2)) := by
      rw [div_eq_mul_inv ε (Real.sqrt L)]
      gcongr
    have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have h3 : 2 * Real.sqrt 2 * ((1 / 64 : ℝ) * (ε * Real.sqrt 2)) = ε / 16 := by
      calc
        2 * Real.sqrt 2 * ((1 / 64 : ℝ) * (ε * Real.sqrt 2))
            = (1 / 32 : ℝ) * (Real.sqrt 2 * Real.sqrt 2) * ε := by ring
        _ = (1 / 32 : ℝ) * 2 * ε := by rw [hsq2]
        _ = ε / 16 := by ring
    linarith
  exact le_trans hS0_S1_norm hfinal

private lemma fs1b_bound {K : ℕ} {Δz x yJ L κ ε : ℝ}
    (hκ : 1 ≤ κ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) (hL : 0 < L)
    (hL_eq : L = Real.log (κ / ε)) (hΔz_pos : 0 < Δz)
    (hKΔz : (K : ℝ) * Δz = 4 * Real.sqrt L)
    (hx_abs_pos : 0 < |x|) (hinv_x : 1 / |x| ≤ κ)
    (hfb_sum : Summable (fbTerm Δz x yJ))
    (hfb_norm_sum : Summable (fun k : ℤ => ‖fbTerm Δz x yJ k‖))
    (hmaj_sum : Summable (fun k : ℤ => 2 * Δz * Real.exp (-(Δz ^ 2 / 2) * (k : ℝ) ^ 2))) :
    ‖(1 / ((Real.sqrt (2 * Real.pi) : ℂ) * (x : ℂ))) *
          ∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), fbTerm Δz x yJ k -
        (1 / ((Real.sqrt (2 * Real.pi) : ℂ) * (x : ℂ))) *
          ∑' k : ℤ, fbTerm Δz x yJ k‖ ≤ ε / 4 := by
  let zK : ℝ := 4 * Real.sqrt L
  have hzK_pos : 0 < zK := by dsimp [zK]; positivity
  have hκε_pos : 0 < κ / ε := by positivity
  have hnorm_tail :
      ‖∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), fbTerm Δz x yJ k - ∑' k : ℤ, fbTerm Δz x yJ k‖ ≤
        4 * ∑' n : ℕ, Δz * Real.exp (-(((K + 1 + n : ℕ) : ℝ) * Δz) ^ 2 / 2) := by
    have hbound := tsum_compl_Icc_norm_bound (K := K) hfb_sum hfb_norm_sum hmaj_sum
      (fun k => by simp) (fbTerm_norm_le hΔz_pos)
    have h4 :
        2 * ∑' n : ℕ, 2 * Δz * Real.exp (-(Δz ^ 2 / 2) * ((K + 1 + n : ℕ) : ℝ) ^ 2) =
          4 * ∑' n : ℕ, Δz * Real.exp (-(((K + 1 + n : ℕ) : ℝ) * Δz) ^ 2 / 2) := by
      have hrew :
          (fun n : ℕ => 2 * Δz * Real.exp (-(Δz ^ 2 / 2) * ((K + 1 + n : ℕ) : ℝ) ^ 2)) =
            (fun n : ℕ => 2 * (Δz * Real.exp (-(((K + 1 + n : ℕ) : ℝ) * Δz) ^ 2 / 2))) := by
        ext n
        rw [mul_assoc]
        congr 1
        congr 1
        congr 1
        ring
      rw [hrew, tsum_mul_left]
      ring
    exact hbound.trans_eq h4
  have htail_int :
      ∑' n : ℕ, Δz * Real.exp (-(((K + 1 + n : ℕ) : ℝ) * Δz) ^ 2 / 2) ≤
        ∫ z in Set.Ioi zK, Real.exp (-z ^ 2 / 2) := by
    apply Real.tsum_le_of_sum_range_le
    · intro n; exact mul_nonneg hΔz_pos.le (Real.exp_pos _).le
    · intro N
      have hanti : AntitoneOn (fun t : ℝ => Real.exp (-t ^ 2 / 2)) (Set.Ici zK) :=
        (antitone_exp_neg_sq_div 2 (by norm_num)).mono (Set.Ici_subset_Ici.mpr hzK_pos.le)
      have hcont : Continuous (fun t : ℝ => Real.exp (-t ^ 2 / 2)) := by continuity
      have hrs := riemann_sum_antitone_le (a := zK) (δ := Δz) hΔz_pos.le N hanti hcont
      have hrew :
          (∑ n ∈ Finset.range N, Δz * Real.exp (-(((K + 1 + n : ℕ) : ℝ) * Δz) ^ 2 / 2)) =
            ∑ n ∈ Finset.range N, Δz * Real.exp (-(zK + ((n + 1 : ℕ) : ℝ) * Δz) ^ 2 / 2) := by
        apply Finset.sum_congr rfl
        intro n _
        have harg : zK + ((n + 1 : ℕ) : ℝ) * Δz = ((K + 1 + n : ℕ) : ℝ) * Δz := by
          dsimp [zK]; rw [← hKΔz]; push_cast; ring
        rw [harg]
      rw [hrew]
      have hg_int : Integrable (fun z : ℝ => Real.exp (-z ^ 2 / 2)) volume := by
        have heq : (fun z : ℝ => Real.exp (-z ^ 2 / 2)) =
            (fun z : ℝ => Real.exp (-(1 / 2 : ℝ) * z ^ 2)) := by
          ext z; congr 1; ring
        rw [heq]
        exact integrable_exp_neg_mul_sq (by norm_num)
      have hNΔ : 0 ≤ (N : ℝ) * Δz := mul_nonneg (Nat.cast_nonneg N) hΔz_pos.le
      have hle_ioi :
          ∫ z in zK..(zK + (N : ℝ) * Δz), Real.exp (-z ^ 2 / 2) ≤
            ∫ z in Set.Ioi zK, Real.exp (-z ^ 2 / 2) := by
        rw [intervalIntegral.integral_of_le (by linarith)]
        apply MeasureTheory.setIntegral_mono_set hg_int.integrableOn
        · filter_upwards with z; exact (Real.exp_pos _).le
        · exact Filter.Eventually.of_forall (fun z hz => hz.1)
      exact le_trans hrs hle_ioi
  have heq28 := QuantumLinSys.Fourier.eq_28 zK hzK_pos.le
  have hsqrt_2pi_pos : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hS1_S2_norm :
      ‖(1 / ((Real.sqrt (2 * Real.pi) : ℂ) * (x : ℂ))) *
            ∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), fbTerm Δz x yJ k -
          (1 / ((Real.sqrt (2 * Real.pi) : ℂ) * (x : ℂ))) *
            ∑' k : ℤ, fbTerm Δz x yJ k‖ ≤ (2 / |x|) * Real.exp (-zK ^ 2 / 2) := by
    have hrew :
        (1 / ((Real.sqrt (2 * Real.pi) : ℂ) * (x : ℂ))) *
              ∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), fbTerm Δz x yJ k -
            (1 / ((Real.sqrt (2 * Real.pi) : ℂ) * (x : ℂ))) *
              ∑' k : ℤ, fbTerm Δz x yJ k =
          (1 / ((Real.sqrt (2 * Real.pi) : ℂ) * (x : ℂ))) *
            (∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), fbTerm Δz x yJ k -
              ∑' k : ℤ, fbTerm Δz x yJ k) := by ring
    rw [hrew, norm_mul, norm_div, norm_one, norm_mul,
      Complex.norm_of_nonneg hsqrt_2pi_pos.le, Complex.norm_real, Real.norm_eq_abs]
    calc
      1 / (Real.sqrt (2 * Real.pi) * |x|) *
          ‖∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), fbTerm Δz x yJ k - ∑' k : ℤ, fbTerm Δz x yJ k‖
          ≤ 1 / (Real.sqrt (2 * Real.pi) * |x|) *
              (4 * ∑' n : ℕ, Δz * Real.exp (-(((K + 1 + n : ℕ) : ℝ) * Δz) ^ 2 / 2)) := by
              gcongr
      _ ≤ 1 / (Real.sqrt (2 * Real.pi) * |x|) *
            (4 * ∫ z in Set.Ioi zK, Real.exp (-z ^ 2 / 2)) := by gcongr
      _ = (4 / |x|) * (1 / Real.sqrt (2 * Real.pi) * ∫ z in Set.Ioi zK, Real.exp (-z ^ 2 / 2)) := by
              ring
      _ ≤ (4 / |x|) * (1 / 2 * Real.exp (-zK ^ 2 / 2)) := by gcongr
      _ = (2 / |x|) * Real.exp (-zK ^ 2 / 2) := by ring
  have hzK_exp : Real.exp (-zK ^ 2 / 2) = (ε / κ) ^ 8 := by
    have hzK_sq : zK ^ 2 / 2 = 8 * L := by
      dsimp [zK]; rw [mul_pow, Real.sq_sqrt hL.le]; norm_num; ring
    rw [show -zK ^ 2 / 2 = -8 * L by linarith, hL_eq,
      exp_neg_eight_mul_log hκε_pos, inv_div]
  have hfinal : (2 / |x|) * Real.exp (-zK ^ 2 / 2) ≤ ε / 4 := by
    rw [hzK_exp]
    have hεκ_half : ε / κ ≤ 1 / 2 := by rw [div_le_iff₀ (by linarith)]; nlinarith
    have hεκ_pow : (ε / κ) ^ 7 ≤ (1 / 2 : ℝ) ^ 7 := pow_le_pow_left₀ (by positivity) hεκ_half 7
    calc
      (2 / |x|) * (ε / κ) ^ 8 = 2 * (1 / |x|) * (ε / κ) ^ 8 := by ring
      _ ≤ (2 * κ) * (ε / κ) ^ 8 := by gcongr
      _ = 2 * ε * (ε / κ) ^ 7 := by field_simp [(show κ ≠ 0 by linarith)]
      _ ≤ 2 * ε * (1 / 2 : ℝ) ^ 7 := by gcongr
      _ = ε / 64 := by norm_num; ring
      _ ≤ ε / 4 := by linarith
  exact le_trans hS1_S2_norm hfinal

private lemma fs1c_bound {Δz x yJ L κ ε a : ℝ}
    (hκ : 1 ≤ κ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) (hL : 0 < L)
    (hL_eq : L = Real.log (κ / ε)) (hyJ_eq : yJ = 4 * κ * Real.sqrt L)
    (hΔz_pos : 0 < Δz) (hx_lb : 1 / κ ≤ |x|) (hx_ub : |x| ≤ 1)
    (hinv_x : 1 / |x| ≤ κ)
    (ha_eq : a = (Real.pi / Δz) ^ 2 / 2) (ha_ge_1 : 1 ≤ a)
    (hπ_le : 96 * κ * Real.sqrt L ≤ Real.pi / Δz)
    (hexp_a_le : Real.exp (-a) ≤ (ε / κ) ^ 16)
    (hfb_sum : Summable (fbTerm Δz x yJ)) :
    ‖(1 / ((Real.sqrt (2 * Real.pi) : ℂ) * (x : ℂ))) * ∑' k : ℤ, fbTerm Δz x yJ k -
        (1 / ((Real.sqrt (2 * Real.pi) : ℂ) * (x : ℂ))) *
          ∑' k : ℤ, (Δz : ℂ) * (Real.exp (-((k : ℝ) * Δz) ^ 2 / 2) : ℂ)‖ ≤ ε / 4 := by
  have hyJ_pos : 0 < yJ := by rw [hyJ_eq]; positivity
  have hκε_pos : 0 < κ / ε := by positivity
  have hgb_sum : Summable (fun k : ℤ => (Δz : ℂ) * (Real.exp (-((k : ℝ) * Δz) ^ 2 / 2) : ℂ)) := by
    have hmaj : Summable (fun k : ℤ => Δz * Real.exp (-(Δz ^ 2 / 2) * (k : ℝ) ^ 2)) :=
      (exp_neg_int_sq_summable (Δz ^ 2 / 2) (by positivity)).mul_left Δz
    refine Summable.of_norm_bounded hmaj ?_
    intro k
    rw [norm_mul, Complex.norm_of_nonneg hΔz_pos.le, Complex.norm_of_nonneg (Real.exp_pos _).le]
    exact le_of_eq (by congr 1; ring_nf)
  have hdiff_tsum :
      (1 / ((Real.sqrt (2 * Real.pi) : ℂ) * (x : ℂ))) * ∑' k : ℤ, fbTerm Δz x yJ k -
          (1 / ((Real.sqrt (2 * Real.pi) : ℂ) * (x : ℂ))) *
            ∑' k : ℤ, (Δz : ℂ) * (Real.exp (-((k : ℝ) * Δz) ^ 2 / 2) : ℂ) =
        -(1 / (x : ℂ)) *
          (1 / (Real.sqrt (2 * Real.pi) : ℂ) *
            ∑' k : ℤ, (Δz : ℂ) * (Real.exp (-((k : ℝ) * Δz) ^ 2 / 2) : ℂ) *
              Complex.exp (-Complex.I * ((x * yJ : ℝ) : ℂ) * (((k : ℝ) : ℂ) * (Δz : ℂ)))) := by
    have hsub_tsum := hfb_sum.tsum_sub hgb_sum
    have hfun :
        (fun k : ℤ => fbTerm Δz x yJ k - (Δz : ℂ) * (Real.exp (-((k : ℝ) * Δz) ^ 2 / 2) : ℂ)) =
          (fun k : ℤ => -((Δz : ℂ) * (Real.exp (-((k : ℝ) * Δz) ^ 2 / 2) : ℂ) *
            Complex.exp (-Complex.I * (x : ℂ) * (yJ : ℂ) * ((k : ℂ) * (Δz : ℂ))))) := by
      ext k; dsimp [fbTerm]; ring
    have hexp_fun :
        (fun k : ℤ => -((Δz : ℂ) * (Real.exp (-((k : ℝ) * Δz) ^ 2 / 2) : ℂ) *
            Complex.exp (-Complex.I * (x : ℂ) * (yJ : ℂ) * ((k : ℂ) * (Δz : ℂ))))) =
          (fun k : ℤ => -((Δz : ℂ) * (Real.exp (-((k : ℝ) * Δz) ^ 2 / 2) : ℂ) *
            Complex.exp (-Complex.I * ((x * yJ : ℝ) : ℂ) * (((k : ℝ) : ℂ) * (Δz : ℂ))))) := by
      ext k; congr 1; congr 1; congr 1; push_cast; ring
    rw [← mul_sub, ← hsub_tsum, hfun, hexp_fun, tsum_neg]
    ring
  have h13 := QuantumLinSys.Fourier.lemma_13 (x * yJ) Δz hΔz_pos
  have h13' :
      1 / (Real.sqrt (2 * Real.pi) : ℂ) *
          ∑' k : ℤ, (Δz : ℂ) * (Real.exp (-((k : ℝ) * Δz) ^ 2 / 2) : ℂ) *
            Complex.exp (-Complex.I * ((x * yJ : ℝ) : ℂ) * (((k : ℝ) : ℂ) * (Δz : ℂ))) =
        ∑' k : ℤ, (Real.exp (-(x * yJ + 2 * Real.pi * (k : ℝ) / Δz) ^ 2 / 2) : ℂ) := h13.symm
  rw [hdiff_tsum, h13', ← Complex.ofReal_tsum]
  rw [norm_mul, norm_neg, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs]
  let g_c : ℤ → ℝ := fun k => Real.exp (-(x * yJ + 2 * Real.pi * (k : ℝ) / Δz) ^ 2 / 2)
  have hxyJ_le_pi : |x * yJ| ≤ Real.pi / Δz := by
    rw [abs_mul, abs_of_pos hyJ_pos, hyJ_eq]
    have h1 : |x| * (4 * κ * Real.sqrt L) ≤ 1 * (4 * κ * Real.sqrt L) := by gcongr
    have h2 : 4 * κ * Real.sqrt L ≤ 96 * κ * Real.sqrt L := by nlinarith
    linarith
  have hgc_le : ∀ k : ℤ, k ≠ 0 → g_c k ≤ Real.exp (-a * (k : ℝ) ^ 2) := by
    intro k hk0
    dsimp [g_c]
    rw [Real.exp_le_exp]
    have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk0
    have h_abs : |(k : ℝ)| * (Real.pi / Δz) ≤ |x * yJ + 2 * Real.pi * (k : ℝ) / Δz| := by
      have htri := abs_sub_abs_le_abs_sub (2 * Real.pi * (k : ℝ) / Δz) (-(x * yJ))
      have heq1 : (2 * Real.pi * (k : ℝ) / Δz) - (-(x * yJ)) =
          x * yJ + 2 * Real.pi * (k : ℝ) / Δz := by ring
      have heq2 : |2 * Real.pi * (k : ℝ) / Δz| = 2 * |(k : ℝ)| * (Real.pi / Δz) := by
        rw [show 2 * Real.pi * (k : ℝ) / Δz = 2 * (k : ℝ) * (Real.pi / Δz) by ring,
          abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
          abs_of_pos (div_pos Real.pi_pos hΔz_pos)]
      rw [heq1, heq2, abs_neg] at htri
      have hxyJ_le_k : |x * yJ| ≤ |(k : ℝ)| * (Real.pi / Δz) := by
        calc
          |x * yJ| ≤ Real.pi / Δz := hxyJ_le_pi
          _ = 1 * (Real.pi / Δz) := (one_mul _).symm
          _ ≤ |(k : ℝ)| * (Real.pi / Δz) := by gcongr
      linarith
    have hsq : (|(k : ℝ)| * (Real.pi / Δz)) ^ 2 ≤ (x * yJ + 2 * Real.pi * (k : ℝ) / Δz) ^ 2 := by
      have h0 : 0 ≤ |(k : ℝ)| * (Real.pi / Δz) := by positivity
      calc
        (|(k : ℝ)| * (Real.pi / Δz)) ^ 2
            ≤ |x * yJ + 2 * Real.pi * (k : ℝ) / Δz| ^ 2 := by nlinarith
        _ = (x * yJ + 2 * Real.pi * (k : ℝ) / Δz) ^ 2 := sq_abs _
    have hsq_eq : (|(k : ℝ)| * (Real.pi / Δz)) ^ 2 / 2 = a * (k : ℝ) ^ 2 := by
      rw [ha_eq, mul_pow, sq_abs]; ring
    linarith
  have hgc_maj : Summable (fun k : ℤ => Real.exp (-a * (k : ℝ) ^ 2)) :=
    exp_neg_int_sq_summable a (by linarith)
  have hsplit_c := tsum_int_split_zero_bound (g := g_c) (h := fun k : ℤ => Real.exp (-a * (k : ℝ) ^ 2))
    (fun _ => (Real.exp_pos _).le) hgc_maj (fun k => by simp) hgc_le
  have hcast_c :
      (fun n : ℕ => Real.exp (-a * (((n + 1 : ℕ) : ℤ) : ℝ) ^ 2)) =
        (fun n : ℕ => Real.exp (-a * ((n + 1 : ℕ) : ℝ) ^ 2)) := by
    ext n; push_cast; rfl
  rw [hcast_c] at hsplit_c
  have hgc_nonneg : 0 ≤ ∑' k : ℤ, g_c k := tsum_nonneg (fun _ => (Real.exp_pos _).le)
  rw [Complex.norm_of_nonneg hgc_nonneg]
  have hgc0 : g_c 0 ≤ (ε / κ) ^ 8 := by
    dsimp [g_c]
    simp only [Int.cast_zero, mul_zero, zero_div, add_zero]
    have hxyJ_lb : 4 * Real.sqrt L ≤ |x * yJ| := by
      rw [abs_mul, abs_of_pos hyJ_pos, hyJ_eq]
      calc
        4 * Real.sqrt L = (1 / κ) * (4 * κ * Real.sqrt L) := by
          field_simp [(show κ ≠ 0 by linarith)]
        _ ≤ |x| * (4 * κ * Real.sqrt L) := mul_le_mul_of_nonneg_right hx_lb (by positivity)
    have hsq : 8 * L ≤ (x * yJ) ^ 2 / 2 := by
      have h1 : (4 * Real.sqrt L) ^ 2 ≤ |x * yJ| ^ 2 := by
        have h0 : 0 ≤ 4 * Real.sqrt L := by positivity
        nlinarith
      rw [sq_abs, mul_pow, Real.sq_sqrt hL.le] at h1
      linarith
    calc
      Real.exp (-(x * yJ) ^ 2 / 2) ≤ Real.exp (-8 * L) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = (ε / κ) ^ 8 := by rw [hL_eq, exp_neg_eight_mul_log hκε_pos, inv_div]
  have hgeom_tail := tsum_geom_tail_bound ha_ge_1
    (f := fun n : ℕ => Real.exp (-a * ((n + 1 : ℕ) : ℝ) ^ 2))
    (fun _ => (Real.exp_pos _).le)
    (fun n => by
      rw [Real.exp_le_exp]
      have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
      have hsq : ((n + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
      nlinarith)
  have hgc_tail_le : 2 * ∑' n : ℕ, Real.exp (-a * ((n + 1 : ℕ) : ℝ) ^ 2) ≤ 4 * (ε / κ) ^ 16 := by
    have h1 := hgeom_tail.2
    linarith [hexp_a_le]
  calc
    1 / |x| * ∑' k : ℤ, g_c k
        ≤ 1 / |x| * (g_c 0 + 2 * ∑' n : ℕ, Real.exp (-a * ((n + 1 : ℕ) : ℝ) ^ 2)) := by
            gcongr
            exact hsplit_c.2
    _ ≤ κ * ((ε / κ) ^ 8 + 4 * (ε / κ) ^ 16) := by gcongr
    _ ≤ κ * ((ε / κ) ^ 8 + 4 * (ε / κ) ^ 8) := by
            have hεκ_le1 : ε / κ ≤ 1 := by rw [div_le_one (by linarith)]; linarith
            have hpow_le : (ε / κ) ^ 16 ≤ (ε / κ) ^ 8 :=
              pow_le_pow_of_le_one (by positivity) hεκ_le1 (by norm_num)
            gcongr
    _ = 5 * κ * (ε / κ) ^ 8 := by ring
    _ = 5 * ε * (ε / κ) ^ 7 := by field_simp [(show κ ≠ 0 by linarith)]
    _ ≤ 5 * ε * (1 / 2 : ℝ) ^ 7 := by
            have hεκ_half : ε / κ ≤ 1 / 2 := by rw [div_le_iff₀ (by linarith)]; nlinarith
            have hpow7 : (ε / κ) ^ 7 ≤ (1 / 2 : ℝ) ^ 7 :=
              pow_le_pow_left₀ (by positivity) hεκ_half 7
            gcongr
    _ = 5 / 128 * ε := by norm_num; ring
    _ ≤ ε / 4 := by linarith

private lemma fs1d_bound {Δz x κ ε a : ℝ}
    (hκ : 1 ≤ κ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) (hΔz_pos : 0 < Δz)
    (hinv_x : 1 / |x| ≤ κ)
    (ha_eq : a = (Real.pi / Δz) ^ 2 / 2) (ha_ge_1 : 1 ≤ a)
    (hexp_a_le : Real.exp (-a) ≤ (ε / κ) ^ 16) :
    ‖(1 / ((Real.sqrt (2 * Real.pi) : ℂ) * (x : ℂ))) *
          ∑' k : ℤ, (Δz : ℂ) * (Real.exp (-((k : ℝ) * Δz) ^ 2 / 2) : ℂ) -
        ((1 / x : ℝ) : ℂ)‖ ≤ ε / 4 := by
  have h13 := QuantumLinSys.Fourier.lemma_13 0 Δz hΔz_pos
  have hS3_eq :
      (1 / ((Real.sqrt (2 * Real.pi) : ℂ) * (x : ℂ))) *
          ∑' k : ℤ, (Δz : ℂ) * (Real.exp (-((k : ℝ) * Δz) ^ 2 / 2) : ℂ) =
        (1 / (x : ℂ)) *
          ∑' k : ℤ, (Real.exp (-(0 + 2 * Real.pi * (k : ℝ) / Δz) ^ 2 / 2) : ℂ) := by
    have harg1 :
        (fun k : ℤ => (Δz : ℂ) * (Real.exp (-((k : ℝ) * Δz) ^ 2 / 2) : ℂ)) =
          (fun k : ℤ => (Δz : ℂ) * (Real.exp (-((k : ℝ) * Δz) ^ 2 / 2) : ℂ) *
            Complex.exp (-Complex.I * (0 : ℝ) * (((k : ℝ) : ℂ) * (Δz : ℂ)))) := by
      ext k; simp
    rw [show (1 / ((Real.sqrt (2 * Real.pi) : ℂ) * (x : ℂ))) *
        ∑' k : ℤ, (Δz : ℂ) * (Real.exp (-((k : ℝ) * Δz) ^ 2 / 2) : ℂ) =
        (1 / (x : ℂ)) * (1 / (Real.sqrt (2 * Real.pi) : ℂ) *
          ∑' k : ℤ, (Δz : ℂ) * (Real.exp (-((k : ℝ) * Δz) ^ 2 / 2) : ℂ)) by ring]
    rw [harg1, ← h13]
  let g_d : ℤ → ℝ := fun k => Real.exp (-(0 + 2 * Real.pi * (k : ℝ) / Δz) ^ 2 / 2)
  have hgd_maj : Summable (fun k : ℤ => Real.exp (-a * (k : ℝ) ^ 2)) :=
    exp_neg_int_sq_summable a (by linarith)
  have hgd_le : ∀ k : ℤ, g_d k ≤ Real.exp (-a * (k : ℝ) ^ 2) := by
    intro k
    dsimp [g_d]
    rw [Real.exp_le_exp]
    have heq : -(0 + 2 * Real.pi * (k : ℝ) / Δz) ^ 2 / 2 =
        -(4 * ((Real.pi / Δz) ^ 2 / 2) * (k : ℝ) ^ 2) := by ring
    rw [heq, ← ha_eq]
    have hk2 : 0 ≤ (k : ℝ) ^ 2 := sq_nonneg _
    nlinarith
  have hsplit_d := tsum_int_split_zero_bound (g := g_d) (h := fun k : ℤ => Real.exp (-a * (k : ℝ) ^ 2))
    (fun _ => (Real.exp_pos _).le) hgd_maj (fun k => by simp)
    (fun k _ => hgd_le k)
  have hcast_d :
      (fun n : ℕ => Real.exp (-a * (((n + 1 : ℕ) : ℤ) : ℝ) ^ 2)) =
        (fun n : ℕ => Real.exp (-a * ((n + 1 : ℕ) : ℝ) ^ 2)) := by
    ext n; push_cast; rfl
  rw [hcast_d] at hsplit_d
  have hgd0 : g_d 0 = 1 := by simp [g_d]
  have hgd_nonneg : 0 ≤ (∑' k : ℤ, g_d k) - 1 := by
    have h0le : g_d 0 ≤ ∑' k : ℤ, g_d k := by
      have hterm := hsplit_d.1.le_tsum (0 : ℤ) (fun k _ => (Real.exp_pos _).le)
      exact hterm
    linarith [hgd0]
  have hS3_S4_eq :
      (1 / ((Real.sqrt (2 * Real.pi) : ℂ) * (x : ℂ))) *
            ∑' k : ℤ, (Δz : ℂ) * (Real.exp (-((k : ℝ) * Δz) ^ 2 / 2) : ℂ) -
          ((1 / x : ℝ) : ℂ) =
        (1 / (x : ℂ)) * (((∑' k : ℤ, g_d k) - 1 : ℝ) : ℂ) := by
    rw [hS3_eq, ← Complex.ofReal_tsum g_d]
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  have hgeom_tail := tsum_geom_tail_bound ha_ge_1
    (f := fun n : ℕ => Real.exp (-a * ((n + 1 : ℕ) : ℝ) ^ 2))
    (fun _ => (Real.exp_pos _).le)
    (fun n => by
      rw [Real.exp_le_exp]
      have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
      have hsq : ((n + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
      nlinarith)
  have hdiff_le : (∑' k : ℤ, g_d k) - 1 ≤ 4 * (ε / κ) ^ 16 := by
    have h1 := hsplit_d.2
    have h2 := hgeom_tail.2
    linarith [hgd0, hexp_a_le]
  rw [hS3_S4_eq, norm_mul, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_of_nonneg hgd_nonneg]
  calc
    1 / |x| * ((∑' k : ℤ, g_d k) - 1) ≤ κ * (4 * (ε / κ) ^ 16) := by gcongr
    _ = 4 * ε * (ε / κ) ^ 15 := by field_simp [(show κ ≠ 0 by linarith)]
    _ ≤ 4 * ε * (1 / 2 : ℝ) ^ 15 := by
            have hεκ_half : ε / κ ≤ 1 / 2 := by rw [div_le_iff₀ (by linarith)]; nlinarith
            have hpow15 : (ε / κ) ^ 15 ≤ (1 / 2 : ℝ) ^ 15 :=
              pow_le_pow_left₀ (by positivity) hεκ_half 15
            gcongr
    _ = ε / 8192 := by norm_num; ring
    _ ≤ ε / 4 := by linarith

end Helpers

theorem solution :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ κ ε : ℝ,
      1 ≤ κ → 0 < ε → ε < 1 / 2 →
        ∃ (J K : ℕ) (Δy Δz : ℝ),
          c * (κ / ε * Real.log (κ / ε)) ≤ (J : ℝ) ∧
          (J : ℝ) ≤ C * (κ / ε * Real.log (κ / ε)) ∧
          c * (κ * Real.log (κ / ε)) ≤ (K : ℝ) ∧
          (K : ℝ) ≤ C * (κ * Real.log (κ / ε)) ∧
          c * (ε / Real.sqrt (Real.log (κ / ε))) ≤ Δy ∧
          Δy ≤ C * (ε / Real.sqrt (Real.log (κ / ε))) ∧
          c * (κ * Real.sqrt (Real.log (κ / ε)))⁻¹ ≤ Δz ∧
          Δz ≤ C * (κ * Real.sqrt (Real.log (κ / ε)))⁻¹ ∧
          ∀ x ∈ QuantumLinSys.Chebyshev.Dκ κ,
            ‖QuantumLinSys.Fourier.hDisc J K Δy Δz x - ((1 / x : ℝ) : ℂ)‖ ≤ ε := by
  refine ⟨4 / 257, 257, by norm_num, by norm_num, ?_⟩
  intro κ ε hκ hε0 hε1
  let L : ℝ := Real.log (κ / ε)
  have hκε_gt_two : 2 < κ / ε := by
    rw [lt_div_iff₀ hε0]
    linarith
  have hκε_pos : 0 < κ / ε := by linarith
  have hL_gt_half : 1 / 2 < L := by
    have hlog2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hκε_gt_two.le
    linarith [log_two_gt_half]
  have hL_pos : 0 < L := by linarith
  have hsqrtL_pos : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL_pos
  have hκL_gt_half : 1 / 2 < κ * L := by nlinarith
  have hκεL_gt_one : 1 < κ / ε * L := by nlinarith
  let yJ : ℝ := 4 * κ * Real.sqrt L
  let zK : ℝ := 4 * Real.sqrt L
  let J : ℕ := ⌈256 * (κ / ε * L)⌉₊
  let K : ℕ := ⌈128 * (κ * L)⌉₊
  let Δy : ℝ := yJ / (J : ℝ)
  let Δz : ℝ := zK / (K : ℝ)
  have hyJ_pos : 0 < yJ := by positivity
  have hzK_pos : 0 < zK := by positivity
  have hJ_lb : 256 * (κ / ε * L) ≤ (J : ℝ) := Nat.le_ceil _
  have hJ_ub : (J : ℝ) ≤ 257 * (κ / ε * L) := by
    have hlt := Nat.ceil_lt_add_one (show 0 ≤ 256 * (κ / ε * L) by positivity)
    have : (J : ℝ) ≤ 256 * (κ / ε * L) + 1 := hlt.le
    linarith
  have hJ_pos : (0 : ℝ) < (J : ℝ) := by linarith
  have hK_lb : 128 * (κ * L) ≤ (K : ℝ) := Nat.le_ceil _
  have hK_ub : (K : ℝ) ≤ 130 * (κ * L) := by
    have hlt := Nat.ceil_lt_add_one (show 0 ≤ 128 * (κ * L) by positivity)
    have : (K : ℝ) ≤ 128 * (κ * L) + 1 := hlt.le
    linarith
  have hK_pos : (0 : ℝ) < (K : ℝ) := by linarith
  have hΔy_pos : 0 < Δy := div_pos hyJ_pos hJ_pos
  have hΔz_pos : 0 < Δz := div_pos hzK_pos hK_pos
  have hL_sq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL_pos.le
  have hΔy_lb : (4 / 257 : ℝ) * (ε / Real.sqrt L) ≤ Δy := by
    dsimp [Δy, yJ]
    rw [div_eq_mul_inv]
    have hden_pos : 0 < 257 * (κ / ε * L) := by positivity
    have hinv : (257 * (κ / ε * L))⁻¹ ≤ (J : ℝ)⁻¹ :=
      (inv_le_inv₀ hden_pos hJ_pos).mpr hJ_ub
    calc
      (4 / 257 : ℝ) * (ε / Real.sqrt L)
          = (4 * κ * Real.sqrt L) * (257 * (κ / ε * L))⁻¹ := by
              field_simp [hε0.ne', hsqrtL_pos.ne', (show κ ≠ 0 by linarith)]
              nlinarith [hL_sq]
      _ ≤ (4 * κ * Real.sqrt L) * (J : ℝ)⁻¹ :=
              mul_le_mul_of_nonneg_left hinv hyJ_pos.le
  have hΔy_ub : Δy ≤ (1 / 64 : ℝ) * (ε / Real.sqrt L) := by
    dsimp [Δy, yJ]
    rw [div_eq_mul_inv]
    have hden_pos : 0 < 256 * (κ / ε * L) := by positivity
    have hinv : (J : ℝ)⁻¹ ≤ (256 * (κ / ε * L))⁻¹ :=
      (inv_le_inv₀ hJ_pos hden_pos).mpr hJ_lb
    calc
      (4 * κ * Real.sqrt L) * (J : ℝ)⁻¹
          ≤ (4 * κ * Real.sqrt L) * (256 * (κ / ε * L))⁻¹ :=
              mul_le_mul_of_nonneg_left hinv hyJ_pos.le
      _ = (1 / 64 : ℝ) * (ε / Real.sqrt L) := by
              field_simp [hε0.ne', hsqrtL_pos.ne', (show κ ≠ 0 by linarith)]
              nlinarith [hL_sq]
  have hΔz_lb : (4 / 130 : ℝ) * (κ * Real.sqrt L)⁻¹ ≤ Δz := by
    dsimp [Δz, zK]
    rw [div_eq_mul_inv]
    have hden_pos : 0 < 130 * (κ * L) := by positivity
    have hinv : (130 * (κ * L))⁻¹ ≤ (K : ℝ)⁻¹ :=
      (inv_le_inv₀ hden_pos hK_pos).mpr hK_ub
    calc
      (4 / 130 : ℝ) * (κ * Real.sqrt L)⁻¹
          = (4 * Real.sqrt L) * (130 * (κ * L))⁻¹ := by
              field_simp [hsqrtL_pos.ne', (show κ ≠ 0 by linarith)]
              nlinarith [hL_sq]
      _ ≤ (4 * Real.sqrt L) * (K : ℝ)⁻¹ :=
              mul_le_mul_of_nonneg_left hinv hzK_pos.le
  have hΔz_ub : Δz ≤ (1 / 32 : ℝ) * (κ * Real.sqrt L)⁻¹ := by
    dsimp [Δz, zK]
    rw [div_eq_mul_inv]
    have hden_pos : 0 < 128 * (κ * L) := by positivity
    have hinv : (K : ℝ)⁻¹ ≤ (128 * (κ * L))⁻¹ :=
      (inv_le_inv₀ hK_pos hden_pos).mpr hK_lb
    calc
      (4 * Real.sqrt L) * (K : ℝ)⁻¹
          ≤ (4 * Real.sqrt L) * (128 * (κ * L))⁻¹ :=
              mul_le_mul_of_nonneg_left hinv hzK_pos.le
      _ = (1 / 32 : ℝ) * (κ * Real.sqrt L)⁻¹ := by
              field_simp [hsqrtL_pos.ne', (show κ ≠ 0 by linarith)]
              nlinarith [hL_sq]
  refine ⟨J, K, Δy, Δz, ?_, ?_, ?_, ?_, hΔy_lb, ?_, ?_, ?_, ?_⟩
  · exact le_trans (mul_le_mul_of_nonneg_right (by norm_num) (by positivity)) hJ_lb
  · exact le_trans hJ_ub (mul_le_mul_of_nonneg_right (by norm_num) (by positivity))
  · exact le_trans (mul_le_mul_of_nonneg_right (by norm_num) (by positivity)) hK_lb
  · exact le_trans hK_ub (mul_le_mul_of_nonneg_right (by norm_num) (by positivity))
  · exact le_trans hΔy_ub (mul_le_mul_of_nonneg_right (by norm_num) (by positivity))
  · exact le_trans (mul_le_mul_of_nonneg_right (by norm_num) (by positivity)) hΔz_lb
  · exact le_trans hΔz_ub (mul_le_mul_of_nonneg_right (by norm_num) (by positivity))
  · intro x hx
    have hx_bounds : 1 / κ ≤ |x| ∧ |x| ≤ 1 := by
      rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hneg : x ≤ 0 := le_trans h2 (div_nonpos_of_nonpos_of_nonneg (by norm_num) (by linarith))
        rw [abs_of_nonpos hneg]
        have hneg_div : -(1 / κ) = -1 / κ := by ring
        constructor <;> linarith
      · have hpos : 0 ≤ x := le_trans (by positivity) h1
        rw [abs_of_nonneg hpos]
        exact ⟨h1, h2⟩
    have hx_abs_pos : 0 < |x| := lt_of_lt_of_le (by positivity) hx_bounds.1
    have hx_ne : x ≠ 0 := abs_pos.mp hx_abs_pos
    have hinv_x : 1 / |x| ≤ κ := by
      rw [div_le_iff₀ hx_abs_pos]
      calc
        1 = κ * (1 / κ) := by field_simp [(show κ ≠ 0 by linarith)]
        _ ≤ κ * |x| := mul_le_mul_of_nonneg_left hx_bounds.1 (by positivity)
    have hJΔy : (J : ℝ) * Δy = yJ := by
      dsimp [Δy]; field_simp [hJ_pos.ne']
    have hKΔz : (K : ℝ) * Δz = zK := by
      dsimp [Δz]; field_simp [hK_pos.ne']
    have hθ_bound :
        ∀ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
          |x * Δy * ((k : ℝ) * Δz)| ≤ 1 := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      have hk_abs : |(k : ℝ)| ≤ (K : ℝ) := by
        rw [abs_le]
        exact ⟨by exact_mod_cast hk.1, by exact_mod_cast hk.2⟩
      have hzk_abs : |(k : ℝ) * Δz| ≤ zK := by
        rw [abs_mul, abs_of_pos hΔz_pos]
        calc
          |(k : ℝ)| * Δz ≤ (K : ℝ) * Δz := mul_le_mul_of_nonneg_right hk_abs hΔz_pos.le
          _ = zK := hKΔz
      have hprod : |x * Δy * ((k : ℝ) * Δz)| ≤ (1 / 16 : ℝ) * ε := by
        rw [abs_mul, abs_mul, abs_of_pos hΔy_pos]
        calc
          |x| * Δy * |(k : ℝ) * Δz|
              ≤ 1 * ((1 / 64 : ℝ) * (ε / Real.sqrt L)) * zK := by
                  gcongr
                  exact hx_bounds.2
          _ = (1 / 16 : ℝ) * ε := by
                  dsimp [zK]
                  field_simp [hsqrtL_pos.ne']
                  norm_num
      linarith
    have hmaj_sum :
        Summable (fun k : ℤ => 2 * Δz * Real.exp (-(Δz ^ 2 / 2) * (k : ℝ) ^ 2)) :=
      (exp_neg_int_sq_summable (Δz ^ 2 / 2) (by positivity)).mul_left (2 * Δz)
    have hfb_sum : Summable (fbTerm Δz x yJ) :=
      Summable.of_norm_bounded hmaj_sum (fbTerm_norm_le hΔz_pos)
    have hfb_norm_sum : Summable (fun k : ℤ => ‖fbTerm Δz x yJ k‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fbTerm_norm_le hΔz_pos) hmaj_sum
    let a : ℝ := (Real.pi / Δz) ^ 2 / 2
    have hπ_div_Δz_lb : 96 * κ * Real.sqrt L ≤ Real.pi / Δz := by
      have h1 : 32 * κ * Real.sqrt L ≤ Δz⁻¹ := by
        have hpos1 : 0 < 32 * κ * Real.sqrt L := by positivity
        rw [le_inv_comm₀ hpos1 hΔz_pos]
        calc
          Δz ≤ (1 / 32 : ℝ) * (κ * Real.sqrt L)⁻¹ := hΔz_ub
          _ = (32 * κ * Real.sqrt L)⁻¹ := by ring
      have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
      rw [div_eq_mul_inv]
      calc
        96 * κ * Real.sqrt L = 3 * (32 * κ * Real.sqrt L) := by ring
        _ ≤ Real.pi * Δz⁻¹ := by gcongr
    have ha_ge_16L : 16 * L ≤ a := by
      dsimp [a]
      have h0 : 0 ≤ 96 * κ * Real.sqrt L := by positivity
      have hsq : (96 * κ * Real.sqrt L) ^ 2 ≤ (Real.pi / Δz) ^ 2 :=
        pow_le_pow_left₀ h0 hπ_div_Δz_lb 2
      have hsq_eq : (96 * κ * Real.sqrt L) ^ 2 = 9216 * κ ^ 2 * L := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hL_pos.le]; norm_num
      have hκ2 : 1 ≤ κ ^ 2 := one_le_pow₀ hκ
      calc
        16 * L ≤ 4608 * 1 * L := by linarith
        _ ≤ 4608 * κ ^ 2 * L := by gcongr
        _ = (96 * κ * Real.sqrt L) ^ 2 / 2 := by rw [hsq_eq]; ring
        _ ≤ (Real.pi / Δz) ^ 2 / 2 := div_le_div_of_nonneg_right hsq (by norm_num)
    have ha_ge_1 : 1 ≤ a := by linarith
    have hexp_a_le : Real.exp (-a) ≤ (ε / κ) ^ 16 := by
      calc
        Real.exp (-a) ≤ Real.exp (-16 * L) :=
          Real.exp_le_exp.mpr (by linarith)
        _ = (ε / κ) ^ 16 := by rw [exp_neg_sixteen_mul_log hκε_pos, inv_div]
    let S0 : ℂ := QuantumLinSys.Fourier.hDisc J K Δy Δz x
    let S1 : ℂ :=
      (1 / ((Real.sqrt (2 * Real.pi) : ℂ) * (x : ℂ))) *
        ∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), fbTerm Δz x yJ k
    let S2 : ℂ :=
      (1 / ((Real.sqrt (2 * Real.pi) : ℂ) * (x : ℂ))) * ∑' k : ℤ, fbTerm Δz x yJ k
    let S3 : ℂ :=
      (1 / ((Real.sqrt (2 * Real.pi) : ℂ) * (x : ℂ))) *
        ∑' k : ℤ, (Δz : ℂ) * (Real.exp (-((k : ℝ) * Δz) ^ 2 / 2) : ℂ)
    let S4 : ℂ := ((1 / x : ℝ) : ℂ)
    have hFS1a : ‖S0 - S1‖ ≤ ε / 4 :=
      fs1a_bound hL_gt_half hε0 hΔy_pos hΔz_pos hΔy_ub hx_ne hJΔy hKΔz hθ_bound
    have hFS1b : ‖S1 - S2‖ ≤ ε / 4 :=
      fs1b_bound hκ hε0 hε1 hL_pos rfl hΔz_pos hKΔz hx_abs_pos hinv_x hfb_sum hfb_norm_sum hmaj_sum
    have hFS1c : ‖S2 - S3‖ ≤ ε / 4 :=
      fs1c_bound hκ hε0 hε1 hL_pos rfl rfl hΔz_pos hx_bounds.1 hx_bounds.2 hinv_x
        rfl ha_ge_1 hπ_div_Δz_lb hexp_a_le hfb_sum
    have hFS1d : ‖S3 - S4‖ ≤ ε / 4 :=
      fs1d_bound hκ hε0 hε1 hΔz_pos hinv_x rfl ha_ge_1 hexp_a_le
    have hsplit : S0 - S4 = (S0 - S1) + (S1 - S2) + (S2 - S3) + (S3 - S4) := by ring
    change ‖S0 - S4‖ ≤ ε
    rw [hsplit]
    calc
      ‖(S0 - S1) + (S1 - S2) + (S2 - S3) + (S3 - S4)‖
          ≤ ‖(S0 - S1) + (S1 - S2) + (S2 - S3)‖ + ‖S3 - S4‖ := norm_add_le _ _
      _ ≤ ‖(S0 - S1) + (S1 - S2)‖ + ‖S2 - S3‖ + ‖S3 - S4‖ := by
            gcongr; exact norm_add_le _ _
      _ ≤ ‖S0 - S1‖ + ‖S1 - S2‖ + ‖S2 - S3‖ + ‖S3 - S4‖ := by
            gcongr; exact norm_add_le _ _
      _ ≤ ε / 4 + ε / 4 + ε / 4 + ε / 4 := by gcongr
      _ = ε := by ring
