-- Prove2me | solution 1 for StrongConv.cNorm_iteratedDeriv_div_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-04T23:27:06.873031+00:00
-- url     : https://prove2.me/submissions/ce6f5d57-7954-41b0-af63-6abf62b90b97

import Definitions.Def_StrongConv
import Theorems.Thm_StrongConv_cNorm_iteratedDeriv_le
import Mathlib

section
section
namespace StrongConvS4

open Nat

lemma fact_two_mul (k : ℕ) (hk : 1 ≤ k) :
    ((2 * k).factorial : ℝ) = 2 ^ k * k.factorial * ((2 * k - 1).doubleFactorial : ℝ) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h := Nat.factorial_eq_mul_doubleFactorial (2 * (j + 1) - 1)
  have e : 2 * (j + 1) - 1 + 1 = 2 * (j + 1) := by omega
  rw [e] at h
  have h2 := Nat.doubleFactorial_two_mul (j + 1)
  rw [h, h2]
  push_cast
  ring

lemma fact_two_mul_ge (k : ℕ) (hk : 1 ≤ k) : 2 * 6 ^ (k - 1) ≤ (2 * k).factorial := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    have : (2 * (k + 1)).factorial = (2 * k + 2) * (2 * k + 1) * (2 * k).factorial := by
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
      ring
    rw [this]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at ih ⊢
    calc 2 * 6 ^ (j + 1) = 6 * (2 * 6 ^ j) := by ring
      _ ≤ (2 * (j + 1) + 2) * (2 * (j + 1) + 1) * (2 * 6 ^ j) := by
          apply Nat.mul_le_mul_right; nlinarith
      _ ≤ _ := Nat.mul_le_mul_left _ ih

lemma term_le (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (k : ℕ) (hk : 1 ≤ k) :
    y ^ k / ((2 * k).factorial : ℝ) ≤ (y / 2) * (1 / 6) ^ (k - 1) := by
  have h1 : (2 : ℝ) * 6 ^ (k - 1) ≤ ((2 * k).factorial : ℝ) := by exact_mod_cast fact_two_mul_ge k hk
  have hpos : (0 : ℝ) < 2 * 6 ^ (k - 1) := by positivity
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h1 hpos ⊢
  have hyj : y ^ j ≤ 1 := pow_le_one₀ hy0 hy1
  rw [div_le_iff₀ (lt_of_lt_of_le hpos h1)]
  calc y ^ (j + 1) = y * y ^ j := by ring
    _ ≤ y * 1 := by gcongr
    _ = y / 2 * (1 / 6) ^ j * (2 * 6 ^ j) := by
        rw [one_div, inv_pow]; field_simp
    _ ≤ _ := by gcongr

lemma partial_sum_le (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (m : ℕ) :
    ∑ k ∈ Finset.Icc 1 m, y ^ k / ((2 * k).factorial : ℝ) ≤ (y / 2) * (6 / 5) := by
  calc ∑ k ∈ Finset.Icc 1 m, y ^ k / ((2 * k).factorial : ℝ)
      ≤ ∑ k ∈ Finset.Icc 1 m, (y / 2) * (1 / 6 : ℝ) ^ (k - 1) :=
        Finset.sum_le_sum fun k hk => term_le y hy0 hy1 k (Finset.mem_Icc.1 hk).1
    _ = (y / 2) * ∑ j ∈ Finset.range m, (1 / 6 : ℝ) ^ j := by
        rw [← Finset.mul_sum]
        congr 1
        induction m with
        | zero => simp
        | succ n ih =>
          rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]
          simp
    _ ≤ (y / 2) * (6 / 5) := by
        gcongr
        rw [geom_sum_eq (by norm_num)]
        have : (0 : ℝ) ≤ (1 / 6) ^ m := by positivity
        rw [div_le_iff_of_neg (by norm_num)]
        linarith

/-- The algebraic core of the rational Markov induction. -/
lemma markov_induction (b c : ℝ) (M : ℕ → ℝ) (hb : 0 ≤ b) (hc : 1 ≤ c) (hM0 : 0 ≤ M 0)
    (hM : ∀ m, 1 ≤ m → M m ≤ 2 * c * ∑ k ∈ Finset.Icc 1 m,
      (m.choose k : ℝ) * ((2 * b) ^ k / ((2 * k - 1).doubleFactorial : ℝ)) * M (m - k)) :
    ∀ m, M m ≤ m.factorial * (5 * c * b) ^ m * M 0 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    have hc0 : 0 < c := by linarith
    set y : ℝ := 4 / (5 * c) with hy
    have hy0 : 0 ≤ y := by positivity
    have hy1 : y ≤ 1 := by
      rw [hy, div_le_one (by positivity)]; linarith
    have hterm : ∀ k ∈ Finset.Icc 1 m,
        (m.choose k : ℝ) * ((2 * b) ^ k / ((2 * k - 1).doubleFactorial : ℝ)) * M (m - k)
        ≤ (m.factorial : ℝ) * (5 * c * b) ^ m * M 0 * (y ^ k / ((2 * k).factorial : ℝ)) := by
      intro k hk
      obtain ⟨hk1, hkm⟩ := Finset.mem_Icc.1 hk
      have hcoef : 0 ≤ (m.choose k : ℝ) * ((2 * b) ^ k / ((2 * k - 1).doubleFactorial : ℝ)) := by
        positivity
      have h1 := mul_le_mul_of_nonneg_left (ih (m - k) (by omega)) hcoef
      refine h1.trans (le_of_eq ?_)
      have hch := Nat.choose_mul_factorial_mul_factorial hkm
      have hch' : (m.choose k : ℝ) * k.factorial * (m - k).factorial = m.factorial := by
        exact_mod_cast hch
      have hf := fact_two_mul k hk1
      have hkf : (k.factorial : ℝ) ≠ 0 := by positivity
      have hdf : ((2 * k - 1).doubleFactorial : ℝ) ≠ 0 := by positivity
      have hmk : (5 * c * b) ^ m = (5 * c * b) ^ (m - k) * (5 * c * b) ^ k := by
        rw [← pow_add]; congr 1; omega
      have e1 : (5 * c * b) ^ k = (5 * c) ^ k * b ^ k := mul_pow _ _ _
      have e2 : (2 * b) ^ k = 2 ^ k * b ^ k := mul_pow _ _ _
      have e3 : y ^ k = 2 ^ k * 2 ^ k / (5 * c) ^ k := by
        rw [hy, div_pow, ← mul_pow]; norm_num
      have hck : (5 * c) ^ k ≠ 0 := by positivity
      rw [hf, hmk, e1, e2, e3, ← hch']
      field_simp
    have hsum := Finset.sum_le_sum hterm
    rw [← Finset.mul_sum] at hsum
    have hps := partial_sum_le y hy0 hy1 m
    have hpos : 0 ≤ (m.factorial : ℝ) * (5 * c * b) ^ m * M 0 := by positivity
    calc M m ≤ 2 * c * ∑ k ∈ Finset.Icc 1 m,
          (m.choose k : ℝ) * ((2 * b) ^ k / ((2 * k - 1).doubleFactorial : ℝ)) * M (m - k) :=
          hM m hm
      _ ≤ 2 * c * ((m.factorial : ℝ) * (5 * c * b) ^ m * M 0 *
            ∑ k ∈ Finset.Icc 1 m, y ^ k / ((2 * k).factorial : ℝ)) := by gcongr
      _ ≤ 2 * c * ((m.factorial : ℝ) * (5 * c * b) ^ m * M 0 * (y / 2 * (6 / 5))) := by gcongr
      _ = (m.factorial : ℝ) * (5 * c * b) ^ m * M 0 * (2 * c * (y / 2 * (6 / 5))) := by ring
      _ ≤ (m.factorial : ℝ) * (5 * c * b) ^ m * M 0 * 1 := by
          gcongr
          rw [hy]; field_simp; norm_num
      _ = _ := by ring

end StrongConvS4

end
end

section
section
namespace StrongConvS4

/-- Differentiability of every iterated derivative of a smooth-on-open-set function. -/
lemma diffAt_iteratedDeriv {r : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hr : ContDiffOn ℝ (⊤ : ℕ∞) r U) (j : ℕ) {x : ℝ} (hx : x ∈ U) :
    DifferentiableAt ℝ (iteratedDeriv j r) x := by
  have h1 : DifferentiableOn ℝ (iteratedDerivWithin j r U) U :=
    hr.differentiableOn_iteratedDerivWithin
      (by exact_mod_cast ENat.natCast_lt_top j) hU.uniqueDiffOn
  have h2 : Set.EqOn (iteratedDerivWithin j r U) (iteratedDeriv j r) U := fun y hy =>
    iteratedDerivWithin_of_isOpen hU hy
  exact ((h1.congr (fun y hy => (h2 hy).symm)).differentiableAt (hU.mem_nhds hx))

lemma pascal (n : ℕ) (R G : ℕ → ℝ) :
    ∑ k ∈ Finset.range (n + 1 + 1), ((n + 1).choose k : ℝ) * R (n + 1 - k) * G k
      = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * R (n - k + 1) * G k
        + ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * R (n - k) * G (k + 1) := by
  rw [Finset.sum_range_succ' _ (n + 1)]
  simp only [Nat.choose_succ_succ, Nat.cast_add, add_mul, Finset.sum_add_distrib]
  have h2 : ∑ k ∈ Finset.range (n + 1), (n.choose (k + 1) : ℝ) * R (n + 1 - (k + 1)) * G (k + 1)
      = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * R (n - k + 1) * G k
        - (n.choose 0 : ℝ) * R (n + 1 - 0) * G 0 := by
    have := Finset.sum_range_succ' (fun k => (n.choose k : ℝ) * R (n + 1 - k) * G k) (n + 1)
    rw [Finset.sum_range_succ] at this
    simp only [Nat.choose_succ_self, Nat.cast_zero, zero_mul] at this
    have e : ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * R (n - k + 1) * G k
        = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * R (n + 1 - k) * G k := by
      apply Finset.sum_congr rfl
      intro k hk
      have : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
      rw [show n + 1 - k = n - k + 1 by omega]
    rw [e]; linarith
  have h3 : ∀ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * R (n + 1 - (k + 1)) * G (k + 1)
      = (n.choose k : ℝ) * R (n - k) * G (k + 1) := by
    intro k _; simp
  have e0 : ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * R (n + 1 - (k + 1)) * G (k + 1)
      = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * R (n - k) * G (k + 1) :=
    Finset.sum_congr rfl h3
  simp only [Nat.choose_zero_right, Nat.cast_one, Nat.succ_eq_add_one] at *
  linarith

/-- Leibniz rule for `F = r * G` on an open set. -/
lemma leibniz {F r G : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hr : ContDiffOn ℝ (⊤ : ℕ∞) r U) (hG : ContDiffOn ℝ (⊤ : ℕ∞) G U)
    (hF : ∀ x ∈ U, F x = r x * G x) (n : ℕ) {x : ℝ} (hx : x ∈ U) :
    iteratedDeriv n F x =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * iteratedDeriv (n - k) r x * iteratedDeriv k G x := by
  have key : ∀ n : ℕ, Set.EqOn (iteratedDeriv n F)
      (fun x => ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℝ) * iteratedDeriv (n - k) r x * iteratedDeriv k G x) U := by
    intro n
    induction n with
    | zero =>
      intro y hy
      simp [hF y hy]
    | succ n ih =>
      intro y hy
      have e1 : iteratedDeriv (n + 1) F y = deriv (iteratedDeriv n F) y := by
        rw [iteratedDeriv_succ]
      have e2 : deriv (iteratedDeriv n F) y =
          deriv (fun x => ∑ k ∈ Finset.range (n + 1),
            (n.choose k : ℝ) * iteratedDeriv (n - k) r x * iteratedDeriv k G x) y := by
        apply Filter.EventuallyEq.deriv_eq
        filter_upwards [hU.mem_nhds hy] with z hz using ih hz
      rw [e1, e2]
      have hd : ∀ k ∈ Finset.range (n + 1), HasDerivAt
          (fun x => (n.choose k : ℝ) * iteratedDeriv (n - k) r x * iteratedDeriv k G x)
          ((n.choose k : ℝ) * (iteratedDeriv (n - k + 1) r y * iteratedDeriv k G y
            + iteratedDeriv (n - k) r y * iteratedDeriv (k + 1) G y)) y := by
        intro k _
        have h1 : HasDerivAt (iteratedDeriv (n - k) r) (iteratedDeriv (n - k + 1) r y) y := by
          rw [iteratedDeriv_succ]; exact (diffAt_iteratedDeriv hU hr _ hy).hasDerivAt
        have h2 : HasDerivAt (iteratedDeriv k G) (iteratedDeriv (k + 1) G y) y := by
          rw [iteratedDeriv_succ]; exact (diffAt_iteratedDeriv hU hG _ hy).hasDerivAt
        have := ((h1.const_mul (n.choose k : ℝ)).mul h2)
        refine HasDerivAt.congr_deriv this ?_
        ring
      have hs := HasDerivAt.fun_sum hd
      rw [hs.deriv]
      -- Pascal recombination
      simp only [mul_add, Finset.sum_add_distrib]
      have hA : ∑ k ∈ Finset.range (n + 1 + 1), ((n + 1).choose k : ℝ) *
            iteratedDeriv (n + 1 - k) r y * iteratedDeriv k G y
          = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * iteratedDeriv (n - k + 1) r y
              * iteratedDeriv k G y
            + ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * iteratedDeriv (n - k) r y
              * iteratedDeriv (k + 1) G y := by
        exact pascal n (fun j => iteratedDeriv j r y) (fun j => iteratedDeriv j G y)
      show _ = ∑ k ∈ Finset.range (n + 1 + 1), ((n + 1).choose k : ℝ) *
            iteratedDeriv (n + 1 - k) r y * iteratedDeriv k G y
      rw [hA]
      simp only [mul_assoc]
  exact key n hx

end StrongConvS4

end
end

section
section
open Polynomial

namespace StrongConv

lemma pcd (h : ℝ[X]) : ContDiff ℝ (⊤ : ℕ∞) (fun x => h.eval x) := by
  have := (Polynomial.contDiff_aeval (𝕜 := ℝ) h ((⊤ : ℕ∞) : WithTop ℕ∞))
  simpa only [Polynomial.coe_aeval_eq_eval] using this

lemma cN_eq (F : ℝ → ℝ) (a : ℝ) : cNorm 0 F 0 a = sSup ((fun x => |F x|) '' Set.Icc 0 a) := by
  simp [cNorm, supOn]

lemma cN_le {F : ℝ → ℝ} {a B : ℝ} (ha : 0 < a) (h : ∀ x ∈ Set.Icc 0 a, |F x| ≤ B) :
    cNorm 0 F 0 a ≤ B := by
  rw [cN_eq]
  apply csSup_le
  · exact ⟨_, Set.mem_image_of_mem _ (Set.left_mem_Icc.2 ha.le)⟩
  · rintro _ ⟨x, hx, rfl⟩; exact h x hx

lemma le_cN {F : ℝ → ℝ} {a x : ℝ} (hF : ContinuousOn F (Set.Icc 0 a)) (hx : x ∈ Set.Icc 0 a) :
    |F x| ≤ cNorm 0 F 0 a := by
  rw [cN_eq]
  apply le_csSup
  · exact (isCompact_Icc.image_of_continuousOn (hF.abs)).bddAbove
  · exact Set.mem_image_of_mem _ hx

lemma cN_nonneg (F : ℝ → ℝ) (a : ℝ) : 0 ≤ cNorm 0 F 0 a := by
  rw [cN_eq]; apply Real.sSup_nonneg; rintro _ ⟨x, _, rfl⟩; exact abs_nonneg _

theorem cNorm_iteratedDeriv_div_le_dev (q m : ℕ) (f g : ℝ[X]) (hf : f.natDegree ≤ q)
    (hg : g.natDegree ≤ q) (a : ℝ) (ha : 0 < a) (hg0 : ∀ x ∈ Set.Icc 0 a, g.eval x ≠ 0) :
    cNorm 0 (iteratedDeriv m (fun x => f.eval x / g.eval x)) 0 a ≤
      m.factorial * (5 * sSup {t | ∃ x ∈ Set.Icc 0 a, ∃ y ∈ Set.Icc 0 a, t = |g.eval x / g.eval y|} *
        (q : ℝ) ^ 2 / a) ^ m * cNorm 0 (fun x => f.eval x / g.eval x) 0 a := by
  set r : ℝ → ℝ := fun x => f.eval x / g.eval x with hr
  set U : Set ℝ := {x | g.eval x ≠ 0} with hUdef
  have hgc : Continuous (fun x => g.eval x) := (pcd g).continuous
  have hU : IsOpen U := isOpen_ne_fun hgc continuous_const
  have hrU : ContDiffOn ℝ (⊤ : ℕ∞) r U :=
    (pcd f).contDiffOn.div (pcd g).contDiffOn (fun x hx => hx)
  have hgU : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => g.eval x) U := (pcd g).contDiffOn
  have hIU : Set.Icc 0 a ⊆ U := fun x hx => hg0 x hx
  have hfU : ∀ x ∈ U, f.eval x = r x * g.eval x := fun x hx => by
    simp only [hr]; field_simp [show g.eval x ≠ 0 from hx]
  -- continuity of iterated derivatives of r on Icc
  have hrc : ∀ j, ContinuousOn (iteratedDeriv j r) (Set.Icc 0 a) := fun j x hx =>
    (StrongConvS4.diffAt_iteratedDeriv hU hrU j (hIU hx)).continuousAt.continuousWithinAt
  have hgcj : ∀ j, ContinuousOn (iteratedDeriv j (fun x => g.eval x)) (Set.Icc 0 a) := fun j =>
    ((pcd g).continuous_iteratedDeriv j (by exact_mod_cast le_top)).continuousOn
  have hfcj : ∀ j, ContinuousOn (iteratedDeriv j (fun x => f.eval x)) (Set.Icc 0 a) := fun j =>
    ((pcd f).continuous_iteratedDeriv j (by exact_mod_cast le_top)).continuousOn
  -- the constant c
  set S : Set ℝ := {t | ∃ x ∈ Set.Icc 0 a, ∃ y ∈ Set.Icc 0 a, t = |g.eval x / g.eval y|} with hS
  have hSb : BddAbove S := by
    have hcont : ContinuousOn (fun p : ℝ × ℝ => |g.eval p.1 / g.eval p.2|)
        (Set.Icc 0 a ×ˢ Set.Icc 0 a) := by
      apply ContinuousOn.abs
      apply ContinuousOn.div (hgc.comp continuous_fst).continuousOn
        (hgc.comp continuous_snd).continuousOn
      rintro ⟨x, y⟩ ⟨_, hy⟩; exact hg0 y hy
    obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_Icc |>.image_of_continuousOn hcont).bddAbove
    refine ⟨B, ?_⟩
    rintro t ⟨x, hx, y, hy, rfl⟩
    exact hB ⟨(x, y), ⟨hx, hy⟩, rfl⟩
  set c := sSup S with hc
  have hcS : ∀ x ∈ Set.Icc 0 a, ∀ y ∈ Set.Icc 0 a, |g.eval x| ≤ c * |g.eval y| := by
    intro x hx y hy
    have h1 : |g.eval x / g.eval y| ≤ c := le_csSup hSb ⟨x, hx, y, hy, rfl⟩
    have hy0 : 0 < |g.eval y| := abs_pos.2 (hg0 y hy)
    rw [abs_div, div_le_iff₀ hy0] at h1
    exact h1
  have hc1 : 1 ≤ c := by
    have h0 : (0 : ℝ) ∈ Set.Icc 0 a := Set.left_mem_Icc.2 ha.le
    have h1 : |g.eval 0 / g.eval 0| ≤ c := le_csSup hSb ⟨0, h0, 0, h0, rfl⟩
    rwa [div_self (hg0 0 h0), abs_one] at h1
  -- M j
  set M : ℕ → ℝ := fun j => cNorm 0 (iteratedDeriv j r) 0 a with hM
  have hM0 : M 0 = cNorm 0 r 0 a := by simp [hM]
  have hMn : ∀ j, 0 ≤ M j := fun j => cN_nonneg _ _
  set b : ℝ := (q : ℝ) ^ 2 / a with hb
  have hb0 : 0 ≤ b := by positivity
  have key := StrongConvS4.markov_induction b c M hb0 hc1 (by rw [hM0]; exact cN_nonneg _ _) ?_ m
  · have e : 5 * c * (q : ℝ) ^ 2 / a = 5 * c * b := by rw [hb]; ring
    simp only [hM0] at key
    simpa [hM, e] using key
  · intro m hm
    -- A_k
    set A : ℕ → ℝ := fun k => (2 * b) ^ k / ((2 * k - 1).doubleFactorial : ℝ) with hA
    have hAn : ∀ k, 0 ≤ A k := fun k => by positivity
    have hApoly : ∀ (h : ℝ[X]), h.natDegree ≤ q → ∀ k,
        cNorm 0 (iteratedDeriv k (fun x => h.eval x)) 0 a ≤ A k * cNorm 0 (fun x => h.eval x) 0 a := by
      intro h hh k
      have := cNorm_iteratedDeriv_le q k h hh a ha
      calc _ ≤ _ := this
        _ = A k * _ := by
          simp only [hA, hb]
          rw [show (2 * (q : ℝ) ^ 2 / a) = 2 * ((q : ℝ) ^ 2 / a) by ring]
          ring
    -- bounds on f and g sup norms relative to one point
    have hr0 : ∀ y ∈ Set.Icc 0 a, |r y| ≤ M 0 := fun y hy => by
      have := le_cN (hrc 0) hy
      simpa [hM] using this
    set Nr := M 0 with hNr
    show cNorm 0 (iteratedDeriv m r) 0 a ≤ _
    refine cN_le ha ?_
    · intro x hx
      have hxU := hIU hx
      have hgx : 0 < |g.eval x| := abs_pos.2 (hg0 x hx)
      have hNg : cNorm 0 (fun x => g.eval x) 0 a ≤ c * |g.eval x| :=
        cN_le ha (fun y hy => hcS y hy x hx)
      have hNf : cNorm 0 (fun x => f.eval x) 0 a ≤ Nr * (c * |g.eval x|) := by
        apply cN_le ha
        intro y hy
        rw [hfU y (hIU hy), abs_mul]
        exact mul_le_mul (hr0 y hy) (hcS y hy x hx) (abs_nonneg _) (hMn 0)
      have hfm : |iteratedDeriv m (fun x => f.eval x) x| ≤ A m * (Nr * (c * |g.eval x|)) :=
        (le_cN (hfcj m) hx).trans ((hApoly f hf m).trans
          (mul_le_mul_of_nonneg_left hNf (hAn m)))
      have hgk : ∀ k, |iteratedDeriv k (fun x => g.eval x) x| ≤ A k * (c * |g.eval x|) :=
        fun k => (le_cN (hgcj k) hx).trans ((hApoly g hg k).trans
          (mul_le_mul_of_nonneg_left hNg (hAn k)))
      have hLeib := StrongConvS4.leibniz hU hrU hgU hfU m hxU
      have hsplit : Finset.range (m + 1) = insert 0 (Finset.Icc 1 m) := by
        ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
      rw [hsplit, Finset.sum_insert (by simp)] at hLeib
      simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero, iteratedDeriv_zero]
        at hLeib
      have hrm : iteratedDeriv m r x * g.eval x =
          iteratedDeriv m (fun x => f.eval x) x - ∑ k ∈ Finset.Icc 1 m,
            (m.choose k : ℝ) * iteratedDeriv (m - k) r x * iteratedDeriv k (fun x => g.eval x) x := by
        linarith
      have hineq : |iteratedDeriv m r x| * |g.eval x| ≤
          A m * (Nr * (c * |g.eval x|)) + ∑ k ∈ Finset.Icc 1 m,
            (m.choose k : ℝ) * (M (m - k) * (A k * (c * |g.eval x|))) := by
        rw [← abs_mul, hrm]
        refine (abs_sub _ _).trans (add_le_add hfm ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
        rw [abs_mul, abs_mul, Nat.abs_cast]
        have hk' := Finset.mem_Icc.1 hk
        have h1 : |iteratedDeriv (m - k) r x| ≤ M (m - k) := by
          have := le_cN (hrc (m - k)) hx; simpa [hM] using this
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul h1 (hgk k) (abs_nonneg _) (hMn _))
          (Nat.cast_nonneg _)
      have hsingle : A m * Nr ≤ ∑ k ∈ Finset.Icc 1 m, (m.choose k : ℝ) * A k * M (m - k) := by
        have := Finset.single_le_sum (f := fun k => (m.choose k : ℝ) * A k * M (m - k))
          (fun k _ => by have := hAn k; have := hMn (m - k); positivity)
          (Finset.mem_Icc.2 ⟨hm, le_rfl⟩)
        simpa [hNr, hM] using this
      have hsn : 0 ≤ ∑ k ∈ Finset.Icc 1 m, (m.choose k : ℝ) * A k * M (m - k) :=
        Finset.sum_nonneg fun k _ => by have := hAn k; have := hMn (m - k); positivity
      have hfin : |iteratedDeriv m r x| * |g.eval x| ≤
          (2 * c * ∑ k ∈ Finset.Icc 1 m, (m.choose k : ℝ) * A k * M (m - k)) * |g.eval x| := by
        refine hineq.trans ?_
        have e : ∑ k ∈ Finset.Icc 1 m, (m.choose k : ℝ) * (M (m - k) * (A k * (c * |g.eval x|)))
            = c * |g.eval x| * ∑ k ∈ Finset.Icc 1 m, (m.choose k : ℝ) * A k * M (m - k) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
        rw [e]
        have : A m * (Nr * (c * |g.eval x|)) ≤
            c * |g.eval x| * ∑ k ∈ Finset.Icc 1 m, (m.choose k : ℝ) * A k * M (m - k) := by
          calc _ = (c * |g.eval x|) * (A m * Nr) := by ring
            _ ≤ _ := by gcongr
        nlinarith
      exact le_of_mul_le_mul_right hfin hgx

end StrongConv

end
end

section
open Polynomial
open StrongConv

theorem solution (q m : ℕ) (f g : ℝ[X]) (hf : f.natDegree ≤ q)
    (hg : g.natDegree ≤ q) (a : ℝ) (ha : 0 < a) (hg0 : ∀ x ∈ Set.Icc 0 a, g.eval x ≠ 0) :
    cNorm 0 (iteratedDeriv m (fun x => f.eval x / g.eval x)) 0 a ≤
      m.factorial * (5 * sSup {t | ∃ x ∈ Set.Icc 0 a, ∃ y ∈ Set.Icc 0 a, t = |g.eval x / g.eval y|} *
        (q : ℝ) ^ 2 / a) ^ m * cNorm 0 (fun x => f.eval x / g.eval x) 0 a := by
  apply StrongConv.cNorm_iteratedDeriv_div_le_dev <;> assumption

end
