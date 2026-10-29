-- Prove2me | solution 1 for SolomonRWRE.Recurrence.lemma_1_5
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T05:05:15.647992+00:00
-- url     : https://prove2.me/submissions/b4df2102-864d-448a-98a6-c4541c216a4e

import Mathlib
import Definitions.Def_SolomonRWRE_Recurrence_Model

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace RWRE15

open SolomonRWRE.Recurrence

/-! ## Part A: the scale function of the birth-death chain -/

/-- real `σ_k = (1 - a_k)/a_k`. -/
noncomputable def sr (a : ℤ → ℝ) (k : ℤ) : ℝ := (1 - a k) / a k

/-- `up n = σ_1 ⋯ σ_n` (`= ρ_n`, `up 0 = 1`). -/
noncomputable def up (a : ℤ → ℝ) (n : ℕ) : ℝ := ∏ j ∈ Finset.range n, sr a ((j : ℤ) + 1)

/-- `dn n = (σ_0 σ_{-1} ⋯ σ_{-n})⁻¹`. -/
noncomputable def dn (a : ℤ → ℝ) (n : ℕ) : ℝ :=
  (sr a 0 * ∏ j ∈ Finset.range n, sr a (-((j : ℤ) + 1)))⁻¹

/-- The scale function: `g (x+1) - g x = up x` for `x ≥ 0`, `= dn (-x-1)` for `x < 0`. -/
noncomputable def g (a : ℤ → ℝ) (x : ℤ) : ℝ :=
  if 0 ≤ x then ∑ k ∈ Finset.range x.toNat, up a k
  else -∑ k ∈ Finset.range (-x).toNat, dn a k

variable {a : ℤ → ℝ}

lemma sr_pos (ha : ∀ n, 0 < a n ∧ a n < 1) (k : ℤ) : 0 < sr a k :=
  div_pos (by linarith [(ha k).2]) (ha k).1

lemma up_pos (ha : ∀ n, 0 < a n ∧ a n < 1) (n : ℕ) : 0 < up a n :=
  Finset.prod_pos (fun j _ => sr_pos ha _)

lemma dn_pos (ha : ∀ n, 0 < a n ∧ a n < 1) (n : ℕ) : 0 < dn a n :=
  inv_pos.2 (mul_pos (sr_pos ha 0) (Finset.prod_pos (fun j _ => sr_pos ha _)))

lemma g_nat (n : ℕ) : g a (n : ℤ) = ∑ k ∈ Finset.range n, up a k := by
  simp [g]

lemma g_neg (n : ℕ) : g a (-(n : ℤ)) = -∑ k ∈ Finset.range n, dn a k := by
  unfold g
  split_ifs with h
  · have : n = 0 := by omega
    subst this; simp
  · simp

lemma up_succ (n : ℕ) : up a (n + 1) = up a n * sr a ((n : ℤ) + 1) := by
  simp [up, Finset.prod_range_succ]

lemma dn_succ (ha : ∀ n, 0 < a n ∧ a n < 1) (n : ℕ) :
    dn a (n + 1) = dn a n / sr a (-((n : ℤ) + 1)) := by
  have h1 := sr_pos ha (-((n : ℤ) + 1))
  simp only [dn, Finset.prod_range_succ]
  rw [div_eq_mul_inv, ← mul_inv, mul_assoc]

lemma g_zero : g a 0 = 0 := by simp [g]

lemma g_one : g a 1 = 1 := by
  have := g_nat (a := a) 1
  simpa [up] using this

lemma g_neg_one : g a (-1) = -(sr a 0)⁻¹ := by
  have := g_neg (a := a) 1
  simpa [dn] using this

/-- Harmonicity: `g x = a_x g(x+1) + (1 - a_x) g(x-1)`. -/
lemma g_harm (ha : ∀ n, 0 < a n ∧ a n < 1) (x : ℤ) :
    a x * g a (x + 1) + (1 - a x) * g a (x - 1) = g a x := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg x
  · rcases n with _ | m
    · have h0 := (ha 0).1; have h1 := (ha 0).2
      simp only [Nat.cast_zero, zero_add, zero_sub]
      rw [g_one, g_neg_one, g_zero, sr]
      have h2 : (1 - a 0) ≠ 0 := by linarith
      field_simp
      ring
    · have e1 : ((m + 1 : ℕ) : ℤ) + 1 = ((m + 2 : ℕ) : ℤ) := by push_cast; ring
      have e2 : ((m + 1 : ℕ) : ℤ) - 1 = ((m : ℕ) : ℤ) := by push_cast; ring
      rw [e1, e2, g_nat, g_nat, g_nat, Finset.sum_range_succ, Finset.sum_range_succ,
        up_succ]
      have h0 := (ha ((m + 1 : ℕ) : ℤ)).1; have h1 := (ha ((m + 1 : ℕ) : ℤ)).2
      have : sr a ((m : ℤ) + 1) = (1 - a ((m + 1 : ℕ) : ℤ)) / a ((m + 1 : ℕ) : ℤ) := by
        simp [sr]
      rw [this]
      field_simp
      ring
  · rcases n with _ | m
    · have h0 := (ha 0).1; have h1 := (ha 0).2
      simp only [Nat.cast_zero, neg_zero, zero_add, zero_sub]
      rw [g_one, g_neg_one, g_zero, sr]
      have h2 : (1 - a 0) ≠ 0 := by linarith
      field_simp
      ring
    · have e1 : -((m + 1 : ℕ) : ℤ) + 1 = -((m : ℕ) : ℤ) := by push_cast; ring
      have e2 : -((m + 1 : ℕ) : ℤ) - 1 = -((m + 2 : ℕ) : ℤ) := by push_cast; ring
      rw [e1, e2, g_neg, g_neg, g_neg, Finset.sum_range_succ, Finset.sum_range_succ,
        dn_succ ha]
      have h0 := (ha (-((m + 1 : ℕ) : ℤ))).1; have h1 := (ha (-((m + 1 : ℕ) : ℤ))).2
      have : sr a (-((m : ℤ) + 1)) = (1 - a (-((m + 1 : ℕ) : ℤ))) / a (-((m + 1 : ℕ) : ℤ)) := by
        simp [sr]
      rw [this]
      have h2 : (1 - a (-((m + 1 : ℕ) : ℤ))) ≠ 0 := by linarith
      field_simp
      ring

lemma g_strictMono (ha : ∀ n, 0 < a n ∧ a n < 1) : StrictMono (g a) := by
  apply strictMono_int_of_lt_succ
  intro x
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg x
  · have e1 : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e1, g_nat, g_nat, Finset.sum_range_succ]
    linarith [up_pos ha n]
  · rcases n with _ | m
    · simp only [Nat.cast_zero, neg_zero, zero_add]
      rw [g_one, g_zero]; norm_num
    · have e1 : -((m + 1 : ℕ) : ℤ) + 1 = -((m : ℕ) : ℤ) := by push_cast; ring
      rw [e1, g_neg, g_neg, Finset.sum_range_succ]
      linarith [dn_pos ha m]

lemma g_le_tsum (ha : ∀ n, 0 < a n ∧ a n < 1) (hs : Summable (up a)) (x : ℤ) :
    g a x ≤ ∑' n, up a n := by
  have hnn : 0 ≤ ∑' n, up a n := tsum_nonneg (fun n => (up_pos ha n).le)
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg x
  · rw [g_nat]
    exact hs.sum_le_tsum _ (fun i _ => (up_pos ha i).le)
  · rw [g_neg]
    have : 0 ≤ ∑ k ∈ Finset.range n, dn a k := Finset.sum_nonneg (fun i _ => (dn_pos ha i).le)
    linarith

lemma neg_tsum_le_g (ha : ∀ n, 0 < a n ∧ a n < 1) (hs : Summable (dn a)) (x : ℤ) :
    -∑' n, dn a n ≤ g a x := by
  have hnn : 0 ≤ ∑' n, dn a n := tsum_nonneg (fun n => (dn_pos ha n).le)
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg x
  · rw [g_nat]
    have : 0 ≤ ∑ k ∈ Finset.range n, up a k := Finset.sum_nonneg (fun i _ => (up_pos ha i).le)
    linarith
  · rw [g_neg]
    have := hs.sum_le_tsum (Finset.range n) (fun i _ => (dn_pos ha i).le)
    linarith

lemma g_unbdd_above (ha : ∀ n, 0 < a n ∧ a n < 1) (hs : ¬ Summable (up a)) (C : ℝ) :
    ∃ x, C < g a x := by
  have := (not_summable_iff_tendsto_nat_atTop_of_nonneg (fun n => (up_pos ha n).le)).1 hs
  obtain ⟨n, hn⟩ := (this.eventually (eventually_gt_atTop C)).exists
  exact ⟨n, by rw [g_nat]; exact hn⟩

lemma g_unbdd_below (ha : ∀ n, 0 < a n ∧ a n < 1) (hs : ¬ Summable (dn a)) (C : ℝ) :
    ∃ x, g a x < C := by
  have := (not_summable_iff_tendsto_nat_atTop_of_nonneg (fun n => (dn_pos ha n).le)).1 hs
  obtain ⟨n, hn⟩ := (this.eventually (eventually_gt_atTop (-C))).exists
  exact ⟨-(n : ℤ), by rw [g_neg]; linarith⟩

/-! ### The series of the statement in terms of `up`, `dn` -/

lemma tsum_ofReal_eq_top_iff {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) :
    ∑' n, ENNReal.ofReal (f n) = ∞ ↔ ¬ Summable f := by
  constructor
  · intro h hs
    rw [← ENNReal.ofReal_tsum_of_nonneg hf hs] at h
    exact ENNReal.ofReal_ne_top h
  · intro hns
    by_contra h
    apply hns
    have := ENNReal.summable_toReal h
    simpa [ENNReal.toReal_ofReal (hf _)] using this

lemma sigma_eq (ha : ∀ n, 0 < a n ∧ a n < 1) (k : ℤ) : sigma a k = ENNReal.ofReal (sr a k) := by
  unfold sigma sr
  rw [ENNReal.ofReal_div_of_pos (ha k).1]

lemma prod_Icc_pos {M : Type*} [CommMonoid M] (f : ℤ → M) (n : ℕ) :
    ∏ k ∈ Finset.Icc (1 : ℤ) ((n : ℤ) + 1), f k =
      ∏ j ∈ Finset.range (n + 1), f ((j : ℤ) + 1) := by
  symm
  apply Finset.prod_nbij' (fun j : ℕ => (j : ℤ) + 1) (fun k : ℤ => (k - 1).toNat)
  · intro j hj; simp only [Finset.mem_range, Finset.mem_Icc] at hj ⊢
    omega
  · intro k hk; simp only [Finset.mem_range, Finset.mem_Icc] at hk ⊢
    omega
  · intro j _; simp
  · intro k hk; simp only [Finset.mem_Icc] at hk; omega
  · intro j _; rfl

lemma prod_Icc_neg {M : Type*} [CommMonoid M] (f : ℤ → M) (n : ℕ) :
    ∏ k ∈ Finset.Icc (-((n : ℤ) + 1)) (-1), f k =
      ∏ j ∈ Finset.range (n + 1), f (-((j : ℤ) + 1)) := by
  symm
  apply Finset.prod_nbij' (fun j : ℕ => -((j : ℤ) + 1)) (fun k : ℤ => (-k - 1).toNat)
  · intro j hj; simp only [Finset.mem_range, Finset.mem_Icc] at hj ⊢
    omega
  · intro k hk; simp only [Finset.mem_range, Finset.mem_Icc] at hk ⊢
    omega
  · intro j _; simp
  · intro k hk; simp only [Finset.mem_Icc] at hk; omega
  · intro j _; rfl

lemma rho_pos_eq (ha : ∀ n, 0 < a n ∧ a n < 1) (n : ℕ) :
    rho a ((n : ℤ) + 1) = ENNReal.ofReal (up a (n + 1)) := by
  unfold rho
  rw [if_pos (by omega), prod_Icc_pos (fun k => sigma a k) n, up,
    ENNReal.ofReal_prod_of_nonneg (fun j _ => (sr_pos ha _).le)]
  exact Finset.prod_congr rfl (fun j _ => sigma_eq ha _)

lemma rho_neg_inv_eq (ha : ∀ n, 0 < a n ∧ a n < 1) (n : ℕ) :
    (rho a (-((n : ℤ) + 1)))⁻¹ = ENNReal.ofReal (sr a 0 * dn a (n + 1)) := by
  have hP : 0 < ∏ j ∈ Finset.range (n + 1), sr a (-((j : ℤ) + 1)) :=
    Finset.prod_pos (fun j _ => sr_pos ha _)
  have h0 := sr_pos ha 0
  have : sr a 0 * dn a (n + 1) = (∏ j ∈ Finset.range (n + 1), sr a (-((j : ℤ) + 1)))⁻¹ := by
    unfold dn
    rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ h0.ne', one_mul]
  rw [this, ENNReal.ofReal_inv_of_pos hP]
  congr 1
  unfold rho
  rw [if_neg (by omega), prod_Icc_neg (fun k => sigma a k) n,
    ENNReal.ofReal_prod_of_nonneg (fun j _ => (sr_pos ha _).le)]
  exact Finset.prod_congr rfl (fun j _ => sigma_eq ha _)

lemma series_pos_iff (ha : ∀ n, 0 < a n ∧ a n < 1) :
    ∑' n : ℕ, rho a ((n : ℤ) + 1) = ∞ ↔ ¬ Summable (up a) := by
  simp_rw [rho_pos_eq ha]
  rw [tsum_ofReal_eq_top_iff (fun n => (up_pos ha _).le)]
  rw [summable_nat_add_iff 1 (f := up a)]

lemma series_neg_iff (ha : ∀ n, 0 < a n ∧ a n < 1) :
    ∑' n : ℕ, (rho a (-((n : ℤ) + 1)))⁻¹ = ∞ ↔ ¬ Summable (dn a) := by
  simp_rw [rho_neg_inv_eq ha]
  rw [tsum_ofReal_eq_top_iff (fun n => (mul_pos (sr_pos ha 0) (dn_pos ha _)).le)]
  rw [summable_mul_left_iff (sr_pos ha 0).ne', summable_nat_add_iff 1 (f := dn a)]

/-! ## Part B: a deterministic lemma on nearest-neighbour paths -/

lemma det_tendsto (x : ℕ → ℤ) (hx : ∀ n, x (n + 1) = x n + 1 ∨ x (n + 1) = x n - 1)
    (G : ℤ → ℝ) (hG : StrictMono G) (L : ℝ)
    (hL : Tendsto (fun n => G (x n)) atTop (𝓝 L)) :
    Tendsto x atTop atTop ∨ Tendsto x atTop atBot := by
  have step1 : ∀ K : ℕ, ∀ᶠ n in atTop, (K : ℤ) < |x n| := by
    intro K
    by_contra hcon
    rw [Filter.not_eventually] at hcon
    set T : Finset ℤ := Finset.Icc (-(K : ℤ) - 1) K with hT
    have hne : T.Nonempty := ⟨0, by simp [hT]⟩
    obtain ⟨z0, -, hz0⟩ := Finset.exists_min_image T (fun z => G (z + 1) - G z) hne
    set δ := G (z0 + 1) - G z0 with hδdef
    have hδ : 0 < δ := sub_pos.2 (hG (by omega))
    have hd : Tendsto (fun n => G (x (n + 1)) - G (x n)) atTop (𝓝 0) := by
      have := (hL.comp (tendsto_add_atTop_nat 1)).sub hL
      simpa using this
    have e1 := (tendsto_order.1 hd).2 δ hδ
    have e2 := (tendsto_order.1 hd).1 (-δ) (by linarith)
    obtain ⟨n, hn1, hn2, hn3⟩ := (hcon.and_eventually (e1.and e2)).exists
    have hn1' : |x n| ≤ K := not_lt.1 hn1
    have hb := abs_le.1 hn1'
    rcases hx n with h | h
    · have hm : x n ∈ T := by simp [hT]; omega
      have h3 : δ ≤ G (x n + 1) - G (x n) := hz0 (x n) hm
      rw [h] at hn2
      linarith
    · have hm : x n - 1 ∈ T := by simp [hT]; omega
      have h3 : δ ≤ G (x n - 1 + 1) - G (x n - 1) := hz0 (x n - 1) hm
      rw [sub_add_cancel] at h3
      rw [h] at hn3
      linarith
  obtain ⟨N, hN⟩ := eventually_atTop.1 (step1 0)
  have hN' : ∀ n ≥ N, x n ≠ 0 := by
    intro n hn h; have := hN n hn; rw [h] at this; simp at this
  rcases lt_or_gt_of_ne (hN' N le_rfl) with hneg | hpos
  · have hall : ∀ n ≥ N, x n < 0 := by
      intro n hn
      induction n, hn using Nat.le_induction with
      | base => exact hneg
      | succ m hm ih =>
        have := hN' (m + 1) (by omega)
        rcases hx m with h | h <;> omega
    right
    rw [tendsto_atBot]
    intro b
    filter_upwards [step1 (-b).toNat, eventually_ge_atTop N] with n h1 h2
    have := hall n h2
    rw [abs_of_neg this] at h1
    omega
  · have hall : ∀ n ≥ N, 0 < x n := by
      intro n hn
      induction n, hn using Nat.le_induction with
      | base => exact hpos
      | succ m hm ih =>
        have := hN' (m + 1) (by omega)
        rcases hx m with h | h <;> omega
    left
    rw [tendsto_atTop]
    intro b
    filter_upwards [step1 b.toNat, eventually_ge_atTop N] with n h1 h2
    have := hall n h2
    rw [abs_of_pos this] at h1
    omega

lemma not_top_of_unbdd (x : ℕ → ℤ) (G : ℤ → ℝ) (hG : StrictMono G) (L : ℝ)
    (hL : Tendsto (fun n => G (x n)) atTop (𝓝 L)) (hun : ∀ C, ∃ z, C < G z)
    (hx : Tendsto x atTop atTop) : False := by
  obtain ⟨z, hz⟩ := hun (L + 1)
  have e1 := (tendsto_order.1 hL).2 (L + 1) (by linarith)
  obtain ⟨n, h1, h2⟩ := (e1.and (tendsto_atTop.1 hx z)).exists
  have := hG.monotone h2
  linarith

lemma not_bot_of_unbdd (x : ℕ → ℤ) (G : ℤ → ℝ) (hG : StrictMono G) (L : ℝ)
    (hL : Tendsto (fun n => G (x n)) atTop (𝓝 L)) (hun : ∀ C, ∃ z, G z < C)
    (hx : Tendsto x atTop atBot) : False := by
  obtain ⟨z, hz⟩ := hun (L - 1)
  have e1 := (tendsto_order.1 hL).1 (L - 1) (by linarith)
  obtain ⟨n, h1, h2⟩ := (e1.and (tendsto_atBot.1 hx z)).exists
  have := hG.monotone h2
  linarith


/-! ## Part C: the chain, cylinders, the filtration and the martingale transform -/

section Prob

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {a : ℤ → ℝ} {X : ℕ → Ω → ℤ}

/-- the cylinder `{X_0 = x_0, …, X_n = x_n}`. -/
def cyl (X : ℕ → Ω → ℤ) (n : ℕ) (x : ℕ → ℤ) : Set Ω := {ω | ∀ k ≤ n, X k ω = x k}

/-- extend a finite prefix by zeros. -/
def trunc (n : ℕ) (u : Fin (n + 1) → ℤ) (k : ℕ) : ℤ := if hk : k < n + 1 then u ⟨k, hk⟩ else 0

lemma trunc_of_lt {n k : ℕ} (u : Fin (n + 1) → ℤ) (hk : k < n + 1) : trunc n u k = u ⟨k, hk⟩ :=
  dif_pos hk

lemma null_of_cyl (n : ℕ) (E : Set Ω) (h : ∀ x : ℕ → ℤ, P (cyl X n x ∩ E) = 0) : P E = 0 := by
  have hsub : E ⊆ ⋃ u : Fin (n + 1) → ℤ, cyl X n (trunc n u) ∩ E := by
    intro ω hω
    refine Set.mem_iUnion.2 ⟨fun i => X i ω, ?_, hω⟩
    intro k hk
    rw [trunc_of_lt _ (by omega)]
  exact measure_mono_null hsub (measure_iUnion_null (fun u => h _))

lemma ae_X0 (hX : IsChainInEnv P a 0 X) : ∀ᵐ ω ∂P, X 0 ω = 0 := by
  rw [ae_iff]
  apply null_of_cyl (X := X) 0
  intro x
  by_cases hx : x 0 = 0
  · have : cyl X 0 x ∩ {ω | ¬X 0 ω = 0} = ∅ := by
      ext ω
      simp only [cyl, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
        not_and, not_not]
      intro h; rw [h 0 le_rfl, hx]
    rw [this, measure_empty]
  · apply measure_mono_null Set.inter_subset_left
    show P {ω | ∀ k ≤ 0, X k ω = x k} = 0
    rw [hX.2.2 0 x]; simp [hx]

lemma ae_step (hX : IsChainInEnv P a 0 X) (n : ℕ) :
    ∀ᵐ ω ∂P, X (n + 1) ω = X n ω + 1 ∨ X (n + 1) ω = X n ω - 1 := by
  rw [ae_iff]
  apply null_of_cyl (X := X) (n + 1)
  intro x
  by_cases hx : x (n + 1) = x n + 1 ∨ x (n + 1) = x n - 1
  · have : cyl X (n + 1) x ∩
        {ω | ¬(X (n + 1) ω = X n ω + 1 ∨ X (n + 1) ω = X n ω - 1)} = ∅ := by
      ext ω
      simp only [cyl, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
        not_and, not_not]
      intro h; rw [h (n + 1) le_rfl, h n (by omega)]; exact hx
    rw [this, measure_empty]
  · apply measure_mono_null Set.inter_subset_left
    show P {ω | ∀ k ≤ n + 1, X k ω = x k} = 0
    rw [hX.2.2 (n + 1) x]
    push_neg at hx
    rw [Finset.prod_eq_zero (i := n) (by simp)]
    · simp
    · unfold step; rw [if_neg hx.1, if_neg hx.2]

lemma ae_good (hX : IsChainInEnv P a 0 X) :
    ∀ᵐ ω ∂P, X 0 ω = 0 ∧ ∀ n, (X (n + 1) ω = X n ω + 1 ∨ X (n + 1) ω = X n ω - 1) := by
  filter_upwards [ae_X0 hX, ae_all_iff.2 (ae_step hX)] with ω h1 h2 using ⟨h1, h2⟩

lemma abs_le_of_good {ω : Ω} (h0 : X 0 ω = 0)
    (hs : ∀ n, (X (n + 1) ω = X n ω + 1 ∨ X (n + 1) ω = X n ω - 1)) (n : ℕ) :
    |X n ω| ≤ n := by
  induction n with
  | zero => simp [h0]
  | succ m ih =>
    rw [abs_le] at ih ⊢
    rcases hs m with h | h <;> rw [h] <;> push_cast <;> omega

/-- the prefix map. -/
def Φ (X : ℕ → Ω → ℤ) (n : ℕ) (ω : Ω) : Fin (n + 1) → ℤ := fun i => X i ω

lemma meas_coord_comap (n k : ℕ) (hk : k ≤ n) :
    Measurable[MeasurableSpace.comap (Φ X n) inferInstance] (X k) := by
  have : X k = (fun v : Fin (n + 1) → ℤ => v ⟨k, by omega⟩) ∘ Φ X n := rfl
  rw [this]
  exact (measurable_pi_apply _).comp (comap_measurable _)

/-- the natural filtration of the chain. -/
def filt (hmeas : ∀ n, Measurable (X n)) : Filtration ℕ (inferInstance : MeasurableSpace Ω) where
  seq n := MeasurableSpace.comap (Φ X n) inferInstance
  mono' := by
    intro n m hnm
    show MeasurableSpace.comap (Φ X n) inferInstance ≤ MeasurableSpace.comap (Φ X m) inferInstance
    have hr : Measurable (fun (v : Fin (m + 1) → ℤ) (i : Fin (n + 1)) => v (Fin.castLE (by omega) i)) :=
      measurable_pi_lambda _ (fun i => measurable_pi_apply _)
    have hm : Measurable[MeasurableSpace.comap (Φ X m) inferInstance] (Φ X n) :=
      hr.comp (comap_measurable (Φ X m))
    intro s hs
    obtain ⟨B, hB, rfl⟩ := hs
    exact hm hB
  le' := by
    intro n
    exact Measurable.comap_le (measurable_pi_iff.2 (fun i => hmeas i))

lemma filt_meas_X (hmeas : ∀ n, Measurable (X n)) (n k : ℕ) (hk : k ≤ n) :
    Measurable[filt hmeas n] (X k) := meas_coord_comap n k hk

open scoped Classical in
/-- the increment of the martingale transform. -/
noncomputable def incr (X : ℕ → Ω → ℤ) (G : ℤ → ℝ) (S : Set ℤ) (j : ℕ) (ω : Ω) : ℝ :=
  if ∀ k ≤ j, X k ω ∈ S then G (X (j + 1) ω) - G (X j ω) else 0

/-- the martingale transform `Y_n = G(X_{n ∧ e}) - G(X_0)`, `e` the exit time of `S`. -/
noncomputable def Yp (X : ℕ → Ω → ℤ) (G : ℤ → ℝ) (S : Set ℤ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.range n, incr X G S j ω

lemma Yp_succ (G : ℤ → ℝ) (S : Set ℤ) (n : ℕ) (ω : Ω) :
    Yp X G S (n + 1) ω = Yp X G S n ω + incr X G S n ω := by
  simp [Yp, Finset.sum_range_succ]

lemma incr_meas (hmeas : ∀ n, Measurable (X n)) (G : ℤ → ℝ) (S : Set ℤ) (j m : ℕ)
    (hjm : j + 1 ≤ m) : Measurable[filt hmeas m] (incr X G S j) := by
  have hset : MeasurableSet[filt hmeas m] {ω | ∀ k ≤ j, X k ω ∈ S} := by
    have : {ω | ∀ k ≤ j, X k ω ∈ S} = ⋂ k : Fin (j + 1), X k ⁻¹' S := by
      ext ω; simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage]
      exact ⟨fun h k => h k (Nat.lt_succ_iff.1 k.2), fun h k hk => h ⟨k, by omega⟩⟩
    rw [this]
    exact MeasurableSet.iInter
      (fun k => filt_meas_X hmeas m k (by have := k.2; omega) MeasurableSet.of_discrete)
  unfold incr
  refine Measurable.ite hset ?_ measurable_const
  exact ((Measurable.of_discrete (f := G)).comp (filt_meas_X hmeas m (j + 1) hjm)).sub
    ((Measurable.of_discrete (f := G)).comp (filt_meas_X hmeas m j (by omega)))

lemma Yp_meas (hmeas : ∀ n, Measurable (X n)) (G : ℤ → ℝ) (S : Set ℤ) (n : ℕ) :
    Measurable[filt hmeas n] (Yp X G S n) := by
  have : Yp X G S n = fun ω => ∑ j ∈ Finset.range n, incr X G S j ω := rfl
  rw [this]
  exact Finset.measurable_sum _
    (fun j hj => incr_meas hmeas G S j n (by simp only [Finset.mem_range] at hj; omega))

lemma incr_integrable [IsProbabilityMeasure P] (hX : IsChainInEnv P a 0 X) (G : ℤ → ℝ)
    (S : Set ℤ) (j : ℕ) : Integrable (incr X G S j) P := by
  have hm : Measurable (incr X G S j) :=
    (incr_meas hX.2.1 G S j (j + 1) le_rfl).mono ((filt hX.2.1).le _) le_rfl
  refine Integrable.of_bound hm.aestronglyMeasurable
    (2 * ∑ z ∈ Finset.Icc (-((j : ℤ) + 1)) ((j : ℤ) + 1), |G z|) ?_
  filter_upwards [ae_good hX] with ω ⟨h0, hs⟩
  have hb : ∀ i ≤ j + 1, |G (X i ω)| ≤ ∑ z ∈ Finset.Icc (-((j : ℤ) + 1)) ((j : ℤ) + 1), |G z| := by
    intro i hi
    have := abs_le_of_good h0 hs i
    rw [abs_le] at this
    exact Finset.single_le_sum (f := fun z => |G z|) (fun z _ => abs_nonneg _)
      (by simp only [Finset.mem_Icc]; omega)
  unfold incr
  split_ifs
  · rw [Real.norm_eq_abs]
    calc |G (X (j + 1) ω) - G (X j ω)| ≤ |G (X (j + 1) ω)| + |G (X j ω)| := abs_sub _ _
      _ ≤ _ := by linarith [hb (j + 1) le_rfl, hb j (by omega)]
  · rw [norm_zero]
    have : 0 ≤ ∑ z ∈ Finset.Icc (-((j : ℤ) + 1)) ((j : ℤ) + 1), |G z| :=
      Finset.sum_nonneg (fun z _ => abs_nonneg _)
    linarith

lemma step_nonneg (hX : IsChainInEnv P a 0 X) (u v : ℤ) : 0 ≤ step a u v := by
  have := hX.1 u
  unfold step
  split_ifs
  · exact this.1
  · linarith [this.2]
  · exact le_rfl

lemma cyl_succ_meas (hX : IsChainInEnv P a 0 X) (j : ℕ) (x : ℕ → ℤ) (y : ℤ) :
    P (cyl X j x ∩ {ω | X (j + 1) ω = y}) = ENNReal.ofReal (((if x 0 = 0 then 1 else 0) *
      ∏ k ∈ Finset.range j, step a (x k) (x (k + 1))) * step a (x j) y) := by
  have hset : cyl X j x ∩ {ω | X (j + 1) ω = y} =
      {ω | ∀ k ≤ j + 1, X k ω = Function.update x (j + 1) y k} := by
    ext ω
    simp only [cyl, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_or_ge k (j + 1) with hk' | hk'
      · rw [Function.update_of_ne (by omega)]; exact h1 k (by omega)
      · have : k = j + 1 := by omega
        subst this; simp [h2]
    · intro h
      refine ⟨fun k hk => ?_, ?_⟩
      · have := h k (by omega); rwa [Function.update_of_ne (by omega)] at this
      · have := h (j + 1) le_rfl; simpa using this
  rw [hset, hX.2.2 (j + 1), Finset.prod_range_succ]
  have e0 : Function.update x (j + 1) y 0 = x 0 := Function.update_of_ne (by omega) _ _
  have ej : Function.update x (j + 1) y j = x j := Function.update_of_ne (by omega) _ _
  have ej1 : Function.update x (j + 1) y (j + 1) = y := by simp
  have hp : ∏ k ∈ Finset.range j, step a (Function.update x (j + 1) y k)
      (Function.update x (j + 1) y (k + 1)) = ∏ k ∈ Finset.range j, step a (x k) (x (k + 1)) := by
    refine Finset.prod_congr rfl (fun k hk => ?_)
    simp only [Finset.mem_range] at hk
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  rw [e0, ej, ej1, hp, mul_assoc]

lemma cyl_meas (hX : IsChainInEnv P a 0 X) (j : ℕ) (x : ℕ → ℤ) : MeasurableSet (cyl X j x) := by
  have : cyl X j x = ⋂ k : Fin (j + 1), X k ⁻¹' {x k} := by
    ext ω
    simp only [cyl, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h k => h k (Nat.lt_succ_iff.1 k.2), fun h k hk => h ⟨k, by omega⟩⟩
  rw [this]
  exact MeasurableSet.iInter (fun k => hX.2.1 k MeasurableSet.of_discrete)

open scoped Classical in
lemma setIntegral_incr_cyl [IsProbabilityMeasure P] (hX : IsChainInEnv P a 0 X) (G : ℤ → ℝ)
    (hG : ∀ z, a z * G (z + 1) + (1 - a z) * G (z - 1) = G z) (S : Set ℤ) (j : ℕ)
    (x : ℕ → ℤ) : ∫ ω in cyl X j x, incr X G S j ω ∂P = 0 := by
  have hcylm := cyl_meas hX j x
  have hEp : MeasurableSet (cyl X j x ∩ {ω | X (j + 1) ω = x j + 1}) :=
    hcylm.inter (hX.2.1 (j + 1) (MeasurableSet.of_discrete (s := {x j + 1})))
  have hEm : MeasurableSet (cyl X j x ∩ {ω | X (j + 1) ω = x j - 1}) :=
    hcylm.inter (hX.2.1 (j + 1) (MeasurableSet.of_discrete (s := {x j - 1})))
  have hae : cyl X j x =ᵐ[P] ((cyl X j x ∩ {ω | X (j + 1) ω = x j + 1}) ∪
      (cyl X j x ∩ {ω | X (j + 1) ω = x j - 1}) : Set Ω) := by
    rw [eventuallyEq_set]
    filter_upwards [ae_step hX j] with ω hω
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro hc
      have : X j ω = x j := hc j le_rfl
      rw [this] at hω
      rcases hω with h | h
      · exact Or.inl ⟨hc, h⟩
      · exact Or.inr ⟨hc, h⟩
    · rintro (⟨hc, _⟩ | ⟨hc, _⟩) <;> exact hc
  have hdisj : Disjoint (cyl X j x ∩ {ω | X (j + 1) ω = x j + 1})
      (cyl X j x ∩ {ω | X (j + 1) ω = x j - 1}) := by
    rw [Set.disjoint_left]
    rintro ω ⟨_, h1⟩ ⟨_, h2⟩
    simp only [Set.mem_ofPred_eq] at h1 h2
    rw [h1] at h2; omega
  have hint := incr_integrable hX G S j
  rw [setIntegral_congr_set hae, setIntegral_union hdisj hEm hint.integrableOn
    hint.integrableOn]
  have hcond : ∀ ω ∈ cyl X j x, ((∀ k ≤ j, X k ω ∈ S) ↔ (∀ k ≤ j, x k ∈ S)) := by
    intro ω hc
    constructor
    · intro h k hk; rw [← hc k hk]; exact h k hk
    · intro h k hk; rw [hc k hk]; exact h k hk
  have hval : ∀ y : ℤ, ∀ ω ∈ cyl X j x ∩ {ω | X (j + 1) ω = y},
      incr X G S j ω = (if ∀ k ≤ j, x k ∈ S then G y - G (x j) else 0) := by
    intro y ω hω
    obtain ⟨hc, h1⟩ := hω
    simp only [Set.mem_ofPred_eq] at h1
    have hc' := hcond ω hc
    unfold incr
    rw [h1, hc j le_rfl]
    by_cases h : ∀ k ≤ j, x k ∈ S
    · rw [if_pos (hc'.2 h), if_pos h]
    · rw [if_neg (fun h' => h (hc'.1 h')), if_neg h]
  rw [setIntegral_congr_fun hEp (hval (x j + 1)), setIntegral_congr_fun hEm (hval (x j - 1)),
    setIntegral_const, setIntegral_const, measureReal_def, measureReal_def,
    cyl_succ_meas hX, cyl_succ_meas hX]
  have hw : 0 ≤ (if x 0 = 0 then (1 : ℝ) else 0) * ∏ k ∈ Finset.range j, step a (x k) (x (k + 1)) :=
    mul_nonneg (by split_ifs <;> norm_num) (Finset.prod_nonneg (fun k _ => step_nonneg hX _ _))
  set w := (if x 0 = 0 then (1 : ℝ) else 0) * ∏ k ∈ Finset.range j, step a (x k) (x (k + 1))
  have s1 : step a (x j) (x j + 1) = a (x j) := by simp [step]
  have s2 : step a (x j) (x j - 1) = 1 - a (x j) := by
    unfold step; rw [if_neg (by omega), if_pos rfl]
  rw [s1, s2, ENNReal.toReal_ofReal (mul_nonneg hw (hX.1 _).1),
    ENNReal.toReal_ofReal (mul_nonneg hw (by linarith [(hX.1 (x j)).2]))]
  by_cases h : ∀ k ≤ j, x k ∈ S
  · rw [if_pos h, if_pos h, smul_eq_mul, smul_eq_mul]
    linear_combination w * hG (x j)
  · rw [if_neg h, if_neg h]; simp

lemma setIntegral_incr_eq_zero [IsProbabilityMeasure P] (hX : IsChainInEnv P a 0 X)
    (G : ℤ → ℝ) (hG : ∀ z, a z * G (z + 1) + (1 - a z) * G (z - 1) = G z) (S : Set ℤ) (j : ℕ)
    (s : Set Ω) (hs : MeasurableSet[filt hX.2.1 j] s) : ∫ ω in s, incr X G S j ω ∂P = 0 := by
  obtain ⟨B, -, rfl⟩ := MeasurableSpace.measurableSet_comap.1 hs
  have hU : Φ X j ⁻¹' B = ⋃ u : Fin (j + 1) → ℤ, (Φ X j ⁻¹' {u} ∩ Φ X j ⁻¹' B) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_singleton_iff]
    exact ⟨fun h => ⟨_, rfl, h⟩, fun ⟨_, _, h⟩ => h⟩
  have hmeasΦ : Measurable (Φ X j) := measurable_pi_iff.2 (fun i => hX.2.1 i)
  have hdisj : Pairwise (Function.onFun Disjoint fun u : Fin (j + 1) → ℤ => Φ X j ⁻¹' {u} ∩ Φ X j ⁻¹' B) := by
    intro u v huv
    refine Disjoint.mono Set.inter_subset_left Set.inter_subset_left ?_
    rw [Set.disjoint_left]
    intro ω h1 h2
    have e1 : Φ X j ω = u := h1
    have e2 : Φ X j ω = v := h2
    exact huv (e1.symm.trans e2)
  rw [hU, integral_iUnion (fun u => (hmeasΦ MeasurableSet.of_discrete).inter
    (hmeasΦ MeasurableSet.of_discrete)) hdisj (incr_integrable hX G S j).integrableOn]
  refine (tsum_congr fun u => ?_).trans tsum_zero
  by_cases hu : u ∈ B
  · have h1 : Φ X j ⁻¹' {u} ∩ Φ X j ⁻¹' B = cyl X j (trunc j u) := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, cyl,
        Set.mem_ofPred_eq]
      constructor
      · rintro ⟨h, -⟩ k hk
        rw [trunc_of_lt _ (by omega), ← h]
        rfl
      · intro h
        have hu' : Φ X j ω = u := by
          funext i
          have := h i (Nat.lt_succ_iff.1 i.2)
          rw [trunc_of_lt _ i.2] at this
          exact this
        exact ⟨hu', hu' ▸ hu⟩
    rw [h1]
    exact setIntegral_incr_cyl hX G hG S j _
  · have h1 : Φ X j ⁻¹' {u} ∩ Φ X j ⁻¹' B = ∅ := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, iff_false, not_and]
      intro h; rw [h]; exact hu
    rw [h1]; simp

lemma Yp_integrable [IsProbabilityMeasure P] (hX : IsChainInEnv P a 0 X) (G : ℤ → ℝ)
    (S : Set ℤ) (n : ℕ) : Integrable (Yp X G S n) P := by
  have : Yp X G S n = fun ω => ∑ j ∈ Finset.range n, incr X G S j ω := rfl
  rw [this]
  exact integrable_finsetSum _ (fun j _ => incr_integrable hX G S j)

lemma Yp_submart [IsProbabilityMeasure P] (hX : IsChainInEnv P a 0 X) (G : ℤ → ℝ)
    (hG : ∀ z, a z * G (z + 1) + (1 - a z) * G (z - 1) = G z) (S : Set ℤ) :
    Submartingale (Yp X G S) (filt hX.2.1) P := by
  refine submartingale_of_setIntegral_le_succ ?_ (fun n => Yp_integrable hX G S n) ?_
  · intro n; exact (Yp_meas hX.2.1 G S n).stronglyMeasurable
  · intro n s hs
    have : Yp X G S (n + 1) = fun ω => Yp X G S n ω + incr X G S n ω := by
      funext ω; exact Yp_succ G S n ω
    rw [this, integral_add (Yp_integrable hX G S n).integrableOn
      (incr_integrable hX G S n).integrableOn, setIntegral_incr_eq_zero hX G hG S n s hs,
      add_zero]

lemma Yp_integral [IsProbabilityMeasure P] (hX : IsChainInEnv P a 0 X) (G : ℤ → ℝ)
    (hG : ∀ z, a z * G (z + 1) + (1 - a z) * G (z - 1) = G z) (S : Set ℤ) (n : ℕ) :
    ∫ ω, Yp X G S n ω ∂P = 0 := by
  have : Yp X G S n = fun ω => ∑ j ∈ Finset.range n, incr X G S j ω := rfl
  rw [this, integral_finsetSum _ (fun j _ => incr_integrable hX G S j)]
  apply Finset.sum_eq_zero
  intro j _
  have := setIntegral_incr_eq_zero hX G hG S j Set.univ MeasurableSet.univ
  simpa using this

lemma Yp_conv [IsProbabilityMeasure P] (hX : IsChainInEnv P a 0 X) (G : ℤ → ℝ)
    (hG : ∀ z, a z * G (z + 1) + (1 - a z) * G (z - 1) = G z) (S : Set ℤ) (c : ℝ)
    (hc : ∀ n, ∀ᵐ ω ∂P, c ≤ Yp X G S n ω) :
    ∀ᵐ ω ∂P, ∃ L, Tendsto (fun n => Yp X G S n ω) atTop (𝓝 L) := by
  refine (Yp_submart hX G hG S).exists_ae_tendsto_of_bdd (R := Real.toNNReal (2 * |c|)) ?_
  intro n
  have hi := Yp_integrable hX G S n
  rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm hi]
  show ENNReal.ofReal _ ≤ ENNReal.ofReal (2 * |c|)
  apply ENNReal.ofReal_le_ofReal
  have h1 : ∫ ω, ‖Yp X G S n ω‖ ∂P ≤ ∫ ω, (Yp X G S n ω - c + |c|) ∂P := by
    apply integral_mono_ae hi.norm ((hi.sub (integrable_const c)).add (integrable_const |c|))
    filter_upwards [hc n] with ω hω
    show ‖Yp X G S n ω‖ ≤ Yp X G S n ω - c + |c|
    rw [Real.norm_eq_abs]
    rcases le_or_gt 0 (Yp X G S n ω) with h | h
    · rw [abs_of_nonneg h]; linarith [le_abs_self c]
    · rw [abs_of_neg h]; linarith [neg_abs_le c]
  have hi2 : Integrable (fun ω => Yp X G S n ω - c) P := hi.sub (integrable_const c)
  have h2 : ∫ ω, (Yp X G S n ω - c + |c|) ∂P = -c + |c| := by
    rw [integral_add hi2 (integrable_const _),
      integral_sub hi (integrable_const c), Yp_integral hX G hG S n]
    simp
  linarith [le_abs_self c, neg_abs_le c]

lemma Yp_all (G : ℤ → ℝ) (S : Set ℤ) (ω : Ω) :
    ∀ n, (∀ k < n, X k ω ∈ S) → Yp X G S n ω = G (X n ω) - G (X 0 ω) := by
  intro n
  induction n with
  | zero => intro _; simp [Yp]
  | succ m ih =>
    intro h
    rw [Yp_succ, ih (fun k hk => h k (by omega))]
    unfold incr
    rw [if_pos (fun k hk => h k (by omega))]
    ring

lemma Yp_repr (G : ℤ → ℝ) (S : Set ℤ) (ω : Ω) :
    ∀ n, ∃ j ≤ n, Yp X G S n ω = G (X j ω) - G (X 0 ω) ∧ ∀ k < j, X k ω ∈ S := by
  intro n
  induction n with
  | zero => exact ⟨0, le_rfl, by simp [Yp], fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | succ m ih =>
    by_cases h : ∀ k ≤ m, X k ω ∈ S
    · exact ⟨m + 1, le_rfl, Yp_all G S ω (m + 1) (fun k hk => h k (by omega)),
        fun k hk => h k (by omega)⟩
    · obtain ⟨j, hj, h1, h2⟩ := ih
      refine ⟨j, by omega, ?_, h2⟩
      rw [Yp_succ, h1]
      unfold incr
      rw [if_neg h, add_zero]

end Prob

end RWRE15

/-! ## Part D: Solomon (1975), Lemma (1.5) -/

open MeasureTheory ProbabilityTheory Filter Topology ENNReal SolomonRWRE.Recurrence in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (a : ℤ → ℝ) (ha : ∀ n, 0 < a n ∧ a n < 1)
    (X : ℕ → Ω → ℤ) (hX : IsChainInEnv P a 0 X) :
    (∑' n : ℕ, (rho a (-((n : ℤ) + 1)))⁻¹ = ∞ → ∑' n : ℕ, rho a ((n : ℤ) + 1) ≠ ∞ →
        ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop atTop) ∧
    (∑' n : ℕ, (rho a (-((n : ℤ) + 1)))⁻¹ ≠ ∞ → ∑' n : ℕ, rho a ((n : ℤ) + 1) = ∞ →
        ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop atBot) ∧
    (∑' n : ℕ, (rho a (-((n : ℤ) + 1)))⁻¹ = ∞ → ∑' n : ℕ, rho a ((n : ℤ) + 1) = ∞ →
        ∀ᵐ ω ∂P, Oscillates (fun n => X n ω)) := by
  have hmono := RWRE15.g_strictMono ha
  have hharm := RWRE15.g_harm ha
  have hharmneg : ∀ z, a z * (-RWRE15.g a (z + 1)) + (1 - a z) * (-RWRE15.g a (z - 1)) =
      -RWRE15.g a z := by
    intro z; have := hharm z; linarith
  have hgood := RWRE15.ae_good hX
  refine ⟨?_, ?_, ?_⟩
  · intro h1 h2
    have hns : ¬ Summable (RWRE15.dn a) := (RWRE15.series_neg_iff ha).1 h1
    have hs : Summable (RWRE15.up a) := by
      by_contra hc; exact h2 ((RWRE15.series_pos_iff ha).2 hc)
    have hbd : ∀ n, ∀ᵐ ω ∂P, -(∑' n, RWRE15.up a n) + RWRE15.g a 0 ≤
        RWRE15.Yp X (fun z => -RWRE15.g a z) Set.univ n ω := by
      intro n
      filter_upwards [hgood] with ω ⟨h0, _⟩
      rw [RWRE15.Yp_all _ _ ω n (fun _ _ => Set.mem_univ _), h0]
      linarith [RWRE15.g_le_tsum ha hs (X n ω)]
    filter_upwards [hgood, RWRE15.Yp_conv hX _ hharmneg Set.univ _ hbd] with ω ⟨h0, hst⟩ ⟨L, hL⟩
    have hL' : Tendsto (fun n => RWRE15.g a (X n ω)) atTop (𝓝 (RWRE15.g a 0 - L)) := by
      have : (fun n => RWRE15.g a (X n ω)) = fun n => RWRE15.g a 0 -
          RWRE15.Yp X (fun z => -RWRE15.g a z) Set.univ n ω := by
        funext n; rw [RWRE15.Yp_all _ _ ω n (fun _ _ => Set.mem_univ _), h0]; ring
      rw [this]; exact tendsto_const_nhds.sub hL
    rcases RWRE15.det_tendsto (fun n => X n ω) hst _ hmono _ hL' with ht | hb
    · exact ht
    · exact (RWRE15.not_bot_of_unbdd _ _ hmono _ hL' (RWRE15.g_unbdd_below ha hns) hb).elim
  · intro h1 h2
    have hns : ¬ Summable (RWRE15.up a) := (RWRE15.series_pos_iff ha).1 h2
    have hs : Summable (RWRE15.dn a) := by
      by_contra hc; exact h1 ((RWRE15.series_neg_iff ha).2 hc)
    have hbd : ∀ n, ∀ᵐ ω ∂P, -(∑' n, RWRE15.dn a n) - RWRE15.g a 0 ≤
        RWRE15.Yp X (RWRE15.g a) Set.univ n ω := by
      intro n
      filter_upwards [hgood] with ω ⟨h0, _⟩
      rw [RWRE15.Yp_all _ _ ω n (fun _ _ => Set.mem_univ _), h0]
      linarith [RWRE15.neg_tsum_le_g ha hs (X n ω)]
    filter_upwards [hgood, RWRE15.Yp_conv hX _ hharm Set.univ _ hbd] with ω ⟨h0, hst⟩ ⟨L, hL⟩
    have hL' : Tendsto (fun n => RWRE15.g a (X n ω)) atTop (𝓝 (L + RWRE15.g a 0)) := by
      have : (fun n => RWRE15.g a (X n ω)) = fun n =>
          RWRE15.Yp X (RWRE15.g a) Set.univ n ω + RWRE15.g a 0 := by
        funext n; rw [RWRE15.Yp_all _ _ ω n (fun _ _ => Set.mem_univ _), h0]; ring
      rw [this]; exact hL.add tendsto_const_nhds
    rcases RWRE15.det_tendsto (fun n => X n ω) hst _ hmono _ hL' with ht | hb
    · exact (RWRE15.not_top_of_unbdd _ _ hmono _ hL' (RWRE15.g_unbdd_above ha hns) ht).elim
    · exact hb
  · intro h1 h2
    have hns1 : ¬ Summable (RWRE15.dn a) := (RWRE15.series_neg_iff ha).1 h1
    have hns2 : ¬ Summable (RWRE15.up a) := (RWRE15.series_pos_iff ha).1 h2
    have hlow : ∀ M : ℕ, ∀ᵐ ω ∂P, ∃ n, X n ω ≤ -(M : ℤ) := by
      intro M
      have hbd : ∀ n, ∀ᵐ ω ∂P, RWRE15.g a (-(M : ℤ)) - RWRE15.g a 0 ≤
          RWRE15.Yp X (RWRE15.g a) (Set.Ioi (-(M : ℤ))) n ω := by
        intro n
        filter_upwards [hgood] with ω ⟨h0, hst⟩
        obtain ⟨j, -, hj, hk⟩ := RWRE15.Yp_repr (RWRE15.g a) (Set.Ioi (-(M : ℤ))) ω n
        rw [hj, h0]
        have hXj : -(M : ℤ) ≤ X j ω := by
          rcases j with _ | i
          · rw [h0]; omega
          · have := hk i (by omega)
            simp only [Set.mem_Ioi] at this
            rcases hst i with h | h <;> omega
        linarith [hmono.monotone hXj]
      filter_upwards [hgood, RWRE15.Yp_conv hX _ hharm _ _ hbd] with ω ⟨h0, hst⟩ ⟨L, hL⟩
      by_contra hne
      push_neg at hne
      have hall : ∀ n, X n ω ∈ Set.Ioi (-(M : ℤ)) := fun n => hne n
      have hL' : Tendsto (fun n => RWRE15.g a (X n ω)) atTop (𝓝 (L + RWRE15.g a 0)) := by
        have : (fun n => RWRE15.g a (X n ω)) = fun n =>
            RWRE15.Yp X (RWRE15.g a) (Set.Ioi (-(M : ℤ))) n ω + RWRE15.g a 0 := by
          funext n; rw [RWRE15.Yp_all _ _ ω n (fun k _ => hall k), h0]; ring
        rw [this]; exact hL.add tendsto_const_nhds
      rcases RWRE15.det_tendsto (fun n => X n ω) hst _ hmono _ hL' with ht | hb
      · exact RWRE15.not_top_of_unbdd _ _ hmono _ hL' (RWRE15.g_unbdd_above ha hns2) ht
      · obtain ⟨n, hn⟩ := (tendsto_atBot.1 hb (-(M : ℤ))).exists
        exact absurd (hne n) (not_lt.2 hn)
    have hup : ∀ M : ℕ, ∀ᵐ ω ∂P, ∃ n, (M : ℤ) ≤ X n ω := by
      intro M
      have hbd : ∀ n, ∀ᵐ ω ∂P, -RWRE15.g a (M : ℤ) + RWRE15.g a 0 ≤
          RWRE15.Yp X (fun z => -RWRE15.g a z) (Set.Iio (M : ℤ)) n ω := by
        intro n
        filter_upwards [hgood] with ω ⟨h0, hst⟩
        obtain ⟨j, -, hj, hk⟩ :=
          RWRE15.Yp_repr (fun z => -RWRE15.g a z) (Set.Iio (M : ℤ)) ω n
        rw [hj, h0]
        have hXj : X j ω ≤ (M : ℤ) := by
          rcases j with _ | i
          · rw [h0]; omega
          · have := hk i (by omega)
            simp only [Set.mem_Iio] at this
            rcases hst i with h | h <;> omega
        linarith [hmono.monotone hXj]
      filter_upwards [hgood, RWRE15.Yp_conv hX _ hharmneg _ _ hbd] with ω ⟨h0, hst⟩ ⟨L, hL⟩
      by_contra hne
      push_neg at hne
      have hall : ∀ n, X n ω ∈ Set.Iio (M : ℤ) := fun n => hne n
      have hL' : Tendsto (fun n => RWRE15.g a (X n ω)) atTop (𝓝 (RWRE15.g a 0 - L)) := by
        have : (fun n => RWRE15.g a (X n ω)) = fun n => RWRE15.g a 0 -
            RWRE15.Yp X (fun z => -RWRE15.g a z) (Set.Iio (M : ℤ)) n ω := by
          funext n; rw [RWRE15.Yp_all _ _ ω n (fun k _ => hall k), h0]; ring
        rw [this]; exact tendsto_const_nhds.sub hL
      rcases RWRE15.det_tendsto (fun n => X n ω) hst _ hmono _ hL' with ht | hb
      · obtain ⟨n, hn⟩ := (tendsto_atTop.1 ht (M : ℤ)).exists
        exact absurd (hne n) (not_lt.2 hn)
      · exact RWRE15.not_bot_of_unbdd _ _ hmono _ hL' (RWRE15.g_unbdd_below ha hns1) hb
    filter_upwards [hgood, ae_all_iff.2 hlow, ae_all_iff.2 hup] with ω ⟨h0, hst⟩ hl hu
    have hab := RWRE15.abs_le_of_good h0 hst
    unfold Oscillates
    refine ⟨fun M => ?_, fun M => ?_⟩
    · rw [frequently_atTop]
      intro N
      obtain ⟨n, hn⟩ := hl (N + (-M).toNat)
      have h3 := hab n
      have h4 := Int.self_le_toNat (-M)
      rw [abs_le] at h3
      push_cast at hn
      exact ⟨n, by omega, by show X n ω ≤ M; omega⟩
    · rw [frequently_atTop]
      intro N
      obtain ⟨n, hn⟩ := hu (N + M.toNat)
      have h3 := hab n
      have h4 := Int.self_le_toNat M
      rw [abs_le] at h3
      push_cast at hn
      exact ⟨n, by omega, by show M ≤ X n ω; omega⟩
