-- Prove2me | solution 1 for Viterbo.isLeast_polygonLength_pentagon_and_diagonal_isClosedBilliard
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:10:34.908154+00:00
-- url     : https://prove2.me/submissions/f72a0dd2-0b2b-4511-9ab0-40b7899f666d

import Definitions.Def_Viterbo
import Definitions.Def_SymmetricPolar
import Mathlib

section
section
/-!
# Viterbo pentagon, Part A: support function of `T`, convex domains, the diagonal billiards,
and the witness of the minimum.
-/

set_option linter.unusedSimpArgs false

namespace Viterbo.PentA

open Viterbo OAI.SymmetricPolar Set Real

/-! ## Constants -/

/-- `c = cos (π/5)`. -/
noncomputable def cc : ℝ := Real.cos (π / 5)
/-- `S = sin (π/5)`. -/
noncomputable def ss : ℝ := Real.sin (π / 5)

lemma cc_sq : cc ^ 2 = (2 * cc + 1) / 4 := by
  have h := Real.cos_pi_div_five
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  simp only [cc]; rw [h]; nlinarith [h5]

lemma ss_sq : ss ^ 2 = (3 - 2 * cc) / 4 := by
  have := Real.sin_sq_add_cos_sq (π / 5)
  have := cc_sq
  simp only [ss, cc] at *; linarith

lemma ss_pos : 0 < ss := by
  unfold ss
  apply Real.sin_pos_of_pos_of_lt_pi
  · positivity
  · linarith [Real.pi_pos]

lemma cc_bounds : 0.809 < cc ∧ cc < 0.80903 := by
  have h := Real.cos_pi_div_five
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  simp only [cc]; rw [h]
  constructor <;> nlinarith

lemma ss_bounds : 0.5877 < ss ∧ ss < 0.5879 := by
  have := ss_sq; have := cc_bounds; have := ss_pos
  constructor <;> nlinarith

lemma ccss_bounds : 0.4754 < cc * ss ∧ cc * ss < 0.4757 := by
  have := ss_bounds; have := cc_bounds
  constructor <;> nlinarith

/-- Monomial reductions, for `linarith`. -/
lemma cc3 : cc ^ 3 = (4 * cc + 1) / 8 := by linear_combination (cc + 1/2) * cc_sq
lemma cc4 : cc ^ 4 = (3 * cc + 1) / 8 := by linear_combination (cc ^ 2 + cc / 2 + 1 / 2) * cc_sq
lemma ss3 : ss ^ 3 = (3 - 2 * cc) / 4 * ss := by linear_combination ss * ss_sq
lemma ss4 : ss ^ 4 = (3 - 2 * cc) ^ 2 / 16 := by linear_combination (ss ^ 2 + (3 - 2 * cc) / 4) * ss_sq
lemma ccss2 : cc * ss ^ 2 = (3 * cc - (2 * cc + 1) / 2) / 4 := by
  linear_combination cc * ss_sq - (1 / 2) * cc_sq
lemma cc2ss : cc ^ 2 * ss = (2 * cc + 1) / 4 * ss := by have := cc_sq; rw [this]
lemma cc2ss2 : cc ^ 2 * ss ^ 2 = (2 * cc + 1) / 4 * ((3 - 2 * cc) / 4) := by
  rw [cc_sq, ss_sq]
lemma cc3ss : cc ^ 3 * ss = (4 * cc + 1) / 8 * ss := by rw [cc3]
lemma ccss3 : cc * ss ^ 3 = cc * ss * ((3 - 2 * cc) / 4) := by rw [ss3]; ring

/-! ## Trig values -/

lemma cos2 : Real.cos (2 * π / 5) = cc - 1 / 2 := by
  rw [show 2 * π / 5 = 2 * (π / 5) by ring, Real.cos_two_mul]; have := cc_sq; simp only [cc] at *
  linarith
lemma sin2 : Real.sin (2 * π / 5) = 2 * ss * cc := by
  rw [show 2 * π / 5 = 2 * (π / 5) by ring, Real.sin_two_mul]; rfl
lemma cos4 : Real.cos (4 * π / 5) = -cc := by
  rw [show 4 * π / 5 = π - π / 5 by ring, Real.cos_pi_sub]; rfl
lemma sin4 : Real.sin (4 * π / 5) = ss := by
  rw [show 4 * π / 5 = π - π / 5 by ring, Real.sin_pi_sub]; rfl
lemma cos6 : Real.cos (6 * π / 5) = -cc := by
  rw [show 6 * π / 5 = π / 5 + π by ring, Real.cos_add_pi]; rfl
lemma sin6 : Real.sin (6 * π / 5) = -ss := by
  rw [show 6 * π / 5 = π / 5 + π by ring, Real.sin_add_pi]; rfl
lemma cos8 : Real.cos (8 * π / 5) = cc - 1 / 2 := by
  rw [show 8 * π / 5 = -(2 * π / 5) + 2 * π by ring, Real.cos_add_two_pi, Real.cos_neg, cos2]
lemma sin8 : Real.sin (8 * π / 5) = -(2 * ss * cc) := by
  rw [show 8 * π / 5 = -(2 * π / 5) + 2 * π by ring, Real.sin_add_two_pi, Real.sin_neg, sin2]

/-! ## Coordinates -/

lemma inner2 (x y : Position 2) : inner ℝ x y = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]; ring

lemma pv_eq (k : ℕ) : pentagonVertex k = !₂[Real.cos (2 * π * k / 5), Real.sin (2 * π * k / 5)] := rfl
lemma rv_eq (k : ℕ) : rotatedVertex k = !₂[Real.sin (2 * π * k / 5), -Real.cos (2 * π * k / 5)] := by
  unfold rotatedVertex
  rw [show -(π / 2) + 2 * π * k / 5 = 2 * π * k / 5 - π / 2 by ring, Real.cos_sub_pi_div_two,
    Real.sin_sub_pi_div_two]

/-! ## Values at `2πk/5` -/

lemma C0 : Real.cos (2 * π * ((0:ℕ):ℝ) / 5) = 1 := by
  simp
lemma S0 : Real.sin (2 * π * ((0:ℕ):ℝ) / 5) = 0 := by
  simp
lemma C1 : Real.cos (2 * π * ((1:ℕ):ℝ) / 5) = cc - 1 / 2 := by
  rw [show 2 * π * ((1:ℕ):ℝ) / 5 = 2 * π / 5 by push_cast; ring, cos2]
lemma S1 : Real.sin (2 * π * ((1:ℕ):ℝ) / 5) = 2 * ss * cc := by
  rw [show 2 * π * ((1:ℕ):ℝ) / 5 = 2 * π / 5 by push_cast; ring, sin2]
lemma C2 : Real.cos (2 * π * ((2:ℕ):ℝ) / 5) = -cc := by
  rw [show 2 * π * ((2:ℕ):ℝ) / 5 = 4 * π / 5 by push_cast; ring, cos4]
lemma S2 : Real.sin (2 * π * ((2:ℕ):ℝ) / 5) = ss := by
  rw [show 2 * π * ((2:ℕ):ℝ) / 5 = 4 * π / 5 by push_cast; ring, sin4]
lemma C3 : Real.cos (2 * π * ((3:ℕ):ℝ) / 5) = -cc := by
  rw [show 2 * π * ((3:ℕ):ℝ) / 5 = 6 * π / 5 by push_cast; ring, cos6]
lemma S3 : Real.sin (2 * π * ((3:ℕ):ℝ) / 5) = -ss := by
  rw [show 2 * π * ((3:ℕ):ℝ) / 5 = 6 * π / 5 by push_cast; ring, sin6]
lemma C4 : Real.cos (2 * π * ((4:ℕ):ℝ) / 5) = cc - 1 / 2 := by
  rw [show 2 * π * ((4:ℕ):ℝ) / 5 = 8 * π / 5 by push_cast; ring, cos8]
lemma S4 : Real.sin (2 * π * ((4:ℕ):ℝ) / 5) = -(2 * ss * cc) := by
  rw [show 2 * π * ((4:ℕ):ℝ) / 5 = 8 * π / 5 by push_cast; ring, sin8]
lemma C5 : Real.cos (2 * π * ((5:ℕ):ℝ) / 5) = 1 := by
  rw [show 2 * π * ((5:ℕ):ℝ) / 5 = 2 * π by push_cast; ring]; simp
lemma S5 : Real.sin (2 * π * ((5:ℕ):ℝ) / 5) = 0 := by
  rw [show 2 * π * ((5:ℕ):ℝ) / 5 = 2 * π by push_cast; ring]; simp
lemma C6 : Real.cos (2 * π * ((6:ℕ):ℝ) / 5) = cc - 1 / 2 := by
  rw [show 2 * π * ((6:ℕ):ℝ) / 5 = 2 * π / 5 + 2 * π by push_cast; ring, Real.cos_add_two_pi, cos2]
lemma S6 : Real.sin (2 * π * ((6:ℕ):ℝ) / 5) = 2 * ss * cc := by
  rw [show 2 * π * ((6:ℕ):ℝ) / 5 = 2 * π / 5 + 2 * π by push_cast; ring, Real.sin_add_two_pi, sin2]
lemma C7 : Real.cos (2 * π * ((7:ℕ):ℝ) / 5) = -cc := by
  rw [show 2 * π * ((7:ℕ):ℝ) / 5 = 4 * π / 5 + 2 * π by push_cast; ring, Real.cos_add_two_pi, cos4]
lemma S7 : Real.sin (2 * π * ((7:ℕ):ℝ) / 5) = ss := by
  rw [show 2 * π * ((7:ℕ):ℝ) / 5 = 4 * π / 5 + 2 * π by push_cast; ring, Real.sin_add_two_pi, sin4]
lemma C8 : Real.cos (2 * π * ((8:ℕ):ℝ) / 5) = -cc := by
  rw [show 2 * π * ((8:ℕ):ℝ) / 5 = 6 * π / 5 + 2 * π by push_cast; ring, Real.cos_add_two_pi, cos6]
lemma S8 : Real.sin (2 * π * ((8:ℕ):ℝ) / 5) = -ss := by
  rw [show 2 * π * ((8:ℕ):ℝ) / 5 = 6 * π / 5 + 2 * π by push_cast; ring, Real.sin_add_two_pi, sin6]

lemma pv0 (k : ℕ) : pentagonVertex k 0 = Real.cos (2 * π * k / 5) := rfl
lemma pv1 (k : ℕ) : pentagonVertex k 1 = Real.sin (2 * π * k / 5) := rfl
lemma rv0 (k : ℕ) : rotatedVertex k 0 = Real.sin (2 * π * k / 5) := by rw [rv_eq]; rfl
lemma rv1 (k : ℕ) : rotatedVertex k 1 = -Real.cos (2 * π * k / 5) := by rw [rv_eq]; rfl


/-! ## Vertex coordinates -/

lemma pv_0_0 : pentagonVertex 0 0 = 1 := by rw [pv0, C0]
lemma pv_0_1 : pentagonVertex 0 1 = 0 := by rw [pv1, S0]
lemma rv_0_0 : rotatedVertex 0 0 = 0 := by rw [rv0, S0]
lemma rv_0_1 : rotatedVertex 0 1 = -(1) := by rw [rv1, C0]
lemma pv_1_0 : pentagonVertex 1 0 = cc - 1 / 2 := by rw [pv0, C1]
lemma pv_1_1 : pentagonVertex 1 1 = 2 * ss * cc := by rw [pv1, S1]
lemma rv_1_0 : rotatedVertex 1 0 = 2 * ss * cc := by rw [rv0, S1]
lemma rv_1_1 : rotatedVertex 1 1 = -(cc - 1 / 2) := by rw [rv1, C1]
lemma pv_2_0 : pentagonVertex 2 0 = -cc := by rw [pv0, C2]
lemma pv_2_1 : pentagonVertex 2 1 = ss := by rw [pv1, S2]
lemma rv_2_0 : rotatedVertex 2 0 = ss := by rw [rv0, S2]
lemma rv_2_1 : rotatedVertex 2 1 = cc := by rw [rv1, C2, neg_neg]
lemma pv_3_0 : pentagonVertex 3 0 = -cc := by rw [pv0, C3]
lemma pv_3_1 : pentagonVertex 3 1 = -ss := by rw [pv1, S3]
lemma rv_3_0 : rotatedVertex 3 0 = -ss := by rw [rv0, S3]
lemma rv_3_1 : rotatedVertex 3 1 = cc := by rw [rv1, C3, neg_neg]
lemma pv_4_0 : pentagonVertex 4 0 = cc - 1 / 2 := by rw [pv0, C4]
lemma pv_4_1 : pentagonVertex 4 1 = -(2 * ss * cc) := by rw [pv1, S4]
lemma rv_4_0 : rotatedVertex 4 0 = -(2 * ss * cc) := by rw [rv0, S4]
lemma rv_4_1 : rotatedVertex 4 1 = -(cc - 1 / 2) := by rw [rv1, C4]
lemma pv_5_0 : pentagonVertex 5 0 = 1 := by rw [pv0, C5]
lemma pv_5_1 : pentagonVertex 5 1 = 0 := by rw [pv1, S5]
lemma rv_5_0 : rotatedVertex 5 0 = 0 := by rw [rv0, S5]
lemma rv_5_1 : rotatedVertex 5 1 = -(1) := by rw [rv1, C5]
lemma pv_6_0 : pentagonVertex 6 0 = cc - 1 / 2 := by rw [pv0, C6]
lemma pv_6_1 : pentagonVertex 6 1 = 2 * ss * cc := by rw [pv1, S6]
lemma rv_6_0 : rotatedVertex 6 0 = 2 * ss * cc := by rw [rv0, S6]
lemma rv_6_1 : rotatedVertex 6 1 = -(cc - 1 / 2) := by rw [rv1, C6]
lemma pv_7_0 : pentagonVertex 7 0 = -cc := by rw [pv0, C7]
lemma pv_7_1 : pentagonVertex 7 1 = ss := by rw [pv1, S7]
lemma rv_7_0 : rotatedVertex 7 0 = ss := by rw [rv0, S7]
lemma rv_7_1 : rotatedVertex 7 1 = cc := by rw [rv1, C7, neg_neg]
lemma pv_8_0 : pentagonVertex 8 0 = -cc := by rw [pv0, C8]
lemma pv_8_1 : pentagonVertex 8 1 = -ss := by rw [pv1, S8]
lemma rv_8_0 : rotatedVertex 8 0 = -ss := by rw [rv0, S8]
lemma rv_8_1 : rotatedVertex 8 1 = cc := by rw [rv1, C8, neg_neg]

/-! ## Hulls of five points -/

lemma mem_hull5 (f : ℕ → Position 2) {k : ℕ} (hk : k < 5) :
    f k ∈ convexHull ℝ (f '' ↑(Finset.range 5)) :=
  subset_convexHull ℝ _ ⟨k, by simpa using hk, rfl⟩

lemma convex_halfplane (u : Position 2) (M : ℝ) : Convex ℝ {y : Position 2 | inner ℝ y u ≤ M} := by
  intro x hx y hy a b ha hb hab
  simp only [mem_ofPred_eq, inner_add_left, inner_smul_left] at *
  simp only [RCLike.conj_to_real]
  have hM : a * M + b * M = M := by rw [← add_mul, hab, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hx ha, mul_le_mul_of_nonneg_left hy hb]

lemma hull_le {f : ℕ → Position 2} {u : Position 2} {M : ℝ} (h : ∀ k < 5, inner ℝ (f k) u ≤ M) :
    ∀ x ∈ convexHull ℝ (f '' ↑(Finset.range 5)), inner ℝ x u ≤ M := by
  intro x hx
  have hsub : convexHull ℝ (f '' ↑(Finset.range 5)) ⊆ {y | inner ℝ y u ≤ M} := by
    apply convexHull_min _ (convex_halfplane u M)
    rintro _ ⟨k, hk, rfl⟩
    exact h k (by simpa using hk)
  exact hsub hx

/-- The support function of `T`, as a maximum over the five vertices. -/
noncomputable def hT (d : Position 2) : ℝ :=
  (Finset.range 5).sup' ⟨0, by simp⟩ (fun k => inner ℝ d (rotatedVertex k))

theorem supportFunction_pentagonT (d : Position 2) : supportFunction pentagonT d = hT d := by
  unfold supportFunction
  apply IsGreatest.csSup_eq
  constructor
  · obtain ⟨k, hk, hkeq⟩ := Finset.exists_mem_eq_sup' (s := Finset.range 5) ⟨0, by simp⟩
      (fun k => inner ℝ d (rotatedVertex k))
    refine ⟨rotatedVertex k, mem_hull5 _ (by simpa using hk), ?_⟩
    simp only [hT, hkeq, real_inner_comm]
  · rintro _ ⟨x, hx, rfl⟩
    refine hull_le (fun k hk => ?_) x hx
    rw [real_inner_comm]
    exact Finset.le_sup' (fun k => inner ℝ d (rotatedVertex k)) (by simpa using hk)

theorem le_supportFunction_pentagonT (d : Position 2) {k : ℕ} (hk : k < 5) :
    inner ℝ d (rotatedVertex k) ≤ supportFunction pentagonT d := by
  rw [supportFunction_pentagonT]
  exact Finset.le_sup' (fun k => inner ℝ d (rotatedVertex k)) (by simpa using hk)

theorem supportFunction_pentagonT_le (d : Position 2) {M : ℝ}
    (h : ∀ k < 5, inner ℝ d (rotatedVertex k) ≤ M) : supportFunction pentagonT d ≤ M := by
  rw [supportFunction_pentagonT]
  exact Finset.sup'_le _ _ (fun k hk => h k (by simpa using hk))

/-! ## Interior, frontier, normal cones -/

lemma inner_lt_of_mem_interior {S : Set (Position 2)} {u y : Position 2} {M : ℝ}
    (hS : ∀ x ∈ S, inner ℝ x u ≤ M) (hu : 0 < inner ℝ u u) (hy : y ∈ interior S) :
    inner ℝ y u < M := by
  have hc : Continuous (fun t : ℝ => y + t • u) := by fun_prop
  have hopen : IsOpen ((fun t : ℝ => y + t • u) ⁻¹' interior S) := isOpen_interior.preimage hc
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen 0 (by simpa using hy)
  have hm : (ε / 2) ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  have hmem : y + (ε / 2) • u ∈ S := interior_subset (hball hm)
  have := hS _ hmem
  rw [inner_add_left, real_inner_smul_left] at this
  nlinarith

lemma mem_frontier_of {S : Set (Position 2)} {x u : Position 2} (hx : x ∈ S)
    (hS : ∀ y ∈ S, inner ℝ y u ≤ inner ℝ x u) (hu : 0 < inner ℝ u u) : x ∈ frontier S := by
  rw [frontier, mem_sdiff]
  exact ⟨subset_closure hx, fun hi => lt_irrefl _ (inner_lt_of_mem_interior hS hu hi)⟩

lemma mem_normalConeE_of {S : Set (Position 2)} {u p : Position 2}
    (h : ∀ y ∈ S, inner ℝ y u ≤ inner ℝ p u) : u ∈ normalConeE S p := by
  intro y hy
  show inner ℝ u (y - p) ≤ 0
  rw [inner_sub_right, real_inner_comm y u, real_inner_comm p u]
  linarith [h y hy]

/-! ## Convex domains -/

/-! ## The diagonal billiards -/

lemma pv_mod (k : ℕ) : pentagonVertex (k + 5) = pentagonVertex k := by
  rw [pv_eq, pv_eq]; push_cast
  rw [show 2 * π * ((k : ℝ) + 5) / 5 = 2 * π * k / 5 + 2 * π by ring, Real.cos_add_two_pi,
    Real.sin_add_two_pi]

lemma rv_mod (k : ℕ) : rotatedVertex (k + 5) = rotatedVertex k := by
  rw [rv_eq, rv_eq]; push_cast
  rw [show 2 * π * ((k : ℝ) + 5) / 5 = 2 * π * k / 5 + 2 * π by ring, Real.cos_add_two_pi,
    Real.sin_add_two_pi]

lemma le_hT_of_mem {p : Position 2} (hp : p ∈ pentagonT) (d : Position 2) :
    inner ℝ d p ≤ supportFunction pentagonT d := by
  rw [real_inner_comm]
  exact hull_le (fun k hk => by rw [real_inner_comm]; exact le_supportFunction_pentagonT d hk) p hp

lemma diag_of (q0 q1 p0 p1 : Position 2) (hq0 : q0 ∈ pentagonK) (hq1 : q1 ∈ pentagonK)
    (hp0 : p0 ∈ pentagonT) (hp1 : p1 ∈ pentagonT)
    (fq0 : ∀ k < 5, inner ℝ (pentagonVertex k) q0 ≤ inner ℝ q0 q0)
    (fq1 : ∀ k < 5, inner ℝ (pentagonVertex k) q1 ≤ inner ℝ q1 q1)
    (fp0 : ∀ k < 5, inner ℝ (rotatedVertex k) p0 ≤ inner ℝ p0 p0)
    (fp1 : ∀ k < 5, inner ℝ (rotatedVertex k) p1 ≤ inner ℝ p1 p1)
    (pq0 : 0 < inner ℝ q0 q0) (pq1 : 0 < inner ℝ q1 q1) (pp0 : 0 < inner ℝ p0 p0)
    (pp1 : 0 < inner ℝ p1 p1) (hne : inner ℝ q1 q0 < inner ℝ q0 q0)
    (n1 : ∀ k < 5, inner ℝ (rotatedVertex k) (q1 - q0) ≤ inner ℝ p0 (q1 - q0))
    (n2 : ∀ k < 5, inner ℝ (rotatedVertex k) (q0 - q1) ≤ inner ℝ p1 (q0 - q1))
    (n3 : ∀ k < 5, inner ℝ (pentagonVertex k) (p0 - p1) ≤ inner ℝ q1 (p0 - p1))
    (n4 : ∀ k < 5, inner ℝ (pentagonVertex k) (p1 - p0) ≤ inner ℝ q0 (p1 - p0)) :
    IsClosedBilliard pentagonK pentagonT ![q0, q1] ∧
      polygonLength pentagonT ![q0, q1] = inner ℝ (q1 - q0) p0 + inner ℝ (q0 - q1) p1 := by
  have h1 : supportFunction pentagonT (q1 - q0) = inner ℝ (q1 - q0) p0 :=
    le_antisymm (supportFunction_pentagonT_le _ (fun k hk => by
      linarith [n1 k hk, real_inner_comm p0 (q1 - q0), real_inner_comm (rotatedVertex k) (q1 - q0)])) (le_hT_of_mem hp0 _)
  have h2 : supportFunction pentagonT (q0 - q1) = inner ℝ (q0 - q1) p1 :=
    le_antisymm (supportFunction_pentagonT_le _ (fun k hk => by
      linarith [n2 k hk, real_inner_comm p1 (q0 - q1), real_inner_comm (rotatedVertex k) (q0 - q1)])) (le_hT_of_mem hp1 _)
  refine ⟨⟨le_refl _, ?_, ?_, ![p0, p1], ?_⟩, ?_⟩
  · intro j; fin_cases j
    · exact mem_frontier_of hq0 (hull_le fq0) pq0
    · exact mem_frontier_of hq1 (hull_le fq1) pq1
  · intro j; fin_cases j
    · intro h; simp at h; rw [h] at hne; exact lt_irrefl _ hne
    · intro h; simp at h; rw [h] at hne; exact lt_irrefl _ hne
  · intro j; fin_cases j
    · refine ⟨mem_frontier_of hp0 (hull_le fp0) pp0, ?_, ?_⟩
      · exact mem_normalConeE_of (hull_le n1)
      · simp only [Fin.isValue, Set.mem_neg]
        simp
        exact mem_normalConeE_of (hull_le (by simpa using n3))
    · refine ⟨mem_frontier_of hp1 (hull_le fp1) pp1, ?_, ?_⟩
      · simp
        exact mem_normalConeE_of (hull_le n2)
      · simp only [Fin.isValue, Set.mem_neg]
        simp
        exact mem_normalConeE_of (hull_le (by simpa using n4))
  · simp [polygonLength, Fin.sum_univ_two, h1, h2]

lemma cos_pi_div_ten : Real.cos (π / 10) = 2 * ss * cc := by
  rw [show π / 10 = π / 2 - 2 * π / 5 by ring, Real.cos_pi_div_two_sub, sin2]

lemma pv_mem (k : ℕ) : pentagonVertex k ∈ pentagonK := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hk : k < 5
    · exact mem_hull5 _ hk
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 5 := ⟨k - 5, by omega⟩
      rw [pv_mod]; exact ih j (by omega)

lemma rv_mem (k : ℕ) : rotatedVertex k ∈ pentagonT := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hk : k < 5
    · exact mem_hull5 _ hk
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 5 := ⟨k - 5, by omega⟩
      rw [rv_mod]; exact ih j (by omega)

lemma diag0 : IsClosedBilliard pentagonK pentagonT ![pentagonVertex 0, pentagonVertex 2] ∧
    polygonLength pentagonT ![pentagonVertex 0, pentagonVertex 2] =
      2 * Real.cos (π / 10) * (1 + Real.cos (π / 5)) := by
  obtain ⟨h1, h2⟩ := diag_of (pentagonVertex 0) (pentagonVertex 2) (rotatedVertex 4) (rotatedVertex 1)
    (mem_hull5 _ (by norm_num)) (mem_hull5 _ (by norm_num)) (mem_hull5 _ (by norm_num))
    (mem_hull5 _ (by norm_num)) (by (intro j hj; interval_cases j <;> simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (intro j hj; interval_cases j <;> simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (intro j hj; interval_cases j <;> simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (intro j hj; interval_cases j <;> simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds]))
    (by (simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (intro j hj; interval_cases j <;> simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (intro j hj; interval_cases j <;> simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (intro j hj; interval_cases j <;> simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (intro j hj; interval_cases j <;> simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds]))
  refine ⟨h1, ?_⟩
  rw [h2, cos_pi_div_ten, show Real.cos (π / 5) = cc from rfl]
  (simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])

lemma diag1 : IsClosedBilliard pentagonK pentagonT ![pentagonVertex 1, pentagonVertex 3] ∧
    polygonLength pentagonT ![pentagonVertex 1, pentagonVertex 3] =
      2 * Real.cos (π / 10) * (1 + Real.cos (π / 5)) := by
  obtain ⟨h1, h2⟩ := diag_of (pentagonVertex 1) (pentagonVertex 3) (rotatedVertex 5) (rotatedVertex 2)
    (pv_mem _) (pv_mem _) (rv_mem _) (rv_mem _)
    (by (intro j hj; interval_cases j <;> simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (intro j hj; interval_cases j <;> simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (intro j hj; interval_cases j <;> simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (intro j hj; interval_cases j <;> simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds]))
    (by (simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (intro j hj; interval_cases j <;> simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (intro j hj; interval_cases j <;> simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (intro j hj; interval_cases j <;> simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (intro j hj; interval_cases j <;> simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds]))
  refine ⟨h1, ?_⟩
  rw [h2, cos_pi_div_ten, show Real.cos (π / 5) = cc from rfl]
  (simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])

lemma diag2 : IsClosedBilliard pentagonK pentagonT ![pentagonVertex 2, pentagonVertex 4] ∧
    polygonLength pentagonT ![pentagonVertex 2, pentagonVertex 4] =
      2 * Real.cos (π / 10) * (1 + Real.cos (π / 5)) := by
  obtain ⟨h1, h2⟩ := diag_of (pentagonVertex 2) (pentagonVertex 4) (rotatedVertex 6) (rotatedVertex 3)
    (pv_mem _) (pv_mem _) (rv_mem _) (rv_mem _)
    (by (intro j hj; interval_cases j <;> simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (intro j hj; interval_cases j <;> simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (intro j hj; interval_cases j <;> simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (intro j hj; interval_cases j <;> simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds]))
    (by (simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (intro j hj; interval_cases j <;> simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (intro j hj; interval_cases j <;> simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (intro j hj; interval_cases j <;> simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (intro j hj; interval_cases j <;> simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds]))
  refine ⟨h1, ?_⟩
  rw [h2, cos_pi_div_ten, show Real.cos (π / 5) = cc from rfl]
  (simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])

lemma diag3 : IsClosedBilliard pentagonK pentagonT ![pentagonVertex 3, pentagonVertex 5] ∧
    polygonLength pentagonT ![pentagonVertex 3, pentagonVertex 5] =
      2 * Real.cos (π / 10) * (1 + Real.cos (π / 5)) := by
  obtain ⟨h1, h2⟩ := diag_of (pentagonVertex 3) (pentagonVertex 5) (rotatedVertex 7) (rotatedVertex 4)
    (pv_mem _) (pv_mem _) (rv_mem _) (rv_mem _)
    (by (intro j hj; interval_cases j <;> simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (intro j hj; interval_cases j <;> simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (intro j hj; interval_cases j <;> simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (intro j hj; interval_cases j <;> simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds]))
    (by (simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (intro j hj; interval_cases j <;> simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (intro j hj; interval_cases j <;> simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (intro j hj; interval_cases j <;> simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (intro j hj; interval_cases j <;> simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds]))
  refine ⟨h1, ?_⟩
  rw [h2, cos_pi_div_ten, show Real.cos (π / 5) = cc from rfl]
  (simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])

lemma diag4 : IsClosedBilliard pentagonK pentagonT ![pentagonVertex 4, pentagonVertex 6] ∧
    polygonLength pentagonT ![pentagonVertex 4, pentagonVertex 6] =
      2 * Real.cos (π / 10) * (1 + Real.cos (π / 5)) := by
  obtain ⟨h1, h2⟩ := diag_of (pentagonVertex 4) (pentagonVertex 6) (rotatedVertex 8) (rotatedVertex 5)
    (pv_mem _) (pv_mem _) (rv_mem _) (rv_mem _)
    (by (intro j hj; interval_cases j <;> simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (intro j hj; interval_cases j <;> simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (intro j hj; interval_cases j <;> simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (intro j hj; interval_cases j <;> simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds]))
    (by (simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (intro j hj; interval_cases j <;> simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (intro j hj; interval_cases j <;> simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (intro j hj; interval_cases j <;> simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])) (by (intro j hj; interval_cases j <;> simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds]))
  refine ⟨h1, ?_⟩
  rw [h2, cos_pi_div_ten, show Real.cos (π / 5) = cc from rfl]
  (simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])

theorem diag_billiard (k : ℕ) (hk : k < 5) :
    IsClosedBilliard pentagonK pentagonT ![pentagonVertex k, pentagonVertex (k + 2)] ∧
      polygonLength pentagonT ![pentagonVertex k, pentagonVertex (k + 2)] =
        2 * Real.cos (Real.pi / 10) * (1 + Real.cos (Real.pi / 5)) := by
  interval_cases k
  · exact diag0
  · exact diag1
  · exact diag2
  · exact diag3
  · exact diag4

theorem notTranslatable_diag0 :
    NotTranslatableIntoInterior pentagonK ![pentagonVertex 0, pentagonVertex 2] := by
  intro t h
  have h0 := h 0
  have h1 := h 1
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Set.add_singleton,
    Set.mem_image] at h0 h1
  obtain ⟨y0, hy0, e0⟩ := h0
  obtain ⟨y2, hy2, e2⟩ := h1
  have hK1 : ∀ x ∈ pentagonK, inner ℝ x (pentagonVertex 2 - pentagonVertex 0) ≤
      inner ℝ (pentagonVertex 2) (pentagonVertex 2 - pentagonVertex 0) := hull_le (by (intro j hj; interval_cases j <;> simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds]))
  have hK2 : ∀ x ∈ pentagonK, inner ℝ x (pentagonVertex 0 - pentagonVertex 2) ≤
      inner ℝ (pentagonVertex 0) (pentagonVertex 0 - pentagonVertex 2) := hull_le (by (intro j hj; interval_cases j <;> simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds]))
  have hu1 : 0 < inner ℝ (pentagonVertex 2 - pentagonVertex 0) (pentagonVertex 2 - pentagonVertex 0) := by
    (simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])
  have hu2 : 0 < inner ℝ (pentagonVertex 0 - pentagonVertex 2) (pentagonVertex 0 - pentagonVertex 2) := by
    (simp only [inner2, PiLp.sub_apply, PiLp.neg_apply, pv_0_0, pv_0_1, rv_0_0, rv_0_1, pv_1_0, pv_1_1, rv_1_0, rv_1_1, pv_2_0, pv_2_1, rv_2_0, rv_2_1, pv_3_0, pv_3_1, rv_3_0, rv_3_1, pv_4_0, pv_4_1, rv_4_0, rv_4_1, pv_5_0, pv_5_1, rv_5_0, rv_5_1, pv_6_0, pv_6_1, rv_6_0, rv_6_1, pv_7_0, pv_7_1, rv_7_0, rv_7_1, pv_8_0, pv_8_1, rv_8_0, rv_8_1] <;> linarith [cc_sq, ss_sq, cc3, cc4, ss3, ss4, ccss2, cc2ss, cc2ss2, cc3ss, ccss3, cc_bounds, ss_bounds, ccss_bounds])
  have a1 := inner_lt_of_mem_interior hK1 hu1 hy2
  have a2 := inner_lt_of_mem_interior hK2 hu2 hy0
  have b1 := congrArg (fun z => inner ℝ z (pentagonVertex 2 - pentagonVertex 0)) e2
  have b2 := congrArg (fun z => inner ℝ z (pentagonVertex 0 - pentagonVertex 2)) e0
  simp only [inner_add_left] at b1 b2
  have : inner ℝ t (pentagonVertex 0 - pentagonVertex 2) = -inner ℝ t (pentagonVertex 2 - pentagonVertex 0) := by
    rw [inner_sub_right, inner_sub_right]; ring
  linarith

theorem witness : ∃ (m : ℕ) (q : Fin m → Position 2), m ≤ 3 ∧ NotTranslatableIntoInterior pentagonK q ∧
    2 * Real.cos (Real.pi / 10) * (1 + Real.cos (Real.pi / 5)) = polygonLength pentagonT q :=
  ⟨2, ![pentagonVertex 0, pentagonVertex 2], by norm_num, notTranslatable_diag0, diag0.2.symm⟩

end Viterbo.PentA

end
end

section
section
/-!
# Viterbo pentagon, Part B: the lower bound

Every closed polygon with at most three vertices that cannot be translated into the interior of
the pentagon `K` has `T°`-length at least `c₀ = 2 cos(π/10) (1 + cos(π/5))`.

Route.
* `K ⊇ {x | ⟨u_i, x⟩ ≤ s₁ for all i}` with `u_i = w_{i+1} - w_i` (`w_k` the vertices of `T`) and
  `s₁ = sin(2π/5)`; so the strict inequalities give points of `int K`.
* (Helly in the plane) if `M_i = max_j ⟨u_i, q_j⟩` satisfy `M_i + M_{i+1} + 2c M_{i+3} < c₀` for all
  `i` (`c = cos(π/5)`), the polygon translates into `int K`.
* For `m ≤ 3`, each such combination `Ψ` is at most the `T°`-length, by explicit certificates:
  `h_T(d) ≥ ⟨d, w_k⟩` and `h_T(d) ≥ ⟨d, w_{k-1} + w_{k+1} - w_k⟩`.
-/

namespace Viterbo.PentB

open Viterbo OAI.SymmetricPolar Set Real
open scoped Pointwise

/-! ## Constants -/

/-- `cc = cos (π/5)`. -/
noncomputable def cc : ℝ := Real.cos (π / 5)
/-- `ss = sin (π/5)`. -/
noncomputable def ss : ℝ := Real.sin (π / 5)

lemma cc_sq : cc ^ 2 = (2 * cc + 1) / 4 := by
  have h := Real.cos_pi_div_five
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  simp only [cc]; rw [h]; nlinarith [h5]

lemma ss_sq : ss ^ 2 = (3 - 2 * cc) / 4 := by
  have := Real.sin_sq_add_cos_sq (π / 5)
  have := cc_sq
  simp only [ss, cc] at *; linarith

lemma ss_pos : 0 < ss := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · positivity
  · linarith [Real.pi_pos]

lemma cc_bounds : 0.809 < cc ∧ cc < 0.80903 := by
  have h := Real.cos_pi_div_five
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  simp only [cc]; rw [h]
  constructor <;> nlinarith

lemma ss_bounds : 0.5877 < ss ∧ ss < 0.5879 := by
  have := ss_sq; have := cc_bounds; have := ss_pos
  constructor <;> nlinarith

lemma cc3 : cc ^ 3 = (4 * cc + 1) / 8 := by linear_combination (cc + 1/2) * cc_sq
lemma cc4 : cc ^ 4 = (3 * cc + 1) / 8 := by linear_combination (cc ^ 2 + cc / 2 + 1 / 2) * cc_sq
lemma ss3 : ss ^ 3 = (3 - 2 * cc) / 4 * ss := by linear_combination ss * ss_sq
lemma ss4 : ss ^ 4 = (3 - 2 * cc) ^ 2 / 16 := by
  linear_combination (ss ^ 2 + (3 - 2 * cc) / 4) * ss_sq

/-! ## Trig values -/

lemma cos2 : Real.cos (2 * π / 5) = cc - 1 / 2 := by
  rw [show 2 * π / 5 = 2 * (π / 5) by ring, Real.cos_two_mul]; have := cc_sq; simp only [cc] at *
  linarith
lemma sin2 : Real.sin (2 * π / 5) = 2 * ss * cc := by
  rw [show 2 * π / 5 = 2 * (π / 5) by ring, Real.sin_two_mul]; rfl
lemma cos4 : Real.cos (4 * π / 5) = -cc := by
  rw [show 4 * π / 5 = π - π / 5 by ring, Real.cos_pi_sub]; rfl
lemma sin4 : Real.sin (4 * π / 5) = ss := by
  rw [show 4 * π / 5 = π - π / 5 by ring, Real.sin_pi_sub]; rfl
lemma cos6 : Real.cos (6 * π / 5) = -cc := by
  rw [show 6 * π / 5 = π / 5 + π by ring, Real.cos_add_pi]; rfl
lemma sin6 : Real.sin (6 * π / 5) = -ss := by
  rw [show 6 * π / 5 = π / 5 + π by ring, Real.sin_add_pi]; rfl
lemma cos8 : Real.cos (8 * π / 5) = cc - 1 / 2 := by
  rw [show 8 * π / 5 = -(2 * π / 5) + 2 * π by ring, Real.cos_add_two_pi, Real.cos_neg, cos2]
lemma sin8 : Real.sin (8 * π / 5) = -(2 * ss * cc) := by
  rw [show 8 * π / 5 = -(2 * π / 5) + 2 * π by ring, Real.sin_add_two_pi, Real.sin_neg, sin2]

/-- `c₀ = 2 cos(π/10)(1 + cos(π/5)) = 2 s₁ (1 + c)` with `s₁ = sin(2π/5) = 2 ss cc`. -/
lemma c0_eq : 2 * Real.cos (Real.pi / 10) * (1 + Real.cos (Real.pi / 5)) =
    2 * (2 * ss * cc) * (1 + cc) := by
  rw [show Real.pi / 10 = Real.pi / 2 - 2 * Real.pi / 5 by ring, Real.cos_pi_div_two_sub, sin2]
  rfl

/-! ## Coordinates -/

lemma inner2 (x y : Position 2) : inner ℝ x y = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]; ring

/-- `cos (2πk/5)`. -/
noncomputable def X : Fin 5 → ℝ := ![1, cc - 1 / 2, -cc, -cc, cc - 1 / 2]
/-- `sin (2πk/5)`. -/
noncomputable def Y : Fin 5 → ℝ := ![0, 2 * ss * cc, ss, -ss, -(2 * ss * cc)]

lemma cosk (k : Fin 5) : Real.cos (2 * π * ((k : ℕ) : ℝ) / 5) = X k := by
  fin_cases k
  · simp [X]
  · simp only [X]; rw [show 2 * π * ((1 : ℕ) : ℝ) / 5 = 2 * π / 5 by push_cast; ring, cos2]; rfl
  · simp only [X]; rw [show 2 * π * ((2 : ℕ) : ℝ) / 5 = 4 * π / 5 by push_cast; ring, cos4]; rfl
  · simp only [X]; rw [show 2 * π * ((3 : ℕ) : ℝ) / 5 = 6 * π / 5 by push_cast; ring, cos6]; rfl
  · simp only [X]; rw [show 2 * π * ((4 : ℕ) : ℝ) / 5 = 8 * π / 5 by push_cast; ring, cos8]; rfl

lemma sink (k : Fin 5) : Real.sin (2 * π * ((k : ℕ) : ℝ) / 5) = Y k := by
  fin_cases k
  · simp [Y]
  · simp only [Y]; rw [show 2 * π * ((1 : ℕ) : ℝ) / 5 = 2 * π / 5 by push_cast; ring, sin2]; rfl
  · simp only [Y]; rw [show 2 * π * ((2 : ℕ) : ℝ) / 5 = 4 * π / 5 by push_cast; ring, sin4]; rfl
  · simp only [Y]; rw [show 2 * π * ((3 : ℕ) : ℝ) / 5 = 6 * π / 5 by push_cast; ring, sin6]; rfl
  · simp only [Y]; rw [show 2 * π * ((4 : ℕ) : ℝ) / 5 = 8 * π / 5 by push_cast; ring, sin8]; rfl

/-- The vertices of `K` and `T`, indexed by `Fin 5`. -/
noncomputable def v (k : Fin 5) : Position 2 := pentagonVertex k
noncomputable def w (k : Fin 5) : Position 2 := rotatedVertex k

lemma v0 (k : Fin 5) : v k 0 = X k := by
  rw [← cosk]; rfl
lemma v1 (k : Fin 5) : v k 1 = Y k := by
  rw [← sink]; rfl
lemma w0 (k : Fin 5) : w k 0 = Y k := by
  rw [← sink]; unfold w rotatedVertex
  simp only [show -(π / 2) + 2 * π * ((k : ℕ) : ℝ) / 5 = 2 * π * ((k : ℕ) : ℝ) / 5 - π / 2 by ring,
    Real.cos_sub_pi_div_two]; rfl
lemma w1 (k : Fin 5) : w k 1 = -X k := by
  rw [← cosk]; unfold w rotatedVertex
  simp only [show -(π / 2) + 2 * π * ((k : ℕ) : ℝ) / 5 = 2 * π * ((k : ℕ) : ℝ) / 5 - π / 2 by ring,
    Real.sin_sub_pi_div_two]; rfl

/-- `P x k = ⟨x, w_k⟩`. -/
noncomputable def P (x : Position 2) (k : Fin 5) : ℝ := x 0 * Y k - x 1 * X k

lemma inner_w (x : Position 2) (k : Fin 5) : inner ℝ x (w k) = P x k := by
  rw [inner2, w0, w1, P]; ring

/-! ## Scalar facts about the tables -/

lemma detXY (k : Fin 5) : X k * Y (k + 1) - Y k * X (k + 1) = 2 * ss * cc := by
  fin_cases k <;> simp [X, Y] <;> ((try ring_nf) <;> (try simp only [cc_sq, ss_sq, cc3, cc4, ss3, ss4]) <;> (try ring_nf) <;> (try simp only [cc_sq, ss_sq, cc3, cc4, ss3, ss4]) <;> (try ring_nf) <;> (try simp only [cc_sq, ss_sq, cc3, cc4, ss3, ss4]) <;> (try ring_nf))

lemma sumX : X 0 + X 1 + X 2 + X 3 + X 4 = 0 := by simp [X]; try ring
lemma sumY : Y 0 + Y 1 + Y 2 + Y 3 + Y 4 = 0 := by simp [Y]; try ring

lemma goldX (k : Fin 5) : X (k - 1) + X (k + 1) = (2 * cc - 1) * X k := by
  fin_cases k <;> simp [X] <;> ((try ring_nf) <;> (try simp only [cc_sq, ss_sq, cc3, cc4, ss3, ss4]) <;> (try ring_nf) <;> (try simp only [cc_sq, ss_sq, cc3, cc4, ss3, ss4]) <;> (try ring_nf) <;> (try simp only [cc_sq, ss_sq, cc3, cc4, ss3, ss4]) <;> (try ring_nf))
lemma goldY (k : Fin 5) : Y (k - 1) + Y (k + 1) = (2 * cc - 1) * Y k := by
  fin_cases k <;> simp [Y] <;> ((try ring_nf) <;> (try simp only [cc_sq, ss_sq, cc3, cc4, ss3, ss4]) <;> (try ring_nf) <;> (try simp only [cc_sq, ss_sq, cc3, cc4, ss3, ss4]) <;> (try ring_nf) <;> (try simp only [cc_sq, ss_sq, cc3, cc4, ss3, ss4]) <;> (try ring_nf))

lemma circX (i : Fin 5) : X (i + 2) - X i + 2 * cc * (X (i + 4) - X (i + 3)) = 0 := by
  fin_cases i <;> simp [X] <;> ((try ring_nf) <;> (try simp only [cc_sq, ss_sq, cc3, cc4, ss3, ss4]) <;> (try ring_nf) <;> (try simp only [cc_sq, ss_sq, cc3, cc4, ss3, ss4]) <;> (try ring_nf) <;> (try simp only [cc_sq, ss_sq, cc3, cc4, ss3, ss4]) <;> (try ring_nf))
lemma circY (i : Fin 5) : Y (i + 2) - Y i + 2 * cc * (Y (i + 4) - Y (i + 3)) = 0 := by
  fin_cases i <;> simp [Y] <;> ((try ring_nf) <;> (try simp only [cc_sq, ss_sq, cc3, cc4, ss3, ss4]) <;> (try ring_nf) <;> (try simp only [cc_sq, ss_sq, cc3, cc4, ss3, ss4]) <;> (try ring_nf) <;> (try simp only [cc_sq, ss_sq, cc3, cc4, ss3, ss4]) <;> (try ring_nf))

lemma oppX (k : Fin 5) : X (k + 2) + X (k + 3) = -(2 * cc) * X k := by
  fin_cases k <;> simp [X] <;> ((try ring_nf) <;> (try simp only [cc_sq, ss_sq, cc3, cc4, ss3, ss4]) <;> (try ring_nf) <;> (try simp only [cc_sq, ss_sq, cc3, cc4, ss3, ss4]) <;> (try ring_nf) <;> (try simp only [cc_sq, ss_sq, cc3, cc4, ss3, ss4]) <;> (try ring_nf))
lemma oppY (k : Fin 5) : Y (k + 2) + Y (k + 3) = -(2 * cc) * Y k := by
  fin_cases k <;> simp [Y] <;> ((try ring_nf) <;> (try simp only [cc_sq, ss_sq, cc3, cc4, ss3, ss4]) <;> (try ring_nf) <;> (try simp only [cc_sq, ss_sq, cc3, cc4, ss3, ss4]) <;> (try ring_nf) <;> (try simp only [cc_sq, ss_sq, cc3, cc4, ss3, ss4]) <;> (try ring_nf))

lemma P_sub (x y : Position 2) (k : Fin 5) : P (x - y) k = P x k - P y k := by
  simp only [P, PiLp.sub_apply]; ring

lemma P_sum (x : Position 2) : P x 0 + P x 1 + P x 2 + P x 3 + P x 4 = 0 := by
  have h1 := sumX; have h2 := sumY
  simp only [P]; linear_combination x 0 * h2 - x 1 * h1

lemma P_gold (x : Position 2) (k : Fin 5) : P x (k - 1) + P x (k + 1) = (2 * cc - 1) * P x k := by
  have h1 := goldX k; have h2 := goldY k
  simp only [P]; linear_combination x 0 * h2 - x 1 * h1

lemma P_opp (x : Position 2) (k : Fin 5) : P x (k + 2) + P x (k + 3) = -(2 * cc) * P x k := by
  have h1 := oppX k; have h2 := oppY k
  simp only [P]; linear_combination x 0 * h2 - x 1 * h1

/-! ## Lower bounds for the support function of `T` -/

lemma w_mem_T (k : Fin 5) : w k ∈ pentagonT :=
  subset_convexHull ℝ _ ⟨k, by simp, rfl⟩

lemma bdd_T (d : Position 2) : BddAbove ((fun x => inner ℝ x d) '' pentagonT) := by
  have hfin : (rotatedVertex '' (Finset.range 5 : Set ℕ)).Finite := (Finset.finite_toSet _).image _
  exact ((hfin.isCompact_convexHull ℝ).image (by fun_prop)).bddAbove

/-- `h_T(d) ≥ ⟨d, w_k⟩`. -/
lemma hT_ge (d : Position 2) (k : Fin 5) : P d k ≤ supportFunction pentagonT d := by
  rw [← inner_w]
  exact le_csSup (bdd_T d) ⟨w k, w_mem_T k, real_inner_comm _ _⟩

lemma hT_nonneg (d : Position 2) : 0 ≤ supportFunction pentagonT d := by
  have := P_sum d
  have h0 := hT_ge d 0; have h1 := hT_ge d 1; have h2 := hT_ge d 2; have h3 := hT_ge d 3
  have h4 := hT_ge d 4
  linarith

/-- `h_T(d) ≥ ⟨d, w_{k-1} + w_{k+1} - w_k⟩` (this point is `(2c - 2) w_k ∈ T`). -/
lemma hT_ge2 (d : Position 2) (k : Fin 5) :
    P d (k - 1) + P d (k + 1) - P d k ≤ supportFunction pentagonT d := by
  have hg := P_gold d k
  have ho := P_opp d k
  have ha := hT_ge d (k + 2)
  have hb := hT_ge d (k + 3)
  have h0 := hT_nonneg d
  have hcb := cc_bounds
  have key : P d (k - 1) + P d (k + 1) - P d k = (4 * cc - 3) * (P d (k + 2) + P d (k + 3)) := by
    rw [hg, ho]; linear_combination (8 * P d k) * cc_sq
  rw [key]
  have h4 : 0 ≤ 4 * cc - 3 := by linarith
  have := mul_le_mul_of_nonneg_left (add_le_add ha hb) h4
  nlinarith

lemma hT_ge_sub (x y : Position 2) (k : Fin 5) :
    P x k - P y k ≤ supportFunction pentagonT (x - y) := by
  rw [← P_sub]; exact hT_ge _ k

lemma hT_ge2_sub (x y : Position 2) (k : Fin 5) :
    (P x (k - 1) - P y (k - 1)) + (P x (k + 1) - P y (k + 1)) - (P x k - P y k) ≤
      supportFunction pentagonT (x - y) := by
  rw [← P_sub, ← P_sub, ← P_sub]; exact hT_ge2 _ k

/-! ## The polygon lengths for `m = 2, 3` -/

lemma length2 (q : Fin 2 → Position 2) : polygonLength pentagonT q =
    supportFunction pentagonT (q 1 - q 0) + supportFunction pentagonT (q 0 - q 1) := by
  simp [polygonLength, Fin.sum_univ_two]

lemma length3 (q : Fin 3 → Position 2) : polygonLength pentagonT q =
    supportFunction pentagonT (q 1 - q 0) + supportFunction pentagonT (q 2 - q 1) +
      supportFunction pentagonT (q 0 - q 2) := by
  simp [polygonLength, Fin.sum_univ_three]

/-! ## The certificates: `Ψ ≤ length` for `m = 2, 3` -/

/-- `Ψ_i(j₁, j₂, j₃) = ⟨u_i, q_{j₁}⟩ + ⟨u_{i+1}, q_{j₂}⟩ - ⟨u_i + u_{i+1}, q_{j₃}⟩` in the coordinates
`p j k = ⟨q_j, w_k⟩`. -/
def Psi {m : ℕ} (p : Fin m → Fin 5 → ℝ) (i : Fin 5) (j1 j2 j3 : Fin m) : ℝ :=
  (p j1 (i + 1) - p j1 i) + (p j2 (i + 2) - p j2 (i + 1)) - (p j3 (i + 2) - p j3 i)

lemma core3 (p : Fin 3 → Fin 5 → ℝ) (H0 H1 H2 : ℝ)
    (_hs0 : p 0 0 + p 0 1 + p 0 2 + p 0 3 + p 0 4 = 0)
    (_hs1 : p 1 0 + p 1 1 + p 1 2 + p 1 3 + p 1 4 = 0)
    (_hs2 : p 2 0 + p 2 1 + p 2 2 + p 2 3 + p 2 4 = 0)
    (a0 : ∀ k, p 1 k - p 0 k ≤ H0)
    (b0 : ∀ k, (p 1 (k - 1) - p 0 (k - 1)) + (p 1 (k + 1) - p 0 (k + 1)) - (p 1 k - p 0 k) ≤ H0)
    (a1 : ∀ k, p 2 k - p 1 k ≤ H1)
    (b1 : ∀ k, (p 2 (k - 1) - p 1 (k - 1)) + (p 2 (k + 1) - p 1 (k + 1)) - (p 2 k - p 1 k) ≤ H1)
    (a2 : ∀ k, p 0 k - p 2 k ≤ H2)
    (b2 : ∀ k, (p 0 (k - 1) - p 2 (k - 1)) + (p 0 (k + 1) - p 2 (k + 1)) - (p 0 k - p 2 k) ≤ H2)
    (i : Fin 5) (j1 j2 j3 : Fin 3) : Psi p i j1 j2 j3 ≤ H0 + H1 + H2 := by
  have a0_0 : p 1 0 - p 0 0 ≤ H0 := a0 0
  have b0_0 : (p 1 4 - p 0 4) + (p 1 1 - p 0 1) - (p 1 0 - p 0 0) ≤ H0 := b0 0
  have a0_1 : p 1 1 - p 0 1 ≤ H0 := a0 1
  have b0_1 : (p 1 0 - p 0 0) + (p 1 2 - p 0 2) - (p 1 1 - p 0 1) ≤ H0 := b0 1
  have a0_2 : p 1 2 - p 0 2 ≤ H0 := a0 2
  have b0_2 : (p 1 1 - p 0 1) + (p 1 3 - p 0 3) - (p 1 2 - p 0 2) ≤ H0 := b0 2
  have a0_3 : p 1 3 - p 0 3 ≤ H0 := a0 3
  have b0_3 : (p 1 2 - p 0 2) + (p 1 4 - p 0 4) - (p 1 3 - p 0 3) ≤ H0 := b0 3
  have a0_4 : p 1 4 - p 0 4 ≤ H0 := a0 4
  have b0_4 : (p 1 3 - p 0 3) + (p 1 0 - p 0 0) - (p 1 4 - p 0 4) ≤ H0 := b0 4
  have a1_0 : p 2 0 - p 1 0 ≤ H1 := a1 0
  have b1_0 : (p 2 4 - p 1 4) + (p 2 1 - p 1 1) - (p 2 0 - p 1 0) ≤ H1 := b1 0
  have a1_1 : p 2 1 - p 1 1 ≤ H1 := a1 1
  have b1_1 : (p 2 0 - p 1 0) + (p 2 2 - p 1 2) - (p 2 1 - p 1 1) ≤ H1 := b1 1
  have a1_2 : p 2 2 - p 1 2 ≤ H1 := a1 2
  have b1_2 : (p 2 1 - p 1 1) + (p 2 3 - p 1 3) - (p 2 2 - p 1 2) ≤ H1 := b1 2
  have a1_3 : p 2 3 - p 1 3 ≤ H1 := a1 3
  have b1_3 : (p 2 2 - p 1 2) + (p 2 4 - p 1 4) - (p 2 3 - p 1 3) ≤ H1 := b1 3
  have a1_4 : p 2 4 - p 1 4 ≤ H1 := a1 4
  have b1_4 : (p 2 3 - p 1 3) + (p 2 0 - p 1 0) - (p 2 4 - p 1 4) ≤ H1 := b1 4
  have a2_0 : p 0 0 - p 2 0 ≤ H2 := a2 0
  have b2_0 : (p 0 4 - p 2 4) + (p 0 1 - p 2 1) - (p 0 0 - p 2 0) ≤ H2 := b2 0
  have a2_1 : p 0 1 - p 2 1 ≤ H2 := a2 1
  have b2_1 : (p 0 0 - p 2 0) + (p 0 2 - p 2 2) - (p 0 1 - p 2 1) ≤ H2 := b2 1
  have a2_2 : p 0 2 - p 2 2 ≤ H2 := a2 2
  have b2_2 : (p 0 1 - p 2 1) + (p 0 3 - p 2 3) - (p 0 2 - p 2 2) ≤ H2 := b2 2
  have a2_3 : p 0 3 - p 2 3 ≤ H2 := a2 3
  have b2_3 : (p 0 2 - p 2 2) + (p 0 4 - p 2 4) - (p 0 3 - p 2 3) ≤ H2 := b2 3
  have a2_4 : p 0 4 - p 2 4 ≤ H2 := a2 4
  have b2_4 : (p 0 3 - p 2 3) + (p 0 0 - p 2 0) - (p 0 4 - p 2 4) ≤ H2 := b2 4
  fin_cases i <;> fin_cases j1 <;> fin_cases j2 <;> fin_cases j3 <;>
    simp only [Psi, Fin.isValue, Fin.reduceAdd, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> linarith

lemma core2 (p : Fin 2 → Fin 5 → ℝ) (H0 H1 : ℝ)
    (_hs0 : p 0 0 + p 0 1 + p 0 2 + p 0 3 + p 0 4 = 0)
    (_hs1 : p 1 0 + p 1 1 + p 1 2 + p 1 3 + p 1 4 = 0)
    (a0 : ∀ k, p 1 k - p 0 k ≤ H0)
    (b0 : ∀ k, (p 1 (k - 1) - p 0 (k - 1)) + (p 1 (k + 1) - p 0 (k + 1)) - (p 1 k - p 0 k) ≤ H0)
    (a1 : ∀ k, p 0 k - p 1 k ≤ H1)
    (b1 : ∀ k, (p 0 (k - 1) - p 1 (k - 1)) + (p 0 (k + 1) - p 1 (k + 1)) - (p 0 k - p 1 k) ≤ H1)
    (i : Fin 5) (j1 j2 j3 : Fin 2) : Psi p i j1 j2 j3 ≤ H0 + H1 := by
  have a0_0 : p 1 0 - p 0 0 ≤ H0 := a0 0
  have b0_0 : (p 1 4 - p 0 4) + (p 1 1 - p 0 1) - (p 1 0 - p 0 0) ≤ H0 := b0 0
  have a0_1 : p 1 1 - p 0 1 ≤ H0 := a0 1
  have b0_1 : (p 1 0 - p 0 0) + (p 1 2 - p 0 2) - (p 1 1 - p 0 1) ≤ H0 := b0 1
  have a0_2 : p 1 2 - p 0 2 ≤ H0 := a0 2
  have b0_2 : (p 1 1 - p 0 1) + (p 1 3 - p 0 3) - (p 1 2 - p 0 2) ≤ H0 := b0 2
  have a0_3 : p 1 3 - p 0 3 ≤ H0 := a0 3
  have b0_3 : (p 1 2 - p 0 2) + (p 1 4 - p 0 4) - (p 1 3 - p 0 3) ≤ H0 := b0 3
  have a0_4 : p 1 4 - p 0 4 ≤ H0 := a0 4
  have b0_4 : (p 1 3 - p 0 3) + (p 1 0 - p 0 0) - (p 1 4 - p 0 4) ≤ H0 := b0 4
  have a1_0 : p 0 0 - p 1 0 ≤ H1 := a1 0
  have b1_0 : (p 0 4 - p 1 4) + (p 0 1 - p 1 1) - (p 0 0 - p 1 0) ≤ H1 := b1 0
  have a1_1 : p 0 1 - p 1 1 ≤ H1 := a1 1
  have b1_1 : (p 0 0 - p 1 0) + (p 0 2 - p 1 2) - (p 0 1 - p 1 1) ≤ H1 := b1 1
  have a1_2 : p 0 2 - p 1 2 ≤ H1 := a1 2
  have b1_2 : (p 0 1 - p 1 1) + (p 0 3 - p 1 3) - (p 0 2 - p 1 2) ≤ H1 := b1 2
  have a1_3 : p 0 3 - p 1 3 ≤ H1 := a1 3
  have b1_3 : (p 0 2 - p 1 2) + (p 0 4 - p 1 4) - (p 0 3 - p 1 3) ≤ H1 := b1 3
  have a1_4 : p 0 4 - p 1 4 ≤ H1 := a1 4
  have b1_4 : (p 0 3 - p 1 3) + (p 0 0 - p 1 0) - (p 0 4 - p 1 4) ≤ H1 := b1 4
  fin_cases i <;> fin_cases j1 <;> fin_cases j2 <;> fin_cases j3 <;>
    simp only [Psi, Fin.isValue, Fin.reduceAdd, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> linarith

/-! ## `K` contains the polygon cut out by the five edge inequalities -/

/-- `s₁ = sin (2π/5)`, the inradius of `K` times the side of `T`. -/
noncomputable def s1 : ℝ := 2 * ss * cc

lemma s1_pos : 0 < s1 := by
  have := ss_bounds; have := cc_bounds; unfold s1; nlinarith

/-- `E i x = ⟨x, w_{i+1} - w_i⟩`. -/
noncomputable def E (i : Fin 5) (x : Position 2) : ℝ := P x (i + 1) - P x i

lemma v_mem_K (k : Fin 5) : v k ∈ pentagonK :=
  subset_convexHull ℝ _ ⟨k, by simp, rfl⟩

lemma zero_mem_K : (0 : Position 2) ∈ pentagonK := by
  have h : ((1/5 : ℝ) • v 0 + (1/5 : ℝ) • v 1 + (1/5 : ℝ) • v 2 + (1/5 : ℝ) • v 3 +
      (1/5 : ℝ) • v 4) = 0 := by
    ext j; fin_cases j
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Fin.zero_eta, v0, PiLp.zero_apply]
      linear_combination sumX / 5
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Fin.mk_one, v1, PiLp.zero_apply]
      linear_combination sumY / 5
  rw [← h]
  have := (convex_convexHull ℝ (pentagonVertex '' (Finset.range 5 : Set ℕ))).sum_mem
    (t := Finset.univ) (w := fun _ : Fin 5 => (1/5 : ℝ)) (z := v) (fun _ _ => by norm_num)
    (by simp) (fun k _ => v_mem_K k)
  rw [pentagonK]
  simpa [Fin.sum_univ_five] using this

/-- Points in the sector between `v_k` and `v_{k+1}` satisfying the `k`-th edge inequality. -/
lemma mem_K_of_sector (x : Position 2) (k : Fin 5) (hk : P x k ≤ 0) (hk1 : 0 ≤ P x (k + 1))
    (hE : P x (k + 1) - P x k ≤ s1) : x ∈ pentagonK := by
  have hs := s1_pos
  have hdet := detXY k
  set α := P x (k + 1) / s1 with hα
  set β := -P x k / s1 with hβ
  have ha : 0 ≤ α := div_nonneg hk1 hs.le
  have hb : 0 ≤ β := div_nonneg (by linarith) hs.le
  have hab : α + β ≤ 1 := by
    rw [hα, hβ, ← add_div, div_le_one hs]; linarith
  have hx : x = α • v k + β • v (k + 1) + (1 - α - β) • (0 : Position 2) := by
    ext j; fin_cases j
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, v0, PiLp.zero_apply, mul_zero,
        add_zero, Fin.zero_eta, hα, hβ, P]
      field_simp
      unfold s1 at *
      linear_combination (-(x 0)) * hdet
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, v1, PiLp.zero_apply, mul_zero,
        add_zero, Fin.mk_one, hα, hβ, P]
      field_simp
      unfold s1 at *
      linear_combination (-(x 1)) * hdet
  rw [hx]
  have := (convex_convexHull ℝ (pentagonVertex '' (Finset.range 5 : Set ℕ))).sum_mem
    (t := Finset.univ) (w := ![α, β, 1 - α - β]) (z := ![v k, v (k + 1), 0])
    (fun i _ => by fin_cases i <;> simp <;> linarith)
    (by simp [Fin.sum_univ_three]) (fun i _ => by
      fin_cases i
      · exact v_mem_K k
      · exact v_mem_K (k + 1)
      · exact zero_mem_K)
  rw [pentagonK]
  simpa [Fin.sum_univ_three] using this

lemma sector (x : Position 2) : ∃ k : Fin 5, P x k ≤ 0 ∧ 0 ≤ P x (k + 1) := by
  have hs := P_sum x
  rcases le_or_gt (P x 0) 0 with h0 | h0 <;> rcases le_or_gt (P x 1) 0 with h1 | h1 <;>
    rcases le_or_gt (P x 2) 0 with h2 | h2 <;> rcases le_or_gt (P x 3) 0 with h3 | h3 <;>
    rcases le_or_gt (P x 4) 0 with h4 | h4 <;>
  first
  | exact ⟨0, by linarith, by simp only [Fin.reduceAdd, Fin.isValue]; linarith⟩
  | exact ⟨1, by linarith, by simp only [Fin.reduceAdd, Fin.isValue]; linarith⟩
  | exact ⟨2, by linarith, by simp only [Fin.reduceAdd, Fin.isValue]; linarith⟩
  | exact ⟨3, by linarith, by simp only [Fin.reduceAdd, Fin.isValue]; linarith⟩
  | exact ⟨4, by linarith, by simp only [Fin.reduceAdd, Fin.isValue]; linarith⟩

lemma mem_K_of_le (x : Position 2) (h : ∀ i, E i x ≤ s1) : x ∈ pentagonK := by
  obtain ⟨k, hk, hk1⟩ := sector x
  exact mem_K_of_sector x k hk hk1 (h k)

lemma E_eq_inner (i : Fin 5) (x : Position 2) : E i x = inner ℝ x (w (i + 1)) - inner ℝ x (w i) := by
  rw [inner_w, inner_w]; rfl

lemma mem_interior_K (x : Position 2) (h : ∀ i, E i x < s1) : x ∈ interior pentagonK := by
  have hopen : IsOpen {y : Position 2 | ∀ i, E i y < s1} := by
    rw [Set.ofPred_forall]
    refine isOpen_iInter_of_finite (fun i => ?_)
    simp only [E_eq_inner]
    exact isOpen_lt (by fun_prop) continuous_const
  exact interior_maximal (fun y hy => mem_K_of_le y (fun i => (hy i).le)) hopen h

/-! ## Translating into the interior (Helly in the plane) -/

/-- A point from its coordinates. -/
noncomputable def mk (a b : ℝ) : Position 2 := !₂[a, b]
lemma mk0 (a b : ℝ) : mk a b 0 = a := rfl
lemma mk1 (a b : ℝ) : mk a b 1 = b := rfl

/-- `U l = u_l = w_{l+1} - w_l`. -/
noncomputable def U (l : Fin 5) : Position 2 := mk (Y (l + 1) - Y l) (-(X (l + 1) - X l))

/-- The Gram values `⟨u_j, u_l⟩ = G (l - j)`. -/
noncomputable def G : Fin 5 → ℝ := ![3 - 2 * cc, (3 - 2 * cc) * (cc - 1 / 2), -((3 - 2 * cc) * cc),
  -((3 - 2 * cc) * cc), (3 - 2 * cc) * (cc - 1 / 2)]

lemma G0 : G 0 = 3 - 2 * cc := rfl
lemma G1 : G 1 = (3 - 2 * cc) * (cc - 1 / 2) := rfl
lemma G2 : G 2 = -((3 - 2 * cc) * cc) := rfl
lemma G3 : G 3 = -((3 - 2 * cc) * cc) := rfl
lemma G4 : G 4 = (3 - 2 * cc) * (cc - 1 / 2) := rfl

lemma gram (j l : Fin 5) : E j (U l) = G (l - j) := by
  fin_cases j <;> fin_cases l <;> simp [E, P, U, mk0, mk1, X, Y, G] <;> ((try ring_nf) <;> (try simp only [cc_sq, ss_sq, cc3, cc4, ss3, ss4]) <;> (try ring_nf) <;> (try simp only [cc_sq, ss_sq, cc3, cc4, ss3, ss4]) <;> (try ring_nf) <;> (try simp only [cc_sq, ss_sq, cc3, cc4, ss3, ss4]) <;> (try ring_nf))

lemma E_add (i : Fin 5) (x y : Position 2) : E i (x + y) = E i x + E i y := by
  simp only [E, P, PiLp.add_apply]; ring

lemma E_smul (i : Fin 5) (a : ℝ) (x : Position 2) : E i (a • x) = a * E i x := by
  simp only [E, P, PiLp.smul_apply, smul_eq_mul]; ring

lemma E_sub (i : Fin 5) (x y : Position 2) : E i (x - y) = E i x - E i y := by
  simp only [E, P, PiLp.sub_apply]; ring

lemma convex_E_gt (i : Fin 5) (b : ℝ) : Convex ℝ {t : Position 2 | b < E i t} := by
  intro x hx y hy a c ha hc hac
  simp only [Set.mem_ofPred_eq, E_add, E_smul] at *
  have hb : a * b + c * b = b := by rw [← add_mul, hac, one_mul]
  rcases ha.eq_or_lt with h | h
  · subst h
    have : c = 1 := by linarith
    subst this; linarith
  · have := mul_lt_mul_of_pos_left hx h
    have := mul_le_mul_of_nonneg_left hy.le hc
    linarith

lemma wit1 (i : Fin 5) (b0 b1 b2 : ℝ) :
    ∃ t, b0 < E i t ∧ b1 < E (i + 1) t ∧ b2 < E (i + 2) t := by
  obtain ⟨e1, e2, e3⟩ : (i + 1) - i = 1 ∧ (i + 1) - (i + 1) = 0 ∧ (i + 1) - (i + 2) = 4 := by
    revert i; decide
  have hcb := cc_bounds
  have hG1 : 0 < G 1 := by rw [G1]; nlinarith
  have hG01 : G 1 ≤ G 0 := by rw [G0, G1]; nlinarith
  set R := (|b0| + |b1| + |b2| + 1) / G 1 with hRdef
  have hR : R * G 1 = |b0| + |b1| + |b2| + 1 := div_mul_cancel₀ _ hG1.ne'
  have hR0 : 0 ≤ R := div_nonneg (by positivity) hG1.le
  have hRG0 := mul_le_mul_of_nonneg_left hG01 hR0
  have := le_abs_self b0; have := le_abs_self b1; have := le_abs_self b2
  have := abs_nonneg b0; have := abs_nonneg b1; have := abs_nonneg b2
  refine ⟨R • U (i + 1), ?_, ?_, ?_⟩
  · rw [E_smul, gram, e1]; linarith
  · rw [E_smul, gram, e2]; linarith
  · rw [E_smul, gram, e3, G4, ← G1]; linarith

lemma wit2 (i : Fin 5) (b0 b1 b3 : ℝ) (hC : b0 + b1 + 2 * cc * b3 < 0) :
    ∃ t, b0 < E i t ∧ b1 < E (i + 1) t ∧ b3 < E (i + 3) t := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ : i - i = 0 ∧ (i + 1) - i = 1 ∧ i - (i + 1) = 4 ∧
      (i + 1) - (i + 1) = 0 ∧ i - (i + 3) = 2 ∧ (i + 1) - (i + 3) = 3 := by
    revert i; decide
  have hcb := cc_bounds
  have hD : 0 < (3 - 2 * cc) * (1 - (cc - 1 / 2) ^ 2) := by nlinarith
  set D := (3 - 2 * cc) * (1 - (cc - 1 / 2) ^ 2) with hDdef
  set δ := -(b0 + b1 + 2 * cc * b3) / 4 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  set A := (b0 + δ) / D with hAdef
  set B := (b1 + δ) / D with hBdef
  have hA : D * A = b0 + δ := by rw [hAdef]; field_simp
  have hB : D * B = b1 + δ := by rw [hBdef]; field_simp
  refine ⟨(A - (cc - 1 / 2) * B) • U i + (B - (cc - 1 / 2) * A) • U (i + 1), ?_, ?_, ?_⟩
  · have : E i ((A - (cc - 1 / 2) * B) • U i + (B - (cc - 1 / 2) * A) • U (i + 1)) = D * A := by
      rw [E_add, E_smul, E_smul, gram, gram, e1, e2, G0, G1, hDdef]; ((try ring_nf) <;> (try simp only [cc_sq, ss_sq, cc3, cc4, ss3, ss4]) <;> (try ring_nf) <;> (try simp only [cc_sq, ss_sq, cc3, cc4, ss3, ss4]) <;> (try ring_nf) <;> (try simp only [cc_sq, ss_sq, cc3, cc4, ss3, ss4]) <;> (try ring_nf))
    linarith
  · have : E (i + 1) ((A - (cc - 1 / 2) * B) • U i + (B - (cc - 1 / 2) * A) • U (i + 1)) =
        D * B := by
      rw [E_add, E_smul, E_smul, gram, gram, e3, e4, G0, G4, hDdef]; ((try ring_nf) <;> (try simp only [cc_sq, ss_sq, cc3, cc4, ss3, ss4]) <;> (try ring_nf) <;> (try simp only [cc_sq, ss_sq, cc3, cc4, ss3, ss4]) <;> (try ring_nf) <;> (try simp only [cc_sq, ss_sq, cc3, cc4, ss3, ss4]) <;> (try ring_nf))
    linarith
  · have : 2 * cc * E (i + 3) ((A - (cc - 1 / 2) * B) • U i + (B - (cc - 1 / 2) * A) • U (i + 1)) =
        -(D * A + D * B) := by
      rw [E_add, E_smul, E_smul, gram, gram, e5, e6, G2, G3, hDdef]; ((try ring_nf) <;> (try simp only [cc_sq, ss_sq, cc3, cc4, ss3, ss4]) <;> (try ring_nf) <;> (try simp only [cc_sq, ss_sq, cc3, cc4, ss3, ss4]) <;> (try ring_nf) <;> (try simp only [cc_sq, ss_sq, cc3, cc4, ss3, ss4]) <;> (try ring_nf))
    rw [hA, hB] at this
    nlinarith

lemma triples : ∀ I : Finset (Fin 5), I.card ≤ 3 →
    ∃ i : Fin 5, I ⊆ {i, i + 1, i + 2} ∨ I ⊆ {i, i + 1, i + 3} := by
  decide

lemma helly_pent (b : Fin 5 → ℝ) (hC : ∀ i, b i + b (i + 1) + 2 * cc * b (i + 3) < 0) :
    ∃ t : Position 2, ∀ i, b i < E i t := by
  have h := Convex.helly_theorem' (𝕜 := ℝ) (F := fun i => {t : Position 2 | b i < E i t})
    (s := Finset.univ) (fun i _ => convex_E_gt i (b i)) ?_
  · obtain ⟨t, ht⟩ := h
    simp only [Set.mem_iInter] at ht
    exact ⟨t, fun i => ht i (Finset.mem_univ i)⟩
  · intro I _ hI
    rw [finrank_euclideanSpace_fin] at hI
    obtain ⟨i, hsub | hsub⟩ := triples I hI
    · obtain ⟨t, h0, h1, h2⟩ := wit1 i (b i) (b (i + 1)) (b (i + 2))
      refine ⟨t, Set.mem_iInter₂.mpr (fun j hj => ?_)⟩
      have := hsub hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with rfl | rfl | rfl <;> assumption
    · obtain ⟨t, h0, h1, h3⟩ := wit2 i (b i) (b (i + 1)) (b (i + 3)) (hC i)
      refine ⟨t, Set.mem_iInter₂.mpr (fun j hj => ?_)⟩
      have := hsub hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with rfl | rfl | rfl <;> assumption

/-- The circuit `u_i + u_{i+1} = -2c u_{i+3}`. -/
lemma circ (x : Position 2) (i : Fin 5) : P x (i + 2) - P x i = -(2 * cc) * E (i + 3) x := by
  have h1 := circX i; have h2 := circY i
  have e : i + 3 + 1 = i + 4 := by rw [add_assoc]; rfl
  simp only [E, e, P]
  linear_combination x 0 * h2 - x 1 * h1

/-- The constant `c₀` in the coordinates. -/
noncomputable def c0 : ℝ := 2 * s1 * (1 + cc)

/-- Farkas–Helly: a polygon all of whose combinations `Ψ` are below `c₀` translates into `int K`. -/
theorem translatable {m : ℕ} (q : Fin m → Position 2)
    (h : ∀ (i : Fin 5) (j1 j2 j3 : Fin m), Psi (fun j k => P (q j) k) i j1 j2 j3 < c0) :
    ∃ t : Position 2, ∀ j, q j ∈ interior pentagonK + ({t} : Set (Position 2)) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; exact ⟨0, fun j => j.elim0⟩
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  set M : Fin 5 → ℝ := fun i => Finset.univ.sup' hne (fun j => E i (q j)) with hM
  have hJ : ∀ i, ∃ j, M i = E i (q j) := fun i => by
    obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' hne (fun j => E i (q j))
    exact ⟨j, hj⟩
  choose J hJ using hJ
  have hle : ∀ i j, E i (q j) ≤ M i := fun i j =>
    Finset.le_sup' (fun j => E i (q j)) (Finset.mem_univ j)
  have hC : ∀ i, (M i - s1) + (M (i + 1) - s1) + 2 * cc * (M (i + 3) - s1) < 0 := by
    intro i
    have h1 := h i (J i) (J (i + 1)) (J (i + 3))
    simp only [Psi] at h1
    rw [circ] at h1
    have e1 : P (q (J i)) (i + 1) - P (q (J i)) i = M i := by rw [hJ i]; rfl
    have e2 : P (q (J (i + 1))) (i + 2) - P (q (J (i + 1))) (i + 1) = M (i + 1) := by
      rw [hJ (i + 1)]; simp only [E, show i + 1 + 1 = i + 2 by rw [add_assoc]; rfl]
    rw [e1, e2, ← hJ (i + 3)] at h1
    unfold c0 at h1
    linarith
  obtain ⟨t, ht⟩ := helly_pent (fun i => M i - s1) hC
  refine ⟨t, fun j => ?_⟩
  rw [Set.add_singleton]
  refine ⟨q j - t, mem_interior_K _ (fun i => ?_), sub_add_cancel _ _⟩
  rw [E_sub]
  have h1 : M i - s1 < E i t := ht i
  have h2 := hle i j
  linarith

/-! ## The lower bound -/

lemma Psi_le_length (m : ℕ) (hm : m ≤ 3) (q : Fin m → Position 2) (i : Fin 5) (j1 j2 j3 : Fin m) :
    Psi (fun j k => P (q j) k) i j1 j2 j3 < c0 ∨
      Psi (fun j k => P (q j) k) i j1 j2 j3 ≤ polygonLength pentagonT q := by
  interval_cases m
  · exact j1.elim0
  · left
    have h1 : j1 = 0 := Subsingleton.elim _ _
    have h2 : j2 = 0 := Subsingleton.elim _ _
    have h3 : j3 = 0 := Subsingleton.elim _ _
    subst h1 h2 h3
    have : Psi (fun j k => P (q j) k) i 0 0 0 = 0 := by simp only [Psi]; ring
    rw [this]; unfold c0; have := s1_pos; have := cc_bounds; nlinarith
  · right
    rw [length2]
    exact core2 (fun j k => P (q j) k) _ _ (P_sum (q 0)) (P_sum (q 1))
      (fun k => hT_ge_sub (q 1) (q 0) k) (fun k => hT_ge2_sub (q 1) (q 0) k)
      (fun k => hT_ge_sub (q 0) (q 1) k) (fun k => hT_ge2_sub (q 0) (q 1) k) i j1 j2 j3
  · right
    rw [length3]
    exact core3 (fun j k => P (q j) k) _ _ _ (P_sum (q 0)) (P_sum (q 1)) (P_sum (q 2))
      (fun k => hT_ge_sub (q 1) (q 0) k) (fun k => hT_ge2_sub (q 1) (q 0) k)
      (fun k => hT_ge_sub (q 2) (q 1) k) (fun k => hT_ge2_sub (q 2) (q 1) k)
      (fun k => hT_ge_sub (q 0) (q 2) k) (fun k => hT_ge2_sub (q 0) (q 2) k) i j1 j2 j3

/-- **Part B**: the lower bound `c₀ ≤ T°-length` for polygons with at most three vertices that
cannot be translated into the interior of `K`. -/
theorem lower_bound (m : ℕ) (q : Fin m → Position 2) (hm : m ≤ 3)
    (hq : NotTranslatableIntoInterior pentagonK q) :
    2 * Real.cos (Real.pi / 10) * (1 + Real.cos (Real.pi / 5)) ≤ polygonLength pentagonT q := by
  have hc0 : 2 * Real.cos (Real.pi / 10) * (1 + Real.cos (Real.pi / 5)) = c0 := by
    rw [c0_eq]; rfl
  rw [hc0]
  by_contra hlt
  replace hlt := not_le.mp hlt
  obtain ⟨t, ht⟩ := translatable q (fun i j1 j2 j3 => by
    rcases Psi_le_length m hm q i j1 j2 j3 with h | h
    · exact h
    · linarith)
  exact hq t ht

end Viterbo.PentB

end
end

section
section
namespace Viterbo.IsLeastFinal
open Viterbo

theorem main :
    IsLeast {L : ℝ | ∃ (m : ℕ) (q : Fin m → OAI.SymmetricPolar.Position 2), m ≤ 3 ∧
        NotTranslatableIntoInterior pentagonK q ∧ L = polygonLength pentagonT q}
      (2 * Real.cos (Real.pi / 10) * (1 + Real.cos (Real.pi / 5))) ∧
    ∀ k : ℕ, k < 5 →
      IsClosedBilliard pentagonK pentagonT ![pentagonVertex k, pentagonVertex (k + 2)] ∧
      polygonLength pentagonT ![pentagonVertex k, pentagonVertex (k + 2)] =
        2 * Real.cos (Real.pi / 10) * (1 + Real.cos (Real.pi / 5)) := by
  refine ⟨⟨Viterbo.PentA.witness, ?_⟩, fun k hk => Viterbo.PentA.diag_billiard k hk⟩
  rintro L ⟨m, q, hm, hq, rfl⟩
  exact Viterbo.PentB.lower_bound m q hm hq

end Viterbo.IsLeastFinal

theorem Viterbo.isLeast_polygonLength_pentagon_and_diagonal_isClosedBilliard :
    IsLeast {L : ℝ | ∃ (m : ℕ) (q : Fin m → OAI.SymmetricPolar.Position 2), m ≤ 3 ∧
        Viterbo.NotTranslatableIntoInterior Viterbo.pentagonK q ∧ L = Viterbo.polygonLength Viterbo.pentagonT q}
      (2 * Real.cos (Real.pi / 10) * (1 + Real.cos (Real.pi / 5))) ∧
    ∀ k : ℕ, k < 5 →
      Viterbo.IsClosedBilliard Viterbo.pentagonK Viterbo.pentagonT ![Viterbo.pentagonVertex k, Viterbo.pentagonVertex (k + 2)] ∧
      Viterbo.polygonLength Viterbo.pentagonT ![Viterbo.pentagonVertex k, Viterbo.pentagonVertex (k + 2)] =
        2 * Real.cos (Real.pi / 10) * (1 + Real.cos (Real.pi / 5)) :=
  Viterbo.IsLeastFinal.main

end
end

section
open Viterbo

theorem solution :
    IsLeast {L : ℝ | ∃ (m : ℕ) (q : Fin m → OAI.SymmetricPolar.Position 2), m ≤ 3 ∧
        NotTranslatableIntoInterior pentagonK q ∧ L = polygonLength pentagonT q}
      (2 * Real.cos (Real.pi / 10) * (1 + Real.cos (Real.pi / 5))) ∧
    ∀ k : ℕ, k < 5 →
      IsClosedBilliard pentagonK pentagonT ![pentagonVertex k, pentagonVertex (k + 2)] ∧
      polygonLength pentagonT ![pentagonVertex k, pentagonVertex (k + 2)] =
        2 * Real.cos (Real.pi / 10) * (1 + Real.cos (Real.pi / 5)) := by
  apply Viterbo.isLeast_polygonLength_pentagon_and_diagonal_isClosedBilliard <;> assumption

end
