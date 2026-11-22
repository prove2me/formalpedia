-- Prove2me | solution 1 for QualityEncroach.Differ.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T19:22:53.690082+00:00
-- url     : https://prove2.me/submissions/d002bff1-66bd-4db9-a307-dfe8296310c4

import Mathlib
import Definitions.Def_QualityEncroach_Differ_Game

namespace QualityEncroachProp3

open QualityEncroach.Differ

/-! ## Section 1: Dyadic integer Bernstein positivity checker -/

private def sumZ : ℕ → (ℕ → ℤ) → ℤ
  | 0, _ => 0
  | n + 1, f => sumZ n f + f n

private def allNat : ℕ → (ℕ → Bool) → Bool
  | 0, _ => true
  | n + 1, f => allNat n f && f n

private lemma allNat_true_iff {n : ℕ} {f : ℕ → Bool} :
    allNat n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => simp [allNat]
  | succ n ih =>
    simp only [allNat, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
      · exact h1 i h
      · exact h2
    · intro h
      exact ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), h n (Nat.lt_succ_self n)⟩

private lemma sumZ_cast (n : ℕ) (f : ℕ → ℤ) :
    (sumZ n f : ℝ) = ∑ i ∈ Finset.range n, (f i : ℝ) := by
  induction n with
  | zero => simp [sumZ]
  | succ n ih =>
    simp only [sumZ, Int.cast_add, ih, Finset.sum_range_succ]

private def c1 (d i : ℕ) (iu : ℤ) (r : ℕ) : ℤ :=
  sumZ (i + 1) fun a =>
    if a ≤ r then
      (Nat.choose i a : ℤ) * (iu + 1) ^ a * iu ^ (i - a) * (Nat.choose (d - i) (r - a) : ℤ)
    else 0

private lemma monomial_bern_1d (d i : ℕ) (hi : i ≤ d) (iu : ℤ) (x : ℝ) :
    ((iu : ℝ) + x) ^ i =
      ∑ r ∈ Finset.range (d + 1), (c1 d i iu r : ℝ) * x ^ r * (1 - x) ^ (d - r) := by
  have h1 : ((iu : ℝ) + x) ^ i =
      (((iu : ℝ) + 1) * x + (iu : ℝ) * (1 - x)) ^ i * (x + (1 - x)) ^ (d - i) := by
    have hx : x + (1 - x) = 1 := by ring
    rw [hx, one_pow, mul_one]
    congr 1
    ring
  rw [h1, add_pow, add_pow]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  have h2 :
      ∑ r ∈ Finset.range (d + 1), (c1 d i iu r : ℝ) * x ^ r * (1 - x) ^ (d - r) =
      ∑ a ∈ Finset.range (i + 1),
        ∑ r ∈ Finset.range (d + 1),
          (if a ≤ r then
            ((Nat.choose i a : ℝ) * ((iu : ℝ) + 1) ^ a * (iu : ℝ) ^ (i - a) *
              (Nat.choose (d - i) (r - a) : ℝ))
          else 0) * x ^ r * (1 - x) ^ (d - r) := by
    conv_lhs =>
      arg 2
      ext r
      rw [c1, sumZ_cast, Finset.sum_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun r _ => ?_
    split_ifs <;> push_cast <;> ring
  rw [h2]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hai : a ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
  have hsub : ∀ b ∈ Finset.range (d - i + 1), a + b ∈ Finset.range (d + 1) := by
    intro b hb
    have hbd : b ≤ d - i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    exact Finset.mem_range.mpr (by omega)
  refine Finset.sum_of_injOn (fun b => a + b)
    (fun b1 _ b2 _ h => Nat.add_left_cancel h)
    hsub
    (fun r hr hnot => ?_)
    (fun b hb => ?_)
  · by_cases har : a ≤ r
    · have hgt : d - i < r - a := by
        by_contra hle
        push Not at hle
        apply hnot
        refine ⟨r - a, Finset.mem_range.mpr (by omega), by dsimp; omega⟩
      simp [har, Nat.choose_eq_zero_of_lt hgt]
    · simp [har]
  · have hbd : b ≤ d - i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    have har : a ≤ a + b := Nat.le_add_right a b
    have hsub1 : a + b - a = b := Nat.add_sub_cancel_left a b
    have hsub2 : d - (a + b) = (i - a) + (d - i - b) := by omega
    simp only [har, ↓reduceIte, hsub1, hsub2, pow_add, mul_pow]
    ring

private def evalSparse : List (ℕ × ℕ × ℤ) → ℝ → ℝ → ℝ
  | [], _, _ => 0
  | (i, j, coeff) :: rest, u, v => (coeff : ℝ) * u ^ i * v ^ j + evalSparse rest u v

private def bernCoeff2D (dx dy ku : ℕ) (iu : ℤ) (kv : ℕ) (iv : ℤ) :
    List (ℕ × ℕ × ℤ) → ℕ → ℕ → ℤ
  | [], _, _ => 0
  | (i, j, coeff) :: rest, r, s =>
    coeff * ((2 : ℤ) ^ ((dx - i) * ku + (dy - j) * kv)) * c1 dx i iu r * c1 dy j iv s +
      bernCoeff2D dx dy ku iu kv iv rest r s

private def polyDegLe (dx dy : ℕ) : List (ℕ × ℕ × ℤ) → Prop
  | [] => True
  | (i, j, _) :: rest => i ≤ dx ∧ j ≤ dy ∧ polyDegLe dx dy rest

private lemma evalSparse_eq_bern (dx dy ku : ℕ) (iu : ℤ) (kv : ℕ) (iv : ℤ)
    (P : List (ℕ × ℕ × ℤ)) (hP : polyDegLe dx dy P) (u v : ℝ) :
    let x : ℝ := (2 : ℝ) ^ ku * u - (iu : ℝ)
    let y : ℝ := (2 : ℝ) ^ kv * v - (iv : ℝ)
    (2 : ℝ) ^ (dx * ku + dy * kv) * evalSparse P u v =
      ∑ r ∈ Finset.range (dx + 1), ∑ s ∈ Finset.range (dy + 1),
        (bernCoeff2D dx dy ku iu kv iv P r s : ℝ) *
          x ^ r * (1 - x) ^ (dx - r) * y ^ s * (1 - y) ^ (dy - s) := by
  intro x y
  induction P with
  | nil =>
    simp [evalSparse, bernCoeff2D]
  | cons hd tl ih =>
    rcases hd with ⟨i, j, coeff⟩
    rcases hP with ⟨hi, hj, htl⟩
    simp only [evalSparse, bernCoeff2D, mul_add]
    rw [ih htl]
    have hsplit :
        ∑ r ∈ Finset.range (dx + 1), ∑ s ∈ Finset.range (dy + 1),
          ((coeff * 2 ^ ((dx - i) * ku + (dy - j) * kv) * c1 dx i iu r * c1 dy j iv s +
              bernCoeff2D dx dy ku iu kv iv tl r s : ℤ) : ℝ) *
            x ^ r * (1 - x) ^ (dx - r) * y ^ s * (1 - y) ^ (dy - s) =
        (∑ r ∈ Finset.range (dx + 1), ∑ s ∈ Finset.range (dy + 1),
          ((coeff : ℝ) * (2 : ℝ) ^ ((dx - i) * ku + (dy - j) * kv) *
              (c1 dx i iu r : ℝ) * (c1 dy j iv s : ℝ)) *
            x ^ r * (1 - x) ^ (dx - r) * y ^ s * (1 - y) ^ (dy - s)) +
        (∑ r ∈ Finset.range (dx + 1), ∑ s ∈ Finset.range (dy + 1),
          (bernCoeff2D dx dy ku iu kv iv tl r s : ℝ) *
            x ^ r * (1 - x) ^ (dx - r) * y ^ s * (1 - y) ^ (dy - s)) := by
      simp_rw [Int.cast_add, add_mul, Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
      push_cast
      ring
    rw [hsplit]
    congr 1
    have hu : (iu : ℝ) + x = (2 : ℝ) ^ ku * u := by simp [x]
    have hv : (iv : ℝ) + y = (2 : ℝ) ^ kv * v := by simp [y]
    have hmonu := monomial_bern_1d dx i hi iu x
    have hmonv := monomial_bern_1d dy j hj iv y
    rw [hu] at hmonu
    rw [hv] at hmonv
    have hpow : (2 : ℝ) ^ (dx * ku + dy * kv) * ((coeff : ℝ) * u ^ i * v ^ j) =
        (coeff : ℝ) * (2 : ℝ) ^ ((dx - i) * ku + (dy - j) * kv) *
          (((2 : ℝ) ^ ku * u) ^ i * ((2 : ℝ) ^ kv * v) ^ j) := by
      have h1 : dx * ku = (dx - i) * ku + i * ku := by
        rw [← Nat.add_mul, Nat.sub_add_cancel hi]
      have h2 : dy * kv = (dy - j) * kv + j * kv := by
        rw [← Nat.add_mul, Nat.sub_add_cancel hj]
      rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]
      rw [h1, h2]
      simp only [pow_add]
      ring
    rw [hpow, hmonu, hmonv]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    refine Finset.sum_congr rfl fun s _ => ?_
    ring

private def allBernPos (dx dy ku : ℕ) (iu : ℤ) (kv : ℕ) (iv : ℤ)
    (P : List (ℕ × ℕ × ℤ)) : Bool :=
  allNat (dx + 1) fun r =>
    allNat (dy + 1) fun s =>
      decide (0 < bernCoeff2D dx dy ku iu kv iv P r s)

private def allBernNonneg (dx dy ku : ℕ) (iu : ℤ) (kv : ℕ) (iv : ℤ)
    (P : List (ℕ × ℕ × ℤ)) : Bool :=
  allNat (dx + 1) fun r =>
    allNat (dy + 1) fun s =>
      decide (0 ≤ bernCoeff2D dx dy ku iu kv iv P r s)

private lemma exists_bern_basis_pos (d : ℕ) (x : ℝ) (_hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∃ r ∈ Finset.range (d + 1), 0 < x ^ r * (1 - x) ^ (d - r) := by
  by_cases h : x < 1
  · refine ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ d), ?_⟩
    have h1 : 0 < 1 - x := by linarith
    simp only [pow_zero, one_mul, Nat.sub_zero]
    positivity
  · have hx : x = 1 := le_antisymm hx1 (not_lt.mp h)
    refine ⟨d, Finset.mem_range.mpr (Nat.lt_succ_self d), ?_⟩
    simp [hx]

private lemma evalSparse_pos_of_allBernPos (dx dy ku : ℕ) (iu : ℤ) (kv : ℕ) (iv : ℤ)
    (P : List (ℕ × ℕ × ℤ)) (hP : polyDegLe dx dy P)
    (hcheck : allBernPos dx dy ku iu kv iv P = true)
    (u v : ℝ)
    (hu0 : (iu : ℝ) ≤ (2 : ℝ) ^ ku * u) (hu1 : (2 : ℝ) ^ ku * u ≤ (iu : ℝ) + 1)
    (hv0 : (iv : ℝ) ≤ (2 : ℝ) ^ kv * v) (hv1 : (2 : ℝ) ^ kv * v ≤ (iv : ℝ) + 1) :
    0 < evalSparse P u v := by
  have hcoeff : ∀ r < dx + 1, ∀ s < dy + 1, 0 < bernCoeff2D dx dy ku iu kv iv P r s := by
    intro r hr s hs
    have h1 := (allNat_true_iff.mp hcheck) r hr
    have h2 := (allNat_true_iff.mp h1) s hs
    exact of_decide_eq_true h2
  set x : ℝ := (2 : ℝ) ^ ku * u - (iu : ℝ)
  set y : ℝ := (2 : ℝ) ^ kv * v - (iv : ℝ)
  have hx0 : 0 ≤ x := by linarith
  have hx1 : x ≤ 1 := by linarith
  have hy0 : 0 ≤ y := by linarith
  have hy1 : y ≤ 1 := by linarith
  have h1x : 0 ≤ 1 - x := by linarith
  have h1y : 0 ≤ 1 - y := by linarith
  have h2pow : (0 : ℝ) < (2 : ℝ) ^ (dx * ku + dy * kv) := by positivity
  suffices hsum : 0 < (2 : ℝ) ^ (dx * ku + dy * kv) * evalSparse P u v by
    nlinarith
  rw [evalSparse_eq_bern dx dy ku iu kv iv P hP u v]
  obtain ⟨r0, hr0, hxr0⟩ := exists_bern_basis_pos dx x hx0 hx1
  obtain ⟨s0, hs0, hys0⟩ := exists_bern_basis_pos dy y hy0 hy1
  have hterm_nn : ∀ r ∈ Finset.range (dx + 1), ∀ s ∈ Finset.range (dy + 1),
      0 ≤ (bernCoeff2D dx dy ku iu kv iv P r s : ℝ) *
        x ^ r * (1 - x) ^ (dx - r) * y ^ s * (1 - y) ^ (dy - s) := by
    intro r hr s hs
    have hc : (0 : ℝ) < (bernCoeff2D dx dy ku iu kv iv P r s : ℝ) := by
      exact_mod_cast hcoeff r (Finset.mem_range.mp hr) s (Finset.mem_range.mp hs)
    have : 0 ≤ x ^ r * (1 - x) ^ (dx - r) * y ^ s * (1 - y) ^ (dy - s) := by positivity
    nlinarith [mul_nonneg hc.le this]
  have hterm_pos :
      0 < (bernCoeff2D dx dy ku iu kv iv P r0 s0 : ℝ) *
        x ^ r0 * (1 - x) ^ (dx - r0) * y ^ s0 * (1 - y) ^ (dy - s0) := by
    have hc : (0 : ℝ) < (bernCoeff2D dx dy ku iu kv iv P r0 s0 : ℝ) := by
      exact_mod_cast hcoeff r0 (Finset.mem_range.mp hr0) s0 (Finset.mem_range.mp hs0)
    have hprod : 0 < (x ^ r0 * (1 - x) ^ (dx - r0)) * (y ^ s0 * (1 - y) ^ (dy - s0)) :=
      mul_pos hxr0 hys0
    have hrew : (bernCoeff2D dx dy ku iu kv iv P r0 s0 : ℝ) *
        x ^ r0 * (1 - x) ^ (dx - r0) * y ^ s0 * (1 - y) ^ (dy - s0) =
        (bernCoeff2D dx dy ku iu kv iv P r0 s0 : ℝ) *
          ((x ^ r0 * (1 - x) ^ (dx - r0)) * (y ^ s0 * (1 - y) ^ (dy - s0))) := by ring
    rw [hrew]
    exact mul_pos hc hprod
  refine Finset.sum_pos' (fun r hr => Finset.sum_nonneg (hterm_nn r hr)) ⟨r0, hr0, ?_⟩
  exact Finset.sum_pos' (hterm_nn r0 hr0) ⟨s0, hs0, hterm_pos⟩

private lemma evalSparse_nonneg_of_allBernNonneg (dx dy ku : ℕ) (iu : ℤ) (kv : ℕ) (iv : ℤ)
    (P : List (ℕ × ℕ × ℤ)) (hP : polyDegLe dx dy P)
    (hcheck : allBernNonneg dx dy ku iu kv iv P = true)
    (u v : ℝ)
    (hu0 : (iu : ℝ) ≤ (2 : ℝ) ^ ku * u) (hu1 : (2 : ℝ) ^ ku * u ≤ (iu : ℝ) + 1)
    (hv0 : (iv : ℝ) ≤ (2 : ℝ) ^ kv * v) (hv1 : (2 : ℝ) ^ kv * v ≤ (iv : ℝ) + 1) :
    0 ≤ evalSparse P u v := by
  have hcoeff : ∀ r < dx + 1, ∀ s < dy + 1, 0 ≤ bernCoeff2D dx dy ku iu kv iv P r s := by
    intro r hr s hs
    have h1 := (allNat_true_iff.mp hcheck) r hr
    have h2 := (allNat_true_iff.mp h1) s hs
    exact of_decide_eq_true h2
  set x : ℝ := (2 : ℝ) ^ ku * u - (iu : ℝ)
  set y : ℝ := (2 : ℝ) ^ kv * v - (iv : ℝ)
  have hx0 : 0 ≤ x := by linarith
  have hx1 : x ≤ 1 := by linarith
  have hy0 : 0 ≤ y := by linarith
  have hy1 : y ≤ 1 := by linarith
  have h1x : 0 ≤ 1 - x := by linarith
  have h1y : 0 ≤ 1 - y := by linarith
  have h2pow : (0 : ℝ) < (2 : ℝ) ^ (dx * ku + dy * kv) := by positivity
  suffices hsum : 0 ≤ (2 : ℝ) ^ (dx * ku + dy * kv) * evalSparse P u v by
    nlinarith
  rw [evalSparse_eq_bern dx dy ku iu kv iv P hP u v]
  refine Finset.sum_nonneg fun r hr => Finset.sum_nonneg fun s hs => ?_
  have hc : (0 : ℝ) ≤ (bernCoeff2D dx dy ku iu kv iv P r s : ℝ) := by
    exact_mod_cast hcoeff r (Finset.mem_range.mp hr) s (Finset.mem_range.mp hs)
  have hxy : 0 ≤ x ^ r * (1 - x) ^ (dx - r) * y ^ s * (1 - y) ^ (dy - s) := by positivity
  nlinarith [mul_nonneg hc hxy]

/-! ### The three explicit sparse polynomials and the dyadic tree -/

private def PQ_poly : List (ℕ × ℕ × ℤ) :=
  [(1, 0, 302), (1, 1, -1464), (2, 0, -9), (1, 2, 9592), (2, 1, -9260),
   (3, 0, 3164), (1, 3, -53200), (2, 2, 70300), (3, 1, -36400), (4, 0, 5600),
   (1, 4, 100800), (2, 3, -168000), (3, 2, 137200), (4, 1, -56000), (5, 0, 11200),
   (0, 2, -2000), (0, 3, 12000), (0, 4, -18000)]

private def negC4_poly : List (ℕ × ℕ × ℤ) :=
  [(0, 1, -4), (1, 0, 1), (0, 2, 12), (1, 1, -10), (2, 0, 4)]

private def negQM_poly : List (ℕ × ℕ × ℤ) :=
  [(1, 0, -3), (0, 1, 4), (0, 2, -12), (1, 1, 6)]

private lemma PQ_poly_deg : polyDegLe 5 4 PQ_poly := by
  simp [PQ_poly, polyDegLe]

private lemma negC4_poly_deg : polyDegLe 2 2 negC4_poly := by
  simp [negC4_poly, polyDegLe]

private lemma negQM_poly_deg : polyDegLe 1 2 negQM_poly := by
  simp [negQM_poly, polyDegLe]

private noncomputable def Qpoly (c : ℝ) : ℝ :=
  151 / 4000 - 77 / 250 * c + 7 / 5 * c ^ 2

private noncomputable def cUV (u v : ℝ) : ℝ :=
  (4 * v - u - 12 * v ^ 2 + 10 * u * v - 4 * u ^ 2) / 4

private noncomputable def PiLuv (u v : ℝ) : ℝ :=
  (4 * v - u - 4 * v ^ 2 + 2 * u * v) * (1 - 2 * v) / 16 +
    (3 * u - 4 * v + 12 * v ^ 2 - 6 * u * v) ^ 2 / (64 * u)

private lemma eval_negC4 (u v : ℝ) :
    evalSparse negC4_poly u v = -(4 * v - u - 12 * v ^ 2 + 10 * u * v - 4 * u ^ 2) := by
  simp [negC4_poly, evalSparse]
  ring

private lemma eval_negQM (u v : ℝ) :
    evalSparse negQM_poly u v = -(3 * u - 4 * v + 12 * v ^ 2 - 6 * u * v) := by
  simp [negQM_poly, evalSparse]
  ring

private lemma eval_PQ (u v : ℝ) (hu : u ≠ 0) :
    evalSparse PQ_poly u v = 8000 * u * (Qpoly (cUV u v) - PiLuv u v) := by
  simp only [PQ_poly, evalSparse, Qpoly, cUV, PiLuv]
  field_simp [hu]
  ring

private inductive BoxTree
  | uSmall
  | uv
  | lin12v
  | negC4
  | negQM
  | okPQ
  | splitU (l r : BoxTree)
  | splitV (l r : BoxTree)

private def checkTree (ku : ℕ) (iu : ℤ) (kv : ℕ) (iv : ℤ) : BoxTree → Bool
  | .uSmall => decide ((iu + 1) * 64 ≤ (2 : ℤ) ^ ku)
  | .uv => decide (iu * (2 : ℤ) ^ kv ≥ (iv + 1) * (2 : ℤ) ^ ku)
  | .lin12v =>
      decide (12 * (iv + 1) * (2 : ℤ) ^ ku < 5 * iu * (2 : ℤ) ^ kv + 2 * (2 : ℤ) ^ (ku + kv))
  | .negC4 => allBernPos 2 2 ku iu kv iv negC4_poly
  | .negQM => allBernNonneg 1 2 ku iu kv iv negQM_poly
  | .okPQ => allBernPos 5 4 ku iu kv iv PQ_poly
  | .splitU l r => checkTree (ku + 1) (2 * iu) kv iv l && checkTree (ku + 1) (2 * iu + 1) kv iv r
  | .splitV l r => checkTree ku iu (kv + 1) (2 * iv) l && checkTree ku iu (kv + 1) (2 * iv + 1) r

private lemma checkTree_sound (ku : ℕ) (iu : ℤ) (kv : ℕ) (iv : ℤ) (T : BoxTree)
    (hT : checkTree ku iu kv iv T = true)
    (u v : ℝ)
    (hu0 : (iu : ℝ) ≤ (2 : ℝ) ^ ku * u) (hu1 : (2 : ℝ) ^ ku * u ≤ (iu : ℝ) + 1)
    (hv0 : (iv : ℝ) ≤ (2 : ℝ) ^ kv * v) (hv1 : (2 : ℝ) ^ kv * v ≤ (iv : ℝ) + 1)
    (hu_big : 1 / 64 < u) (huv : u < v) (h12v : 5 * u + 2 ≤ 12 * v)
    (hc4 : 0 ≤ 4 * v - u - 12 * v ^ 2 + 10 * u * v - 4 * u ^ 2)
    (hqM : 0 < 3 * u - 4 * v + 12 * v ^ 2 - 6 * u * v) :
    0 < evalSparse PQ_poly u v := by
  induction T generalizing ku iu kv iv with
  | uSmall =>
    have h := of_decide_eq_true (by simpa [checkTree] using hT)
    have hR : ((iu : ℝ) + 1) * 64 ≤ (2 : ℝ) ^ ku := by exact_mod_cast h
    have h2k : (0 : ℝ) < (2 : ℝ) ^ ku := by positivity
    nlinarith
  | uv =>
    have h := of_decide_eq_true (by simpa [checkTree] using hT)
    have hR : ((iv : ℝ) + 1) * (2 : ℝ) ^ ku ≤ (iu : ℝ) * (2 : ℝ) ^ kv := by exact_mod_cast h
    have h2ku : (0 : ℝ) < (2 : ℝ) ^ ku := by positivity
    have h2kv : (0 : ℝ) < (2 : ℝ) ^ kv := by positivity
    have h1 : (2 : ℝ) ^ ku * ((2 : ℝ) ^ kv * v) ≤ ((iv : ℝ) + 1) * (2 : ℝ) ^ ku := by nlinarith
    have h2 : (iu : ℝ) * (2 : ℝ) ^ kv ≤ (2 : ℝ) ^ kv * ((2 : ℝ) ^ ku * u) := by nlinarith
    have h3 : (2 : ℝ) ^ ku * (2 : ℝ) ^ kv * v ≤ (2 : ℝ) ^ ku * (2 : ℝ) ^ kv * u := by linarith
    have hprod : (0 : ℝ) < (2 : ℝ) ^ ku * (2 : ℝ) ^ kv := mul_pos h2ku h2kv
    nlinarith
  | lin12v =>
    have h := of_decide_eq_true (by simpa [checkTree] using hT)
    have hR : 12 * ((iv : ℝ) + 1) * (2 : ℝ) ^ ku <
        5 * (iu : ℝ) * (2 : ℝ) ^ kv + 2 * (2 : ℝ) ^ (ku + kv) := by exact_mod_cast h
    have h2ku : (0 : ℝ) < (2 : ℝ) ^ ku := by positivity
    have h2kv : (0 : ℝ) < (2 : ℝ) ^ kv := by positivity
    have hpow : (2 : ℝ) ^ (ku + kv) = (2 : ℝ) ^ ku * (2 : ℝ) ^ kv := pow_add 2 ku kv
    rw [hpow] at hR
    have h1 : 12 * ((2 : ℝ) ^ kv * v) * (2 : ℝ) ^ ku ≤ 12 * ((iv : ℝ) + 1) * (2 : ℝ) ^ ku := by
      nlinarith
    have h2 : 5 * (iu : ℝ) * (2 : ℝ) ^ kv ≤ 5 * ((2 : ℝ) ^ ku * u) * (2 : ℝ) ^ kv := by
      nlinarith
    have h3 : (2 : ℝ) ^ ku * (2 : ℝ) ^ kv * (12 * v) <
        (2 : ℝ) ^ ku * (2 : ℝ) ^ kv * (5 * u + 2) := by linarith
    have hprod : (0 : ℝ) < (2 : ℝ) ^ ku * (2 : ℝ) ^ kv := mul_pos h2ku h2kv
    nlinarith
  | negC4 =>
    have hpos := evalSparse_pos_of_allBernPos 2 2 ku iu kv iv negC4_poly negC4_poly_deg
      (by simpa [checkTree] using hT) u v hu0 hu1 hv0 hv1
    rw [eval_negC4] at hpos
    linarith
  | negQM =>
    have hnn := evalSparse_nonneg_of_allBernNonneg 1 2 ku iu kv iv negQM_poly negQM_poly_deg
      (by simpa [checkTree] using hT) u v hu0 hu1 hv0 hv1
    rw [eval_negQM] at hnn
    linarith
  | okPQ =>
    exact evalSparse_pos_of_allBernPos 5 4 ku iu kv iv PQ_poly PQ_poly_deg
      (by simpa [checkTree] using hT) u v hu0 hu1 hv0 hv1
  | splitU l r ihl ihr =>
    simp only [checkTree, Bool.and_eq_true] at hT
    have h2 : (2 : ℝ) ^ (ku + 1) * u = 2 * ((2 : ℝ) ^ ku * u) := by
      rw [pow_succ]; ring
    rcases le_total ((2 : ℝ) ^ (ku + 1) * u) ((2 * iu + 1 : ℤ) : ℝ) with hle | hge
    · refine ihl (ku + 1) (2 * iu) kv iv hT.1 ?_ ?_ hv0 hv1
      · push_cast; linarith
      · push_cast at hle ⊢; linarith
    · refine ihr (ku + 1) (2 * iu + 1) kv iv hT.2 hge ?_ hv0 hv1
      push_cast; linarith
  | splitV l r ihl ihr =>
    simp only [checkTree, Bool.and_eq_true] at hT
    have h2 : (2 : ℝ) ^ (kv + 1) * v = 2 * ((2 : ℝ) ^ kv * v) := by
      rw [pow_succ]; ring
    rcases le_total ((2 : ℝ) ^ (kv + 1) * v) ((2 * iv + 1 : ℤ) : ℝ) with hle | hge
    · refine ihl ku iu (kv + 1) (2 * iv) hT.1 hu0 hu1 ?_ ?_
      · push_cast; linarith
      · push_cast at hle ⊢; linarith
    · refine ihr ku iu (kv + 1) (2 * iv + 1) hT.2 hu0 hu1 hge ?_
      push_cast; linarith

private def mainTree : BoxTree :=
  .splitU
    (.splitV
      (.splitU (.splitV .lin12v .negQM)
        (.splitV .uv
          (.splitU
            (.splitV .lin12v
              (.splitU .negQM
                (.splitV .lin12v
                  (.splitU (.splitV .negQM (.splitU .negQM .okPQ)) .okPQ))))
            .okPQ)))
      (.splitU
        (.splitV
          (.splitU
            (.splitV .negQM
              (.splitU
                (.splitV (.splitU .uSmall .okPQ)
                  (.splitU .uSmall (.splitV .okPQ .negC4)))
                .okPQ))
            (.splitV
              (.splitU
                (.splitV .negQM (.splitU (.splitV .negQM .okPQ) .okPQ))
                (.splitV .negQM .okPQ))
              .okPQ))
          (.splitU .negC4
            (.splitV (.splitU (.splitV .okPQ .negC4) .okPQ) .negC4)))
        (.splitV
          (.splitU
            (.splitV
              (.splitU
                (.splitV
                  (.splitU
                    (.splitV .negQM .okPQ)
                    (.splitV (.splitU .negQM (.splitV .negQM .okPQ)) .okPQ))
                  .okPQ)
                .okPQ)
              .okPQ)
            .okPQ)
          (.splitU (.splitV .okPQ .negC4)
            (.splitV .okPQ
              (.splitU (.splitV .okPQ .negC4) (.splitV .okPQ .negC4)))))))
    (.splitV .uv
      (.splitU
        (.splitV (.splitU (.splitV .okPQ .okPQ) (.splitV .uv .okPQ))
          (.splitU (.splitV .okPQ (.splitU (.splitV .okPQ .negC4) .okPQ)) .okPQ))
        (.splitV .uv .okPQ)))

private theorem mainTree_ok : checkTree 1 0 1 0 mainTree = true := by decide

private lemma PiLuv_lt_Qpoly (u v : ℝ)
    (hu : 0 < u) (huv : u < v) (hv : v < 1 / 2)
    (h12v : 5 * u + 2 ≤ 12 * v)
    (hc4 : 0 ≤ 4 * v - u - 12 * v ^ 2 + 10 * u * v - 4 * u ^ 2)
    (hqM : 0 < 3 * u - 4 * v + 12 * v ^ 2 - 6 * u * v) :
    PiLuv u v < Qpoly (cUV u v) := by
  by_cases hsmall : u ≤ 1 / 64
  · -- Elementary bound for tiny u ≤ 1/64
    have hsum : (3 * u - 4 * v + 12 * v ^ 2 - 6 * u * v) +
        (4 * v - u - 12 * v ^ 2 + 10 * u * v - 4 * u ^ 2) =
        2 * u * (1 + 2 * v - 2 * u) := by ring
    have hc_lt_u : cUV u v < u := by
      unfold cUV
      nlinarith
    have hc_nn : 0 ≤ cUV u v := by unfold cUV; linarith
    have hQ_lb : 32 / 1000 < Qpoly (cUV u v) := by
      unfold Qpoly
      have hsq : 0 ≤ (cUV u v) ^ 2 := sq_nonneg _
      nlinarith
    have hqM_ub : 3 * u - 4 * v + 12 * v ^ 2 - 6 * u * v ≤ 4 * u := by
      nlinarith
    have hqM_sq : (3 * u - 4 * v + 12 * v ^ 2 - 6 * u * v) ^ 2 / (64 * u) ≤ u / 4 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 64 * u)]
      nlinarith
    set x : ℝ := 1 - 2 * v
    have hx0 : 0 < x := by linarith
    have hx1 : x < 1 := by linarith
    have hcubic : x * (1 - x ^ 2) < 2 / 5 := by
      have hid : 2 / 5 - x * (1 - x ^ 2) =
          (x - 4 / 7) ^ 2 * (x + 8 / 7) + 1 / 49 * (1 - x) + 11 / 1715 := by ring
      have h1 : 0 ≤ (x - 4 / 7) ^ 2 * (x + 8 / 7) := by positivity
      linarith
    have hterm1 : (4 * v - u - 4 * v ^ 2 + 2 * u * v) * (1 - 2 * v) / 16 ≤ 1 / 40 := by
      have hid : (4 * v - u - 4 * v ^ 2 + 2 * u * v) * (1 - 2 * v) / 16 =
          x * (1 - x ^ 2) / 16 - u * x ^ 2 / 16 := by
        simp only [x]; ring
      have hux : 0 ≤ u * x ^ 2 / 16 := by positivity
      linarith
    unfold PiLuv
    linarith
  · push Not at hsmall
    have hPQ : 0 < evalSparse PQ_poly u v := by
      refine checkTree_sound 1 0 1 0 mainTree mainTree_ok u v ?_ ?_ ?_ ?_
        hsmall huv h12v hc4 hqM
      · norm_num; linarith
      · norm_num; linarith
      · norm_num; linarith
      · norm_num; linarith
    rw [eval_PQ u v hu.ne'] at hPQ
    nlinarith

/-! ## Section 2: Backward induction and SPE reduction for `k = 1` -/

private lemma quad_locmax_interval (f : ℝ → ℝ) (R α xs x0 δ : ℝ)
    (hα : 0 < α) (hδ : 0 < δ)
    (hf : ∀ x, f x = R - α * (x - xs) ^ 2)
    (hmax : ∀ x, |x - x0| < δ → f x ≤ f x0) :
    x0 = xs := by
  by_contra hne
  have hd : 0 < |xs - x0| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hne))
  set θ : ℝ := min (1 / 2) (δ / (2 * |xs - x0|))
  have hθ0 : 0 < θ := lt_min (by norm_num) (by positivity)
  have hθ1 : θ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hθ_le : θ ≤ δ / (2 * |xs - x0|) := min_le_right _ _
  set x : ℝ := x0 + θ * (xs - x0)
  have hdist : |x - x0| < δ := by
    have heq : x - x0 = θ * (xs - x0) := by ring
    rw [heq, abs_mul, abs_of_pos hθ0]
    have hle : θ * |xs - x0| ≤ δ / 2 := by
      calc θ * |xs - x0| ≤ (δ / (2 * |xs - x0|)) * |xs - x0| :=
            mul_le_mul_of_nonneg_right hθ_le hd.le
        _ = δ / 2 := by field_simp [hd.ne']
    linarith
  have hle := hmax x hdist
  rw [hf, hf] at hle
  have hsub : x - xs = (1 - θ) * (x0 - xs) := by simp [x]; ring
  rw [hsub, mul_pow] at hle
  have hsq : 0 < (x0 - xs) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  have h1θ : (1 - θ) ^ 2 < 1 := by nlinarith
  have h4 : (1 - θ) ^ 2 * (x0 - xs) ^ 2 < (x0 - xs) ^ 2 := by nlinarith
  have h5 := mul_lt_mul_of_pos_left h4 hα
  linarith

private lemma direct_eq {c : ℝ} {σ : Profile} (hσ : IsSPE 1 c (Set.Ioi 0) σ)
    (w u t q a : ℝ) (hu : 0 < u) (ht : 0 < t) (hq : 0 ≤ q)
    (hpM : ∀ qM, priceM u t qM q = u * (1 - qM - a * q)) :
    σ.direct w u t q = max 0 ((1 - a * q - c / u - u) / 2) := by
  set m := (1 - a * q - c / u - u) / 2 with hm
  have hF : ∀ x, mfrPayoff 1 c ⟨w, u, t, q, x⟩ =
      (w - (t * u) ^ 2) * q + (2 * u * m - u * x) * x := by
    intro x
    simp only [mfrPayoff, hpM, hm, one_mul]
    field_simp [hu.ne']
    ring
  have hd := hσ.1 w u t q hu ht hq
  have hd0 : 0 ≤ σ.direct w u t q := hd.1
  have hopt := hd.2 (max 0 m) (le_max_left _ _)
  simp only [Profile.outcomeAtDirect] at hopt
  rw [hF, hF] at hopt
  set d := σ.direct w u t q
  have key : u * (d - max 0 m) ^ 2 ≤ 0 := by
    rcases le_total 0 m with h | h
    · rw [max_eq_right h] at hopt ⊢; nlinarith
    · rw [max_eq_left h] at hopt ⊢
      nlinarith [mul_nonneg (mul_nonneg hu.le hd0) (neg_nonneg.mpr h)]
  have h2 : (d - max 0 m) ^ 2 ≤ 0 := by
    by_contra h; push Not at h; nlinarith
  have h3 := le_antisymm h2 (sq_nonneg _)
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp h3)

private lemma order_eq {c : ℝ} {σ : Profile} (hσ : IsSPE 1 c (Set.Ioi 0) σ)
    (u t q a γ : ℝ) (hu : 0 < u) (ht : 0 < t) (hq : 0 ≤ q)
    (hpM : ∀ qM x, priceM u t qM x = u * (1 - qM - a * x))
    (hpR : ∀ qM x, priceR u t qM x = t * u * (1 - x) - γ * qM)
    (hA : 0 < t * u - γ * a / 2) (hγ : 0 < γ)
    (hm : 0 ≤ (1 - a * q - c / u - u) / 2) :
    σ.order (t * u - γ * (1 - c / u - u) / 2 - 2 * (t * u - γ * a / 2) * q) u t = q := by
  set w := t * u - γ * (1 - c / u - u) / 2 - 2 * (t * u - γ * a / 2) * q with hw
  have hdir : ∀ x, 0 ≤ x → σ.direct w u t x = max 0 ((1 - a * x - c / u - u) / 2) :=
    fun x hx => direct_eq hσ w u t x a hu ht hx (fun qM => hpM qM x)
  have hord := hσ.2.1 w u t hu ht
  have hq' : 0 ≤ σ.order w u t := hord.1
  have hopt := hord.2 q hq
  simp only [Profile.outcomeAtOrder, Profile.outcomeAtDirect, retailerPayoff, hpR] at hopt
  set q' := σ.order w u t
  rw [hdir q hq, hdir q' hq', max_eq_right hm] at hopt
  have hle : (t * u * (1 - q') - γ * max 0 ((1 - a * q' - c / u - u) / 2) - w) * q' ≤
      (t * u * (1 - q') - γ * ((1 - a * q' - c / u - u) / 2) - w) * q' := by
    have hmax := le_max_right (0 : ℝ) ((1 - a * q' - c / u - u) / 2)
    nlinarith [mul_le_mul_of_nonneg_left hmax (mul_nonneg hγ.le hq')]
  have key : (t * u - γ * a / 2) * (q' - q) ^ 2 ≤ 0 := by
    rw [hw] at hopt hle
    nlinarith
  have h2 : (q' - q) ^ 2 ≤ 0 := by
    by_contra h; push Not at h; nlinarith
  have h3 := le_antisymm h2 (sq_nonneg _)
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp h3)

private lemma payoff_dev {c : ℝ} {σ : Profile} (hσ : IsSPE 1 c (Set.Ioi 0) σ)
    (u t q a γ : ℝ) (hu : 0 < u) (ht : 0 < t) (hq : 0 ≤ q)
    (hpM : ∀ qM x, priceM u t qM x = u * (1 - qM - a * x))
    (hpR : ∀ qM x, priceR u t qM x = t * u * (1 - x) - γ * qM)
    (hA : 0 < t * u - γ * a / 2) (hγ : 0 < γ)
    (hm : 0 ≤ (1 - a * q - c / u - u) / 2) :
    (t * u - γ * (1 - c / u - u) / 2 - 2 * (t * u - γ * a / 2) * q - (t * u) ^ 2) * q +
      u * ((1 - a * q - c / u - u) / 2) ^ 2 ≤ mfrPayoff 1 c σ.path := by
  set w := t * u - γ * (1 - c / u - u) / 2 - 2 * (t * u - γ * a / 2) * q with hw
  have hord : σ.order w u t = q := by
    rw [hw]; exact order_eq hσ u t q a γ hu ht hq hpM hpR hA hγ hm
  have hdir := direct_eq hσ w u t q a hu ht hq (fun qM => hpM qM q)
  have hfo := hσ.2.2.2.2 w u t hu ht
  simp only [Profile.outcomeAtOrder, Profile.outcomeAtDirect, hord, hdir, max_eq_right hm] at hfo
  have heq : mfrPayoff 1 c ⟨w, u, t, q, (1 - a * q - c / u - u) / 2⟩ =
      (w - (t * u) ^ 2) * q + u * ((1 - a * q - c / u - u) / 2) ^ 2 := by
    simp only [mfrPayoff, hpM, one_mul]
    field_simp [hu.ne']
    ring
  rw [heq] at hfo
  exact hfo

private lemma hi_pM (u t : ℝ) (ht : t ≤ 1) (qM qR : ℝ) :
    priceM u t qM qR = u * (1 - qM - t * qR) := by
  simp [priceM, ht]

private lemma hi_pR (u t : ℝ) (ht : t ≤ 1) (qM qR : ℝ) :
    priceR u t qM qR = t * u * (1 - qR) - (t * u) * qM := by
  simp only [priceR, ht, ↓reduceIte]
  ring

private lemma lo_pM (u t : ℝ) (ht : 1 < t) (qM qR : ℝ) :
    priceM u t qM qR = u * (1 - qM - 1 * qR) := by
  simp [priceM, not_le.mpr ht]

private lemma lo_pR (u t : ℝ) (ht : 1 < t) (qM qR : ℝ) :
    priceR u t qM qR = t * u * (1 - qR) - u * qM := by
  simp [priceR, not_le.mpr ht]

private noncomputable def PsiL (c u v q : ℝ) : ℝ :=
  (v - u / 2 + c / 2 + u ^ 2 / 2 - v ^ 2 - (2 * v - u) * q) * q +
    u * ((1 - q - c / u - u) / 2) ^ 2

private lemma payoff_dev_lo {c : ℝ} {σ : Profile} (hσ : IsSPE 1 c (Set.Ioi 0) σ)
    (u v q : ℝ) (hu : 0 < u) (huv : u < v) (hq : 0 ≤ q)
    (hm : 0 ≤ (1 - q - c / u - u) / 2) :
    PsiL c u v q ≤ mfrPayoff 1 c σ.path := by
  set t := v / u
  have ht1 : 1 < t := (one_lt_div hu).mpr huv
  have ht0 : 0 < t := lt_trans zero_lt_one ht1
  have htu : t * u = v := div_mul_cancel₀ v hu.ne'
  have hA : 0 < t * u - u * 1 / 2 := by rw [htu]; linarith
  have hdev := payoff_dev hσ u t q 1 u hu ht0 hq (lo_pM u t ht1) (lo_pR u t ht1) hA hu
    (by simpa using hm)
  have heq : PsiL c u v q =
      (t * u - u * (1 - c / u - u) / 2 - 2 * (t * u - u * 1 / 2) * q - (t * u) ^ 2) * q +
        u * ((1 - 1 * q - c / u - u) / 2) ^ 2 := by
    unfold PsiL
    rw [htu]
    field_simp [hu.ne']
    ring
  linarith

private lemma path_qR_pos {c : ℝ} {σ : Profile} (hc : 0 ≤ c) (hσ : IsSPE 1 c (Set.Ioi 0) σ)
    (ht1 : 1 < σ.t) (henc : 0 < σ.path.qM) :
    0 < σ.path.qR := by
  have hu0 : 0 < σ.u := hσ.2.2.1
  have ht0 : 0 < σ.t := hσ.2.2.2.1
  have hq0nn : 0 ≤ σ.path.qR := (hσ.2.1 σ.w σ.u σ.t hu0 ht0).1
  by_contra hnot
  have hq0 : σ.path.qR = 0 := le_antisymm (not_lt.mp hnot) hq0nn
  have hd := direct_eq hσ σ.w σ.u σ.t σ.path.qR 1 hu0 ht0 hq0nn
    (fun qM => lo_pM σ.u σ.t ht1 qM σ.path.qR)
  change σ.direct σ.w σ.u σ.t (σ.order σ.w σ.u σ.t) = _ at hd
  have hqM_eq : σ.path.qM = max 0 ((1 - c / σ.u - σ.u) / 2) := by
    change σ.direct σ.w σ.u σ.t (σ.order σ.w σ.u σ.t) = _
    rw [hd]
    simp [hq0]
  set m0 := (1 - c / σ.u - σ.u) / 2
  have hm0 : 0 < m0 := by
    by_contra h
    push Not at h
    rw [hqM_eq, max_eq_left h] at henc
    exact lt_irrefl _ henc
  have hP : mfrPayoff 1 c σ.path = σ.u * m0 ^ 2 := by
    have hpu : σ.path.u = σ.u := rfl
    have hpt : σ.path.t = σ.t := rfl
    have hpm : priceM σ.u σ.t σ.path.qM σ.path.qR = σ.u * (1 - m0) := by
      rw [lo_pM σ.u σ.t ht1, hq0, hqM_eq, max_eq_right hm0.le]; ring
    rw [mfrPayoff, hpu, hpt, hpm, hq0, hqM_eq, max_eq_right hm0.le]
    simp only [m0]
    field_simp [hu0.ne']
    ring
  -- Deviate to t' = 1/2, u' = σ.u, small q' > 0
  set q' := min (2 * m0) ((c + σ.u ^ 2 / 2) / (3 * σ.u))
  have hq'0 : 0 < q' := lt_min (by linarith) (by positivity)
  have hm' : 0 ≤ (1 - (1 / 2) * q' - c / σ.u - σ.u) / 2 := by
    have : q' ≤ 2 * m0 := min_le_left _ _
    simp only [m0] at this ⊢
    linarith
  have hA' : 0 < (1 / 2 : ℝ) * σ.u - ((1 / 2) * σ.u) * (1 / 2) / 2 := by linarith
  have hγ' : 0 < (1 / 2 : ℝ) * σ.u := by linarith
  have hdev := payoff_dev hσ σ.u (1 / 2) q' (1 / 2) ((1 / 2) * σ.u)
    hu0 (by norm_num) hq'0.le (hi_pM σ.u (1 / 2) (by norm_num))
    (hi_pR σ.u (1 / 2) (by norm_num)) hA' hγ' hm'
  rw [hP] at hdev
  have hdiff :
      ((1 / 2 : ℝ) * σ.u - (1 / 2) * σ.u * (1 - c / σ.u - σ.u) / 2 -
          2 * ((1 / 2) * σ.u - (1 / 2) * σ.u * (1 / 2) / 2) * q' - ((1 / 2) * σ.u) ^ 2) * q' +
        σ.u * ((1 - (1 / 2) * q' - c / σ.u - σ.u) / 2) ^ 2 - σ.u * m0 ^ 2 =
      q' * ((c + σ.u ^ 2 / 2) / 2 - 11 / 16 * σ.u * q') := by
    simp only [m0]
    field_simp [hu0.ne']
    ring
  have hq'ub : q' ≤ (c + σ.u ^ 2 / 2) / (3 * σ.u) := min_le_right _ _
  have hq'mul : σ.u * q' ≤ (c + σ.u ^ 2 / 2) / 3 := by
    have := mul_le_mul_of_nonneg_left hq'ub hu0.le
    calc σ.u * q' ≤ σ.u * ((c + σ.u ^ 2 / 2) / (3 * σ.u)) := this
      _ = (c + σ.u ^ 2 / 2) / 3 := by field_simp [hu0.ne']
  have hpos_fac : 0 < (c + σ.u ^ 2 / 2) / 2 - 11 / 16 * σ.u * q' := by
    have : 0 < c + σ.u ^ 2 / 2 := by positivity
    nlinarith
  have hstrict := mul_pos hq'0 hpos_fac
  linarith

private lemma path_low_relations {c : ℝ} {σ : Profile} (hc : 0 ≤ c)
    (hσ : IsSPE 1 c (Set.Ioi 0) σ) (ht1 : 1 < σ.t) (henc : 0 < σ.path.qM) :
    let u0 := σ.u
    let v0 := σ.t * σ.u
    0 < u0 ∧ u0 < v0 ∧ v0 < 1 / 2 ∧
    4 * c = 4 * v0 - u0 - 12 * v0 ^ 2 + 10 * u0 * v0 - 4 * u0 ^ 2 ∧
    5 * u0 + 2 ≤ 12 * v0 ∧
    0 < 3 * u0 - 4 * v0 + 12 * v0 ^ 2 - 6 * u0 * v0 ∧
    c ≤ 9 / 92 ∧
    mfrPayoff 1 c σ.path = PiLuv u0 v0 := by
  intro u0 v0
  have hu0 : 0 < u0 := hσ.2.2.1
  have ht0 : 0 < σ.t := hσ.2.2.2.1
  have huv : u0 < v0 := by
    show σ.u < σ.t * σ.u
    nlinarith
  have hq0pos : 0 < σ.path.qR := path_qR_pos hc hσ ht1 henc
  set q0 := σ.path.qR
  set w0 := σ.w
  have hd0 := direct_eq hσ w0 u0 σ.t q0 1 hu0 ht0 hq0pos.le
    (fun qM => lo_pM u0 σ.t ht1 qM q0)
  have hqM0 : σ.path.qM = max 0 ((1 - 1 * q0 - c / u0 - u0) / 2) := hd0
  set m0 := (1 - q0 - c / u0 - u0) / 2
  have hm0 : 0 < m0 := by
    by_contra h
    push Not at h
    have h' : (1 - 1 * q0 - c / u0 - u0) / 2 ≤ 0 := by simpa [m0] using h
    rw [hqM0, max_eq_left h'] at henc
    exact lt_irrefl _ henc
  -- Step 1: Retailer's stage-2 FOC gives w0 = B0 - 2 * A * q0
  set A := v0 - u0 / 2
  have hA : 0 < A := by simp only [A]; linarith
  set B0 := v0 - u0 * (1 - c / u0 - u0) / 2
  have hw0 : w0 = B0 - 2 * A * q0 := by
    have hδ : 0 < min q0 m0 := lt_min hq0pos hm0
    have hvert : q0 = (B0 - w0) / (2 * A) := by
      refine quad_locmax_interval (fun q => (B0 - w0 - A * q) * q)
        ((B0 - w0) ^ 2 / (4 * A)) A ((B0 - w0) / (2 * A)) q0 (min q0 m0) hA hδ ?_ ?_
      · intro q; field_simp [hA.ne']; ring
      · intro q hqdist
        have hq_nn : 0 ≤ q := by
          have := (abs_lt.mp hqdist).1
          have : min q0 m0 ≤ q0 := min_le_left _ _
          linarith
        have hmq : 0 ≤ (1 - q - c / u0 - u0) / 2 := by
          have := (abs_lt.mp hqdist).2
          have : min q0 m0 ≤ m0 := min_le_right _ _
          simp only [m0] at this ⊢
          linarith
        have hord := (hσ.2.1 w0 u0 σ.t hu0 ht0).2 q hq_nn
        have hdq := direct_eq hσ w0 u0 σ.t q 1 hu0 ht0 hq_nn (fun qM => lo_pM u0 σ.t ht1 qM q)
        simp only [Profile.outcomeAtOrder, Profile.outcomeAtDirect, retailerPayoff,
          lo_pR u0 σ.t ht1] at hord
        have hord0 : σ.order w0 u0 σ.t = q0 := rfl
        rw [hord0, hdq, hd0, max_eq_right (by simpa using hmq),
          max_eq_right (by simpa [m0] using hm0.le)] at hord
        have hL : (σ.t * u0 * (1 - q) - u0 * ((1 - 1 * q - c / u0 - u0) / 2) - w0) * q =
            (B0 - w0 - A * q) * q := by
          simp only [B0, A, v0]; ring
        have hR : (σ.t * u0 * (1 - q0) - u0 * ((1 - 1 * q0 - c / u0 - u0) / 2) - w0) * q0 =
            (B0 - w0 - A * q0) * q0 := by
          simp only [B0, A, v0]; ring
        linarith
    have hmul : 2 * A * q0 = B0 - w0 := by
      rw [hvert]; field_simp [hA.ne']
    linarith
  -- Step 2: Equilibrium payoff equals PsiL c u0 v0 q0
  have hP_eq : mfrPayoff 1 c σ.path = PsiL c u0 v0 q0 := by
    have hpm : priceM u0 σ.t σ.path.qM q0 = u0 * (1 - m0 - q0) := by
      rw [lo_pM u0 σ.t ht1, hqM0, max_eq_right (by simpa [m0] using hm0.le)]
      simp [m0]
    simp only [mfrPayoff, one_mul]
    change (w0 - (σ.t * u0) ^ 2) * q0 +
        (priceM u0 σ.t σ.path.qM q0 - c - u0 ^ 2) * σ.path.qM = PsiL c u0 v0 q0
    rw [hpm, hqM0, max_eq_right (by simpa [m0] using hm0.le), hw0]
    simp only [PsiL, B0, A, m0, v0]
    field_simp [hu0.ne']
    ring
  -- Step 3: FOC in v gives q0 = (1 - 2 * v0) / 2 and v0 < 1/2
  have hq0_v0 : q0 = (1 - 2 * v0) / 2 := by
    have hv_vert : v0 = (1 - 2 * q0) / 2 := by
      refine quad_locmax_interval (fun v => PsiL c u0 v q0)
        (q0 * (1 - 2 * q0) ^ 2 / 4 + (-u0 / 2 + c / 2 + u0 ^ 2 / 2 + u0 * q0) * q0 +
          u0 * ((1 - q0 - c / u0 - u0) / 2) ^ 2)
        q0 ((1 - 2 * q0) / 2) v0 (v0 - u0) hq0pos (by linarith) ?_ ?_
      · intro v; simp only [PsiL]; ring
      · intro v hvdist
        have hv_gt : u0 < v := by
          have := (abs_lt.mp hvdist).1
          linarith
        have hdev := payoff_dev_lo hσ u0 v q0 hu0 hv_gt hq0pos.le hm0.le
        linarith
    linarith
  have hv0_lt : v0 < 1 / 2 := by linarith
  -- Step 4: FOC in q gives 4 * c = 4 * v0 - u0 - 12 * v0^2 + 10 * u0 * v0 - 4 * u0^2
  have h4c : 4 * c = 4 * v0 - u0 - 12 * v0 ^ 2 + 10 * u0 * v0 - 4 * u0 ^ 2 := by
    set αq := (8 * v0 - 5 * u0) / 4
    have hαq : 0 < αq := by simp only [αq]; linarith
    set βq := v0 - u0 + c + u0 ^ 2 - v0 ^ 2
    have hδq : 0 < min q0 m0 := lt_min hq0pos hm0
    have hq_vert : q0 = βq / (2 * αq) := by
      refine quad_locmax_interval (fun q => PsiL c u0 v0 q)
        (βq ^ 2 / (4 * αq) + u0 * ((1 - c / u0 - u0) / 2) ^ 2)
        αq (βq / (2 * αq)) q0 (min q0 m0) hαq hδq ?_ ?_
      · intro q
        have hquad : βq ^ 2 / (4 * αq) + u0 * ((1 - c / u0 - u0) / 2) ^ 2 -
            αq * (q - βq / (2 * αq)) ^ 2 =
            -αq * q ^ 2 + βq * q + u0 * ((1 - c / u0 - u0) / 2) ^ 2 := by
          field_simp [hαq.ne']; ring
        rw [hquad]
        simp only [PsiL, αq, βq]
        field_simp [hu0.ne']
        ring
      · intro q hqdist
        have hq_nn : 0 ≤ q := by
          have := (abs_lt.mp hqdist).1
          have : min q0 m0 ≤ q0 := min_le_left _ _
          linarith
        have hmq : 0 ≤ (1 - q - c / u0 - u0) / 2 := by
          have := (abs_lt.mp hqdist).2
          have : min q0 m0 ≤ m0 := min_le_right _ _
          simp only [m0] at this ⊢
          linarith
        have hdev := payoff_dev_lo hσ u0 v0 q hu0 huv hq_nn hmq
        linarith
    have hmul : 2 * αq * q0 = βq := by
      rw [hq_vert]; field_simp [hαq.ne']
    simp only [αq, βq] at hmul
    rw [hq0_v0] at hmul
    linarith
  have hc_val : c = (4 * v0 - u0 - 12 * v0 ^ 2 + 10 * u0 * v0 - 4 * u0 ^ 2) / 4 := by linarith
  -- Step 5: Second-order condition along q(v) = (1 - 2 * v) / 2 gives 5 * u0 + 2 ≤ 12 * v0
  have h12v : 5 * u0 + 2 ≤ 12 * v0 := by
    by_contra hlt
    push Not at hlt
    set δ := min ((v0 - u0) / 2) m0
    have hδ : 0 < δ := lt_min (by linarith) hm0
    set s := -δ
    have hs_neg : s < 0 := by linarith
    have hv'_gt : u0 < v0 + s := by
      have : δ ≤ (v0 - u0) / 2 := min_le_left _ _
      linarith
    have hq'_nn : 0 ≤ (1 - 2 * (v0 + s)) / 2 := by linarith
    have hm' : 0 ≤ (1 - (1 - 2 * (v0 + s)) / 2 - c / u0 - u0) / 2 := by
      have h1 : (1 - (1 - 2 * (v0 + s)) / 2 - c / u0 - u0) / 2 = m0 + s / 2 := by
        simp only [m0, hq0_v0]; ring
      have h2 : δ ≤ m0 := min_le_right _ _
      linarith
    have hdev := payoff_dev_lo hσ u0 (v0 + s) ((1 - 2 * (v0 + s)) / 2) hu0 hv'_gt hq'_nn hm'
    have hgs : PsiL c u0 (v0 + s) ((1 - 2 * (v0 + s)) / 2) - PsiL c u0 v0 q0 =
        (2 + 5 * u0 - 12 * v0) * s ^ 2 / 4 - s ^ 3 := by
      rw [hq0_v0, hc_val]
      simp only [PsiL]
      field_simp [hu0.ne']
      ring
    have hpos1 : 0 < (2 + 5 * u0 - 12 * v0) * s ^ 2 / 4 := by
      have : 0 < s ^ 2 := sq_pos_of_ne_zero hs_neg.ne
      nlinarith
    have hpos2 : 0 < -s ^ 3 := by
      have : s ^ 3 = s * s ^ 2 := by ring
      have : 0 < s ^ 2 := sq_pos_of_ne_zero hs_neg.ne
      nlinarith
    linarith
  -- Step 6: qM_num > 0, c ≤ 9/92, and P = PiLuv u0 v0
  have hqM_num : 0 < 3 * u0 - 4 * v0 + 12 * v0 ^ 2 - 6 * u0 * v0 := by
    have hid : 8 * u0 * m0 = 3 * u0 - 4 * v0 + 12 * v0 ^ 2 - 6 * u0 * v0 := by
      simp only [m0, hq0_v0, hc_val]
      field_simp [hu0.ne']
      ring
    nlinarith
  have hc_ub : c ≤ 9 / 92 := by
    have hid : 48 * c = 108 / 23 - (12 * v0 - 5 * u0 - 2) ^ 2 - 23 * (u0 - 4 / 23) ^ 2 := by
      rw [hc_val]; ring
    nlinarith [sq_nonneg (12 * v0 - 5 * u0 - 2), sq_nonneg (u0 - 4 / 23)]
  have hP_PiL : mfrPayoff 1 c σ.path = PiLuv u0 v0 := by
    rw [hP_eq, hq0_v0, hc_val]
    unfold PsiL PiLuv
    field_simp [hu0.ne']
    ring
  exact ⟨hu0, huv, hv0_lt, h4c, h12v, hqM_num, hc_ub, hP_PiL⟩

private lemma witness_beats_Qpoly {c : ℝ} {σ : Profile} (hc0 : 0 ≤ c) (hc1 : c ≤ 9 / 92)
    (hσ : IsSPE 1 c (Set.Ioi 0) σ) :
    Qpoly c < mfrPayoff 1 c σ.path := by
  rcases le_total c (1 / 20) with hcle | hcge
  · -- Witness 1: t = 1/2, u = 3/8, q = 3/44 + 32/33 * c
    set u1 : ℝ := 3 / 8
    set t1 : ℝ := 1 / 2
    set q1 : ℝ := 3 / 44 + 32 / 33 * c
    have hq1 : 0 ≤ q1 := by simp only [q1]; linarith
    have hm1 : 0 ≤ (1 - t1 * q1 - c / u1 - u1) / 2 := by
      simp only [u1, t1, q1]; linarith
    have hdev := payoff_dev hσ u1 t1 q1 t1 (t1 * u1)
      (by norm_num [u1]) (by norm_num [t1]) hq1
      (hi_pM u1 t1 (by norm_num [t1])) (hi_pR u1 t1 (by norm_num [t1]))
      (by norm_num [u1, t1]) (by norm_num [u1, t1]) hm1
    have hval :
        (t1 * u1 - t1 * u1 * (1 - c / u1 - u1) / 2 -
            2 * (t1 * u1 - t1 * u1 * t1 / 2) * q1 - (t1 * u1) ^ 2) * q1 +
          u1 * ((1 - t1 * q1 - c / u1 - u1) / 2) ^ 2 =
        213 / 5632 - 49 / 176 * c + 10 / 11 * c ^ 2 := by
      simp only [u1, t1, q1]; ring
    have hgap : Qpoly c < 213 / 5632 - 49 / 176 * c + 10 / 11 * c ^ 2 := by
      unfold Qpoly
      have hconc : 0 ≤ c * (1 / 20 - c) := mul_nonneg hc0 (by linarith)
      nlinarith
    linarith
  · -- Witness 2: t = 2/3, u = 4/9, q = 4/63 + 27/28 * c
    set u2 : ℝ := 4 / 9
    set t2 : ℝ := 2 / 3
    set q2 : ℝ := 4 / 63 + 27 / 28 * c
    have hq2 : 0 ≤ q2 := by simp only [q2]; linarith
    have hm2 : 0 ≤ (1 - t2 * q2 - c / u2 - u2) / 2 := by
      simp only [u2, t2, q2]; linarith
    have hdev := payoff_dev hσ u2 t2 q2 t2 (t2 * u2)
      (by norm_num [u2]) (by norm_num [t2]) hq2
      (hi_pM u2 t2 (by norm_num [t2])) (hi_pR u2 t2 (by norm_num [t2]))
      (by norm_num [u2, t2]) (by norm_num [u2, t2]) hm2
    have hval :
        (t2 * u2 - t2 * u2 * (1 - c / u2 - u2) / 2 -
            2 * (t2 * u2 - t2 * u2 * t2 / 2) * q2 - (t2 * u2) ^ 2) * q2 +
          u2 * ((1 - t2 * q2 - c / u2 - u2) / 2) ^ 2 =
        1639 / 45927 - 89 / 378 * c + 99 / 112 * c ^ 2 := by
      simp only [u2, t2, q2]; ring
    have hgap : Qpoly c < 1639 / 45927 - 89 / 378 * c + 99 / 112 * c ^ 2 := by
      unfold Qpoly
      have hconc : 0 ≤ (c - 1 / 20) * (9 / 92 - c) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith
    linarith

private lemma prop3_k1 (c : ℝ) (hc : 0 ≤ c) (σ : Profile)
    (hσ : IsSPE 1 c (Set.Ioi 0) σ) (henc : 0 < σ.path.qM) :
    σ.t ≤ 1 := by
  by_contra hgt
  push Not at hgt
  obtain ⟨hu0, huv, hv0, h4c, h12v, hqM, hc_ub, hP⟩ := path_low_relations hc hσ hgt henc
  have hc_eq : c = cUV σ.u (σ.t * σ.u) := by
    unfold cUV; linarith
  have h1 : PiLuv σ.u (σ.t * σ.u) < Qpoly c := by
    rw [hc_eq]
    exact PiLuv_lt_Qpoly σ.u (σ.t * σ.u) hu0 huv hv0 h12v (by linarith) hqM
  have h2 : Qpoly c < mfrPayoff 1 c σ.path := witness_beats_Qpoly hc hc_ub hσ
  linarith

/-! ## Section 3: Scaling from arbitrary `k > 0` to `k = 1` -/

private lemma priceM_div {k u t qM qR : ℝ} :
    priceM (u / k) t qM qR = priceM u t qM qR / k := by
  unfold priceM
  split_ifs <;> ring

private lemma priceR_div {k u t qM qR : ℝ} :
    priceR (u / k) t qM qR = priceR u t qM qR / k := by
  unfold priceR
  split_ifs <;> ring

private lemma retailerPayoff_div {k w u t qR qM : ℝ} :
    retailerPayoff ⟨w / k, u / k, t, qR, qM⟩ = retailerPayoff ⟨w, u, t, qR, qM⟩ / k := by
  simp only [retailerPayoff, priceR_div]
  ring

private lemma mfrPayoff_div {k c w u t qR qM : ℝ} (hk : k ≠ 0) :
    mfrPayoff k c ⟨w / k, u / k, t, qR, qM⟩ =
      mfrPayoff 1 (k * c) ⟨w, u, t, qR, qM⟩ / k := by
  simp only [mfrPayoff, priceM_div, one_mul]
  field_simp [hk]

private noncomputable def scaleProfile (k : ℝ) (σ : Profile) : Profile where
  w := k * σ.w
  u := k * σ.u
  t := σ.t
  order := fun w u t => σ.order (w / k) (u / k) t
  direct := fun w u t qR => σ.direct (w / k) (u / k) t qR

private lemma scaleProfile_isSPE {k c : ℝ} (hk : 0 < k) {σ : Profile}
    (hσ : IsSPE k c (Set.Ioi 0) σ) :
    IsSPE 1 (k * c) (Set.Ioi 0) (scaleProfile k σ) := by
  have hkne : k ≠ 0 := hk.ne'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro w u t qR hu ht hqR
    have h3 := hσ.1 (w / k) (u / k) t qR (div_pos hu hk) ht hqR
    refine ⟨h3.1, fun qM hqM => ?_⟩
    have hle := h3.2 qM hqM
    simp only [Profile.outcomeAtDirect, scaleProfile] at hle ⊢
    rw [mfrPayoff_div hkne, mfrPayoff_div hkne] at hle
    exact (div_le_div_iff_of_pos_right hk).mp hle
  · intro w u t hu ht
    have h2 := hσ.2.1 (w / k) (u / k) t (div_pos hu hk) ht
    refine ⟨h2.1, fun qR hqR => ?_⟩
    have hle := h2.2 qR hqR
    simp only [Profile.outcomeAtOrder, Profile.outcomeAtDirect, scaleProfile] at hle ⊢
    rw [retailerPayoff_div, retailerPayoff_div] at hle
    exact (div_le_div_iff_of_pos_right hk).mp hle
  · exact mul_pos hk hσ.2.2.1
  · exact hσ.2.2.2.1
  · intro w u t hu ht
    have h1 := hσ.2.2.2.2 (w / k) (u / k) t (div_pos hu hk) ht
    have hpath : (scaleProfile k σ).path =
        ⟨k * σ.w, k * σ.u, σ.t, σ.path.qR, σ.path.qM⟩ := by
      simp [Profile.path, Profile.outcomeAtOrder, Profile.outcomeAtDirect, scaleProfile,
        mul_div_cancel_left₀ _ hkne]
    rw [hpath]
    simp only [Profile.outcomeAtOrder, Profile.outcomeAtDirect, scaleProfile] at h1 ⊢
    have h1' : mfrPayoff k c ⟨w / k, u / k, t, σ.order (w / k) (u / k) t,
          σ.direct (w / k) (u / k) t (σ.order (w / k) (u / k) t)⟩ ≤
        mfrPayoff k c ⟨(k * σ.w) / k, (k * σ.u) / k, σ.t, σ.path.qR, σ.path.qM⟩ := by
      simpa [Profile.path, Profile.outcomeAtOrder, Profile.outcomeAtDirect,
        mul_div_cancel_left₀ _ hkne] using h1
    rw [mfrPayoff_div hkne, mfrPayoff_div hkne] at h1'
    exact (div_le_div_iff_of_pos_right hk).mp h1'

private lemma scaleProfile_qM {k : ℝ} (hk : k ≠ 0) (σ : Profile) :
    (scaleProfile k σ).path.qM = σ.path.qM := by
  simp [Profile.path, Profile.outcomeAtOrder, Profile.outcomeAtDirect, scaleProfile,
    mul_div_cancel_left₀ _ hk]

end QualityEncroachProp3

open QualityEncroach.Differ in
theorem solution (k c : ℝ) (hk : 0 < k) (hc : 0 ≤ c) (σ : Profile)
    (hσ : IsSPE k c (Set.Ioi 0) σ) (henc : 0 < σ.path.qM) :
    σ.t ≤ 1 := by
  have hτ := QualityEncroachProp3.scaleProfile_isSPE hk hσ
  have henc' : 0 < (QualityEncroachProp3.scaleProfile k σ).path.qM := by
    rw [QualityEncroachProp3.scaleProfile_qM hk.ne']
    exact henc
  exact QualityEncroachProp3.prop3_k1 (k * c) (mul_nonneg hk.le hc)
    (QualityEncroachProp3.scaleProfile k σ) hτ henc'
