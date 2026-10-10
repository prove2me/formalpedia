-- Prove2me | solution 1 for ThomsonN7.Final.capspec_cap
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-10-10T01:47:18.875929+00:00
-- url     : https://prove2.me/submissions/e57e79fd-6bde-4771-9d50-6bd1fc0c7d53

import Mathlib
import Definitions.Def_ThomsonN7_core
import Definitions.Def_ThomsonN7_cap_data_2

/-!
# Thomson problem for N = 7 (and the D3h stretch target for N = 9)

Minimise the Coulomb energy `E(x) = ∑_{i<j} 1 / ‖x i - x j‖` over configurations of `N` pairwise
distinct points on the unit sphere `S² ⊂ ℝ³`.

* `N = 7`: the unique minimiser (up to `O(3)` and relabelling) is the regular pentagonal bipyramid,
  with `E = 1/2 + 5√2 + 5/(2 sin(π/5)) + 5/(2 sin(2π/5)) = 14.452977414…`.
* `N = 9`: the (numerically known) minimiser is the D3h tricapped trigonal prism, which has one free
  parameter `z` (the height of the two triangular faces); numerically `z ≈ 0.70365`,
  `E ≈ 25.759986531`.
-/

open Real

namespace ThomsonN7

/-! ## Auxiliary facts (already proved; they show the definitions are well-posed) -/

lemma norm_sq_cyl_sub (ρ θ h ρ' θ' h' : ℝ) :
    ‖cyl ρ θ h - cyl ρ' θ' h'‖ ^ 2 = ρ ^ 2 + ρ' ^ 2 - 2 * ρ * ρ' * cos (θ - θ') + (h - h') ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [cyl, Fin.sum_univ_three, cos_sub]
  nlinarith [sin_sq_add_cos_sq θ, sin_sq_add_cos_sq θ']

lemma pent_of_lt {i : Fin 7} (hi : (i : ℕ) < 5) :
    pentBipyramid i = cyl 1 (2 * π * (i : ℕ) / 5) 0 := by
  simp [pentBipyramid, hi]

lemma pent_five : pentBipyramid 5 = cyl 0 0 1 := by simp [pentBipyramid]
lemma pent_six : pentBipyramid 6 = cyl 0 0 (-1) := by simp [pentBipyramid]

lemma coulombEnergy_seven (x : Fin 7 → R3) : coulombEnergy x =
    ‖x 0 - x 1‖⁻¹ + ‖x 0 - x 2‖⁻¹ + ‖x 0 - x 3‖⁻¹ + ‖x 0 - x 4‖⁻¹ + ‖x 0 - x 5‖⁻¹ + ‖x 0 - x 6‖⁻¹
    + ‖x 1 - x 2‖⁻¹ + ‖x 1 - x 3‖⁻¹ + ‖x 1 - x 4‖⁻¹ + ‖x 1 - x 5‖⁻¹ + ‖x 1 - x 6‖⁻¹
    + ‖x 2 - x 3‖⁻¹ + ‖x 2 - x 4‖⁻¹ + ‖x 2 - x 5‖⁻¹ + ‖x 2 - x 6‖⁻¹
    + ‖x 3 - x 4‖⁻¹ + ‖x 3 - x 5‖⁻¹ + ‖x 3 - x 6‖⁻¹
    + ‖x 4 - x 5‖⁻¹ + ‖x 4 - x 6‖⁻¹ + ‖x 5 - x 6‖⁻¹ := by
  have hI : ∀ i : Fin 7, ∑ j ∈ Finset.Ioi i, ‖x i - x j‖⁻¹ =
      ∑ j, if i < j then ‖x i - x j‖⁻¹ else 0 := by
    intro i
    rw [← Finset.sum_filter]
    congr 1
    ext j; simp
  simp only [coulombEnergy, hI, Fin.sum_univ_seven]
  simp
  ring

lemma norm_eq_of_sq_eq {v : R3} {c : ℝ} (hc : 0 ≤ c) (h : ‖v‖ ^ 2 = c ^ 2) : ‖v‖ = c :=
  (sq_eq_sq₀ (norm_nonneg v) hc).1 h

lemma ring_dist (a b : ℝ) :
    ‖cyl 1 a 0 - cyl 1 b 0‖ ^ 2 = (2 * sin ((a - b) / 2)) ^ 2 := by
  rw [norm_sq_cyl_sub]
  have h1 : cos (a - b) = 1 - 2 * sin ((a - b) / 2) ^ 2 := by
    have := cos_two_mul ((a - b) / 2)
    have h2 := sin_sq_add_cos_sq ((a - b) / 2)
    rw [show 2 * ((a - b) / 2) = a - b by ring] at this
    rw [this]; nlinarith
  rw [h1]; ring

lemma pent_dist_pent {i j : Fin 7} (hi : (i : ℕ) < 5) (hj : (j : ℕ) < 5) (hij : i < j) :
    ‖pentBipyramid i - pentBipyramid j‖ = 2 * sin (π * (((j : ℕ) : ℝ) - (i : ℕ)) / 5) := by
  have hij' : (i : ℕ) < (j : ℕ) := hij
  rw [pent_of_lt hi, pent_of_lt hj]
  apply norm_eq_of_sq_eq
  · have : 0 < sin (π * (((j : ℕ) : ℝ) - (i : ℕ)) / 5) := by
      apply sin_pos_of_pos_of_lt_pi
      · have : (0 : ℝ) < ((j : ℕ) : ℝ) - (i : ℕ) := by
          rw [sub_pos]; exact_mod_cast hij'
        positivity
      · have : (((j : ℕ) : ℝ) - (i : ℕ)) < 5 := by
          have : (j : ℕ) < 5 := hj
          have : (((j : ℕ) : ℝ)) < 5 := by exact_mod_cast this
          have : (0 : ℝ) ≤ (i : ℕ) := Nat.cast_nonneg _
          linarith
        nlinarith [Real.pi_pos]
    linarith
  · rw [ring_dist]
    have : sin ((2 * π * ((i : ℕ) : ℝ) / 5 - 2 * π * ((j : ℕ) : ℝ) / 5) / 2)
        = - sin (π * (((j : ℕ) : ℝ) - (i : ℕ)) / 5) := by
      rw [← sin_neg]; congr 1; ring
    rw [this]; ring

lemma pent_dist_north {i : Fin 7} (hi : (i : ℕ) < 5) :
    ‖pentBipyramid i - pentBipyramid 5‖ = √2 := by
  rw [pent_of_lt hi, pent_five]
  apply norm_eq_of_sq_eq (Real.sqrt_nonneg _)
  rw [norm_sq_cyl_sub, Real.sq_sqrt (by norm_num)]; norm_num

lemma pent_dist_south {i : Fin 7} (hi : (i : ℕ) < 5) :
    ‖pentBipyramid i - pentBipyramid 6‖ = √2 := by
  rw [pent_of_lt hi, pent_six]
  apply norm_eq_of_sq_eq (Real.sqrt_nonneg _)
  rw [norm_sq_cyl_sub, Real.sq_sqrt (by norm_num)]; norm_num

lemma pent_dist_poles : ‖pentBipyramid 5 - pentBipyramid 6‖ = 2 := by
  rw [pent_five, pent_six]
  apply norm_eq_of_sq_eq (by norm_num)
  rw [norm_sq_cyl_sub]; norm_num

/-- Closed form of the pentagonal bipyramid energy (`≈ 14.452977414`). -/
theorem pentBipyramid_energy :
    coulombEnergy pentBipyramid =
      1 / 2 + 5 * √2 + 5 / (2 * sin (π / 5)) + 5 / (2 * sin (2 * π / 5)) := by
  have hs3 : sin (3 * π / 5) = sin (2 * π / 5) := by
    rw [← sin_pi_sub]; congr 1; ring
  have hs4 : sin (4 * π / 5) = sin (π / 5) := by
    rw [← sin_pi_sub]; congr 1; ring
  have d01 : ‖pentBipyramid 0 - pentBipyramid 1‖ = 2 * sin (π / 5) := by
    rw [pent_dist_pent (by decide) (by decide) (by decide)]; norm_num
  have d12 : ‖pentBipyramid 1 - pentBipyramid 2‖ = 2 * sin (π / 5) := by
    rw [pent_dist_pent (by decide) (by decide) (by decide)]; norm_num
  have d23 : ‖pentBipyramid 2 - pentBipyramid 3‖ = 2 * sin (π / 5) := by
    rw [pent_dist_pent (by decide) (by decide) (by decide)]; norm_num
  have d34 : ‖pentBipyramid 3 - pentBipyramid 4‖ = 2 * sin (π / 5) := by
    rw [pent_dist_pent (by decide) (by decide) (by decide)]; norm_num
  have d04 : ‖pentBipyramid 0 - pentBipyramid 4‖ = 2 * sin (π / 5) := by
    rw [pent_dist_pent (by decide) (by decide) (by decide)]; norm_num
    rw [← hs4]; congr 2; ring
  have d02 : ‖pentBipyramid 0 - pentBipyramid 2‖ = 2 * sin (2 * π / 5) := by
    rw [pent_dist_pent (by decide) (by decide) (by decide)]; norm_num
    congr 2; ring
  have d13 : ‖pentBipyramid 1 - pentBipyramid 3‖ = 2 * sin (2 * π / 5) := by
    rw [pent_dist_pent (by decide) (by decide) (by decide)]; norm_num
    congr 2; ring
  have d24 : ‖pentBipyramid 2 - pentBipyramid 4‖ = 2 * sin (2 * π / 5) := by
    rw [pent_dist_pent (by decide) (by decide) (by decide)]; norm_num
    congr 2; ring
  have d03 : ‖pentBipyramid 0 - pentBipyramid 3‖ = 2 * sin (2 * π / 5) := by
    rw [pent_dist_pent (by decide) (by decide) (by decide)]; norm_num
    rw [← hs3]; congr 2; ring
  have d14 : ‖pentBipyramid 1 - pentBipyramid 4‖ = 2 * sin (2 * π / 5) := by
    rw [pent_dist_pent (by decide) (by decide) (by decide)]; norm_num
    rw [← hs3]; congr 2; ring
  have hp1 : 0 < sin (π / 5) := sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  have hp2 : 0 < sin (2 * π / 5) :=
    sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  rw [coulombEnergy_seven, d01, d12, d23, d34, d04, d02, d13, d24, d03, d14,
    pent_dist_north (i := 0) (by decide), pent_dist_north (i := 1) (by decide),
    pent_dist_north (i := 2) (by decide), pent_dist_north (i := 3) (by decide),
    pent_dist_north (i := 4) (by decide), pent_dist_south (i := 0) (by decide),
    pent_dist_south (i := 1) (by decide), pent_dist_south (i := 2) (by decide),
    pent_dist_south (i := 3) (by decide), pent_dist_south (i := 4) (by decide),
    pent_dist_poles]
  have h2 : (0 : ℝ) < √2 := by positivity
  have h3 : (√2)⁻¹ = √2 / 2 := by
    field_simp
    rw [Real.sq_sqrt (by norm_num)]
  rw [h3]
  field_simp
  ring

/- BEGIN M0 -/
namespace Base

open Finset

lemma neg_one_le_inner_of_unit {x y : R3} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    -1 ≤ inner ℝ x y := by
  have := abs_real_inner_le_norm x y
  rw [hx, hy, mul_one] at this
  exact (abs_le.1 this).1

/-! ### Invariance -/

/-! ### Gram values of the pentagonal bipyramid -/

end Base
/- END M0 -/

/- BEGIN M1 -/
namespace ThreePoint

open Finset Matrix
open scoped RealInnerProductSpace

/-! # Bachoc–Vallentin three-point positivity on `S²` (any block size, any `k`)

`Q3 k u v t = ((1-u²)(1-v²))^{k/2} T_k((t-uv)/√((1-u²)(1-v²)))` via the Chebyshev recursion.
-/

/-! ### Addition theorem (de Moivre) -/

theorem Q3_eq_re (u v t : ℝ) (z z' : ℂ)
    (hu : 1 - u ^ 2 = Complex.normSq z) (hv : 1 - v ^ 2 = Complex.normSq z')
    (ht : t - u * v = (z * (starRingEnd ℂ) z').re) (k : ℕ) :
    Q3 k u v t = ((z * (starRingEnd ℂ) z') ^ k).re := by
  set w : ℂ := z * (starRingEnd ℂ) z' with hw
  have hnw : Complex.normSq w = (1 - u ^ 2) * (1 - v ^ 2) := by
    rw [hw, map_mul, Complex.normSq_conj, hu, hv]
  have hrec : w * w = (2 * w.re : ℝ) * w - (Complex.normSq w : ℝ) := by
    apply Complex.ext <;> simp [Complex.normSq_apply] <;> ring
  have key : ∀ k, Q3 k u v t = (w ^ k).re ∧ Q3 (k + 1) u v t = (w ^ (k + 1)).re := by
    intro k
    induction k with
    | zero => simp [Q3, ht]
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have h2 : w ^ (k + 2) = ((2 * w.re : ℝ) : ℂ) * w ^ (k + 1) - (Complex.normSq w : ℝ) * w ^ k := by
        have : w ^ (k + 2) = w ^ k * (w * w) := by ring
        rw [this, hrec]; ring
      show Q3 (k + 2) u v t = (w ^ (k + 2)).re
      rw [h2, Complex.sub_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul, hnw, ← ih.1, ← ih.2, ← ht]
      simp only [Q3]
  exact (key k).1

/-- The quadratic form of `Σ_{j,l} Y_k` at a fixed centre is a sum of two squares. -/
theorem quad_Y3_nonneg (m k : ℕ) {n : ℕ} (u : Fin n → ℝ) (t : Fin n → Fin n → ℝ)
    (a b : Fin n → ℝ) (hu : ∀ j, 1 - u j ^ 2 = a j ^ 2 + b j ^ 2)
    (ht : ∀ j l, t j l - u j * u l = a j * a l + b j * b l)
    (w : Fin m → ℝ) :
    0 ≤ ∑ j, ∑ l, w ⬝ᵥ (Y3 m k (u j) (u l) (t j l)).mulVec w := by
  set z : Fin n → ℂ := fun j => ⟨a j, b j⟩ with hz
  have hQ : ∀ j l, Q3 k (u j) (u l) (t j l)
      = ((z j) ^ k).re * ((z l) ^ k).re + ((z j) ^ k).im * ((z l) ^ k).im := by
    intro j l
    rw [Q3_eq_re (u j) (u l) (t j l) (z j) (z l)
      (by rw [hu j]; simp [hz, Complex.normSq_apply, sq])
      (by rw [hu l]; simp [hz, Complex.normSq_apply, sq])
      (by simp [hz, ht])]
    rw [mul_pow, Complex.mul_re, ← map_pow, Complex.conj_re, Complex.conj_im]
    ring
  have key : ∀ j l, w ⬝ᵥ (Y3 m k (u j) (u l) (t j l)).mulVec w
      = (∑ p, w p * u j ^ (p : ℕ)) * (∑ p, w p * u l ^ (p : ℕ))
        * (((z j) ^ k).re * ((z l) ^ k).re + ((z j) ^ k).im * ((z l) ^ k).im) := by
    intro j l
    rw [← hQ j l]
    simp only [dotProduct, mulVec, Y3, Matrix.of_apply]
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  simp only [key]
  have hsq : ∀ (g c s : Fin n → ℝ), ∑ j, ∑ l, g j * g l * (c j * c l + s j * s l)
      = (∑ j, g j * c j) ^ 2 + (∑ j, g j * s j) ^ 2 := by
    intro g c s
    simp only [sq, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [hsq (fun j => ∑ p, w p * u j ^ (p : ℕ)) (fun j => ((z j) ^ k).re) (fun j => ((z j) ^ k).im)]
  positivity

/-- Every unit vector of `ℝ³` has an orthonormal frame of its orthogonal complement, giving
tangent-plane coordinates with Parseval's identity: extend `{x}` to an orthonormal basis. -/
theorem exists_tangent_frame (x : R3) (hx : ‖x‖ = 1) :
    ∃ e₁ e₂ : R3, ∀ y z : R3, ‖y‖ = 1 → ‖z‖ = 1 →
      (1 - ⟪x, y⟫ ^ 2 = ⟪e₁, y⟫ ^ 2 + ⟪e₂, y⟫ ^ 2) ∧
      (⟪y, z⟫ - ⟪x, y⟫ * ⟪x, z⟫ = ⟪e₁, y⟫ * ⟪e₁, z⟫ + ⟪e₂, y⟫ * ⟪e₂, z⟫) := by
  have hcard : Module.finrank ℝ R3 = Fintype.card (Fin 3) := by simp
  let v : Fin 3 → R3 := fun _ => x
  have hv : Orthonormal ℝ (({0} : Set (Fin 3)).domRestrict v) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j := Subtype.ext (by
      have hi := i.2; have hj := j.2
      simp only [Set.mem_singleton_iff] at hi hj
      rw [hi, hj])
    subst hij
    simp [Set.domRestrict, v, real_inner_self_eq_norm_sq, hx]
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard hv
  have hb0 : b 0 = x := hb 0 (Set.mem_singleton 0)
  refine ⟨b 1, b 2, fun y z hy hz => ?_⟩
  have P := b.sum_inner_mul_inner y z
  have Py := b.sum_inner_mul_inner y y
  rw [Fin.sum_univ_three, hb0] at P Py
  rw [real_inner_self_eq_norm_sq, hy] at Py
  have c1 : ⟪y, x⟫ = ⟪x, y⟫ := real_inner_comm _ _
  have c2 : ⟪y, b 1⟫ = ⟪b 1, y⟫ := real_inner_comm _ _
  have c3 : ⟪y, b 2⟫ = ⟪b 2, y⟫ := real_inner_comm _ _
  rw [c1, c2, c3] at P Py
  constructor
  · linear_combination -Py
  · linear_combination -P

/-! ### Combinatorics of ordered triple sums -/

section Comb

variable {n : ℕ}

theorem sum_all_eq (f : Fin n → Fin n → Fin n → ℝ) :
    ∑ i, ∑ j, ∑ l, f i j l
      = dsum f + ∑ i, ∑ l, f i i l + ∑ i, ∑ j, f i j i + ∑ i, ∑ j, f i j j
          - 2 * ∑ i, f i i i := by
  have pt : ∀ i j l, f i j l
      = (if i ≠ j ∧ i ≠ l ∧ j ≠ l then f i j l else 0) + (if i = j then f i j l else 0)
        + (if i = l then f i j l else 0) + (if j = l then f i j l else 0)
        - 2 * (if i = j then (if j = l then f i j l else 0) else 0) := by
    intro i j l
    by_cases h1 : i = j <;> by_cases h2 : i = l <;> by_cases h3 : j = l <;> simp_all <;> ring
  have e1 : ∑ i, ∑ j, ∑ l, (if i = j then f i j l else 0) = ∑ i, ∑ l, f i i l := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    simp [Finset.sum_ite_eq]
  have e2 : ∑ i, ∑ j, ∑ l, (if i = l then f i j l else 0) = ∑ i, ∑ j, f i j i := by
    simp [Finset.sum_ite_eq]
  have e3 : ∑ i, ∑ j, ∑ l, (if j = l then f i j l else 0) = ∑ i, ∑ j, f i j j := by
    simp [Finset.sum_ite_eq]
  have e4 : ∑ i, ∑ j, ∑ l, (if i = j then (if j = l then f i j l else 0) else 0)
      = ∑ i, f i i i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    simp [Finset.sum_ite_eq]
  calc ∑ i, ∑ j, ∑ l, f i j l
      = ∑ i, ∑ j, ∑ l, ((if i ≠ j ∧ i ≠ l ∧ j ≠ l then f i j l else 0) + (if i = j then f i j l else 0)
        + (if i = l then f i j l else 0) + (if j = l then f i j l else 0)
        - 2 * (if i = j then (if j = l then f i j l else 0) else 0)) := by
          simp only [← pt]
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, e1, e2, e3, e4]
      rfl

end Comb

section Comb2

variable {n : ℕ}

theorem dsum_add (f g : Fin n → Fin n → Fin n → ℝ) :
    dsum (fun i j l => f i j l + g i j l) = dsum f + dsum g := by
  unfold dsum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp

theorem dsum_sub (f g : Fin n → Fin n → Fin n → ℝ) :
    dsum (fun i j l => f i j l - g i j l) = dsum f - dsum g := by
  unfold dsum
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp

theorem dsum_swap23 (f : Fin n → Fin n → Fin n → ℝ) :
    dsum (fun i j l => f i l j) = dsum f := by
  unfold dsum
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : i ≠ a ∧ i ≠ b ∧ a ≠ b
  · rw [if_pos h, if_pos ⟨h.2.1, h.1, h.2.2.symm⟩]
  · rw [if_neg h, if_neg]
    rintro ⟨h1, h2, h3⟩
    exact h ⟨h2, h1, h3.symm⟩

theorem dsum_cyc (f : Fin n → Fin n → Fin n → ℝ) :
    dsum (fun i j l => f j l i) = dsum f := by
  unfold dsum
  calc ∑ i, ∑ j, ∑ l, (if i ≠ j ∧ i ≠ l ∧ j ≠ l then f j l i else 0)
      = ∑ j, ∑ i, ∑ l, (if i ≠ j ∧ i ≠ l ∧ j ≠ l then f j l i else 0) := Finset.sum_comm
    _ = ∑ j, ∑ l, ∑ i, (if i ≠ j ∧ i ≠ l ∧ j ≠ l then f j l i else 0) :=
        Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = _ := by
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
        Finset.sum_congr rfl fun c _ => ?_
      by_cases h : a ≠ b ∧ a ≠ c ∧ b ≠ c
      · rw [if_pos ⟨h.2.1.symm, h.2.2.symm, h.1⟩, if_pos h]
      · rw [if_neg, if_neg h]
        rintro ⟨h1, h2, h3⟩
        exact h ⟨h3, h1.symm, h2.symm⟩

end Comb2

section Comb3

variable {n : ℕ}

theorem sum_ne_eq_two_sum_Ioi (h : Fin n → Fin n → ℝ) (hsymm : ∀ i j, h i j = h j i) :
    ∑ i, ∑ j, (if i ≠ j then h i j else 0) = 2 * ∑ i, ∑ j ∈ Finset.Ioi i, h i j := by
  have step1 : ∀ i : Fin n, ∑ j, (if i ≠ j then h i j else 0)
      = ∑ j, (if i < j then h i j else 0) + ∑ j, (if j < i then h i j else 0) := by
    intro i
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rcases lt_trichotomy i j with hlt | heq | hgt
    · simp [hlt, hlt.ne, not_lt_of_gt hlt]
    · simp [heq]
    · simp [hgt, hgt.ne', not_lt_of_gt hgt]
  have hI : ∀ i : Fin n, ∑ j, (if i < j then h i j else 0) = ∑ j ∈ Finset.Ioi i, h i j := by
    intro i
    rw [← Finset.sum_filter, Finset.filter_lt_eq_Ioi]
  simp only [step1, Finset.sum_add_distrib, hI]
  have h2 : ∑ i : Fin n, ∑ j, (if j < i then h i j else 0)
      = ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, h i j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_filter, Finset.filter_lt_eq_Ioi]
    exact Finset.sum_congr rfl fun i _ => hsymm i j
  rw [h2]
  ring

end Comb3

section Comb4

variable {n : ℕ}

theorem sum_ne_eq_sub (a : Fin n → ℝ) (i : Fin n) :
    ∑ j, (if i ≠ j then a j else 0) = ∑ j, a j - a i := by
  have h1 : ∑ j, a j = ∑ j, (if i ≠ j then a j else 0) + ∑ j, (if i = j then a j else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : i = j <;> simp [h]
  rw [h1, Finset.sum_ite_eq]
  simp

end Comb4

section Final

variable {n : ℕ}

theorem dsum_nonneg {f : Fin n → Fin n → Fin n → ℝ}
    (h : ∀ i j l, i ≠ j → i ≠ l → j ≠ l → 0 ≤ f i j l) : 0 ≤ dsum f := by
  unfold dsum
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun l _ => ?_
  split_ifs with hc
  · exact h i j l hc.1 hc.2.1 hc.2.2
  · exact le_rfl

theorem inner_coords (x y : R3) : ⟪x, y⟫ = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three, mul_comm]

theorem normsq_coords (x : R3) (hx : ‖x‖ = 1) : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 = 1 := by
  have := real_inner_self_eq_norm_sq x
  rw [hx, inner_coords] at this
  nlinarith [this]

/-- The Gram determinant of three unit vectors in `ℝ³` is a square, hence nonnegative. -/
theorem gram_det_nonneg (x y z : R3) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1) :
    0 ≤ 1 + 2 * ⟪x, y⟫ * ⟪x, z⟫ * ⟪y, z⟫ - ⟪x, y⟫ ^ 2 - ⟪x, z⟫ ^ 2 - ⟪y, z⟫ ^ 2 := by
  have hx' := normsq_coords x hx; have hy' := normsq_coords y hy; have hz' := normsq_coords z hz
  rw [inner_coords, inner_coords, inner_coords]
  have key : 1 + 2 * (x 0 * y 0 + x 1 * y 1 + x 2 * y 2) * (x 0 * z 0 + x 1 * z 1 + x 2 * z 2)
        * (y 0 * z 0 + y 1 * z 1 + y 2 * z 2) - (x 0 * y 0 + x 1 * y 1 + x 2 * y 2) ^ 2
        - (x 0 * z 0 + x 1 * z 1 + x 2 * z 2) ^ 2 - (y 0 * z 0 + y 1 * z 1 + y 2 * z 2) ^ 2
      = (x 0 * (y 1 * z 2 - y 2 * z 1) - x 1 * (y 0 * z 2 - y 2 * z 0)
          + x 2 * (y 0 * z 1 - y 1 * z 0)) ^ 2 := by
    linear_combination
      (2*y 0^2*z 0^2 - y 0^2 + 2*y 0*y 1*z 0*z 1 + 2*y 0*y 2*z 0*z 2 - y 1^2*z 2^2
        + 2*y 1*y 2*z 1*z 2 - y 2^2*z 1^2 - z 0^2) * hx'
      + (2*x 0*x 1*z 0*z 1 + 2*x 0*x 2*z 0*z 2 - 2*x 1^2*z 0^2 - x 1^2*z 2^2 + x 1^2
        + 2*x 1*x 2*z 1*z 2 - 2*x 2^2*z 0^2 - x 2^2*z 1^2 + x 2^2 + z 0^2 - 1) * hy'
      + (2*x 0*x 1*y 0*y 1 + 2*x 0*x 2*y 0*y 2 + 2*x 1^2*y 1^2 + x 1^2*y 2^2 - x 1^2
        + 2*x 1*x 2*y 1*y 2 + x 2^2*y 1^2 + 2*x 2^2*y 2^2 - x 2^2 - y 1^2 - y 2^2) * hz'
  rw [key]; positivity

theorem gramOK_inner (x y z : R3) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1) :
    GramOK ⟪x, y⟫ ⟪x, z⟫ ⟪y, z⟫ := by
  have h1 : ∀ a b : R3, ‖a‖ = 1 → ‖b‖ = 1 → ⟪a, b⟫ ^ 2 ≤ 1 := by
    intro a b ha hb
    have := abs_real_inner_le_norm a b
    rw [ha, hb, mul_one] at this
    exact (sq_le_one_iff_abs_le_one _).mpr this
  refine ⟨h1 x y hx hy, h1 x z hx hz, h1 y z hy hz, ?_⟩
  have := gram_det_nonneg x y z hx hy hz
  linarith

end Final

/-! ### The kernels at the diagonal `(1,1,1)` -/

section FinalZ

variable {n : ℕ}

end FinalZ

/- BEGIN M5 -/
section Critical

end Critical

section Critical

end Critical

section Critical

end Critical

section CriticalZ

variable {n : ℕ}

end CriticalZ

section CriticalZsym

variable {n : ℕ}

theorem dsum_swap12 (f : Fin n → Fin n → Fin n → ℝ) :
    dsum (fun i j l => f j i l) = dsum f := by
  unfold dsum
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => ?_
  by_cases h : a ≠ b ∧ a ≠ c ∧ b ≠ c
  · rw [if_pos ⟨h.1.symm, h.2.2, h.2.1⟩, if_pos h]
  · rw [if_neg, if_neg h]
    rintro ⟨h1, h2, h3⟩
    exact h ⟨h1.symm, h3, h2⟩

section Perm

variable (τ : Fin n → Fin n → ℝ) (hτ : ∀ i j, τ j i = τ i j) (f : ℝ → ℝ → ℝ → ℝ)

include hτ

end Perm

end CriticalZsym

section CriticalFinal

variable {n : ℕ}

end CriticalFinal

/- END M5 -/

end ThreePoint

/- BEGIN CERT3 -/

/-!
# Kronecker-substitution checking of polynomial identities

A polynomial `e : Ex` in three variables `u, v, t` with integer coefficients is given as an
expression tree.  To prove `∀ u v t : ℝ, e(u,v,t) = 0` it suffices to check, with kernel
(GMP) integer arithmetic, that
* every exponent of every variable is `< D`,
* the `ℓ¹`-norm of the (uncollected) coefficients is `< 2^w`,
* the value of `e` at the integers `u = 2^w`, `v = 2^(w D)`, `t = 2^(w D²)` is `0`.
-/

namespace Kron

namespace Ex

end Ex

lemma sumT_append {R : Type*} [CommRing R] (W : ℕ → ℕ → ℕ → R) (L M : List Ex.Term) :
    sumT W (L ++ M) = sumT W L + sumT W M := by
  simp [sumT]

lemma sumT_scale {R : Type*} [CommRing R] (W : ℕ → ℕ → ℕ → R)
    (hW : ∀ a b c a' b' c', W (a + a') (b + b') (c + c') = W a b c * W a' b' c')
    (x : Ex.Term) (M : List Ex.Term) :
    sumT W (M.map fun y => (x.1 * y.1, x.2.1 + y.2.1, x.2.2.1 + y.2.2.1, x.2.2.2 + y.2.2.2))
      = (x.1 : R) * W x.2.1 x.2.2.1 x.2.2.2 * sumT W M := by
  induction M with
  | nil => simp [sumT]
  | cons y M ih =>
    simp only [List.map_cons, sumT, List.sum_cons] at ih ⊢
    rw [ih, hW]
    push_cast
    ring

lemma sumT_flatMap {R : Type*} [CommRing R] (W : ℕ → ℕ → ℕ → R)
    (hW : ∀ a b c a' b' c', W (a + a') (b + b') (c + c') = W a b c * W a' b' c')
    (L M : List Ex.Term) :
    sumT W (L.flatMap fun x => M.map fun y =>
      (x.1 * y.1, x.2.1 + y.2.1, x.2.2.1 + y.2.2.1, x.2.2.2 + y.2.2.2)) = sumT W L * sumT W M := by
  induction L with
  | nil => simp [sumT]
  | cons x L ih =>
    rw [List.flatMap_cons, sumT_append, ih, sumT_scale W hW]
    simp only [sumT, List.map_cons, List.sum_cons]
    ring

namespace Ex

lemma evalW_eq_sumT {R : Type*} [CommRing R] (W : ℕ → ℕ → ℕ → R)
    (hW : ∀ a b c a' b' c', W (a + a') (b + b') (c + c') = W a b c * W a' b' c')
    (h0 : W 0 0 0 = 1) (e : Ex) : evalW W e = sumT W e.toList := by
  induction e with
  | c n => simp [evalW, toList, sumT, h0]
  | mon a b d => simp [evalW, toList, sumT]
  | add p q ihp ihq => simp [evalW, toList, sumT_append, ihp, ihq]
  | mul p q ihp ihq => rw [evalW, toList, sumT_flatMap W hW, ihp, ihq]

lemma Wr_add (u v t : ℝ) (a b c a' b' c' : ℕ) :
    Wr u v t (a + a') (b + b') (c + c') = Wr u v t a b c * Wr u v t a' b' c' := by
  simp only [Wr, pow_add]; ring

lemma Wr_zero (u v t : ℝ) : Wr u v t 0 0 0 = 1 := by simp [Wr]

lemma Wk_add (w D a b c a' b' c' : ℕ) :
    Wk w D (a + a') (b + b') (c + c') = Wk w D a b c * Wk w D a' b' c' := by
  simp only [Wk]
  rw [← Nat.cast_mul, ← pow_add]
  congr 2
  ring

lemma Wk_zero (w D : ℕ) : Wk w D 0 0 0 = 1 := by simp [Wk]

lemma ev_eq (u v t : ℝ) (e : Ex) : e.ev u v t = evalW (Wr u v t) e := by
  induction e with
  | c n => rfl
  | mon a b d => rfl
  | add p q ihp ihq => simp only [ev, evalW, ihp, ihq]
  | mul p q ihp ihq => simp only [ev, evalW, ihp, ihq]

lemma kev_eq (w D : ℕ) (e : Ex) : e.kev w D = evalW (Wk w D) e := by
  induction e with
  | c n => rfl
  | mon a b d => rfl
  | add p q ihp ihq => simp only [kev, evalW, ihp, ihq]
  | mul p q ihp ihq => simp only [kev, evalW, ihp, ihq]

lemma sumAbs_scale (x : Term) (M : List Term) :
    sumAbs (M.map fun y => (x.1 * y.1, x.2.1 + y.2.1, x.2.2.1 + y.2.2.1, x.2.2.2 + y.2.2.2))
      = x.1.natAbs * sumAbs M := by
  induction M with
  | nil => simp [sumAbs]
  | cons y M ih =>
    simp only [List.map_cons, sumAbs, List.sum_cons] at ih ⊢
    rw [ih, Int.natAbs_mul]
    ring

lemma sumAbs_flatMap (L M : List Term) :
    sumAbs (L.flatMap fun x => M.map fun y =>
      (x.1 * y.1, x.2.1 + y.2.1, x.2.2.1 + y.2.2.1, x.2.2.2 + y.2.2.2)) = sumAbs L * sumAbs M := by
  induction L with
  | nil => simp [sumAbs]
  | cons x L ih =>
    rw [List.flatMap_cons]
    simp only [sumAbs, List.map_append, List.sum_append] at ih ⊢
    have := sumAbs_scale x M
    simp only [sumAbs] at this
    rw [this, ih]
    simp only [List.map_cons, List.sum_cons]
    ring

lemma sumAbs_toList (e : Ex) : sumAbs e.toList = e.l1 := by
  induction e with
  | c n => simp [toList, l1, sumAbs]
  | mon a b d => simp [toList, l1, sumAbs]
  | add p q ihp ihq =>
    simp only [toList, l1, ← ihp, ← ihq, sumAbs, List.map_append, List.sum_append]
  | mul p q ihp ihq => rw [toList, sumAbs_flatMap, ihp, ihq, l1]

lemma deg_le (e : Ex) :
    ∀ x ∈ e.toList, x.2.1 ≤ e.dx ∧ x.2.2.1 ≤ e.dy ∧ x.2.2.2 ≤ e.dz := by
  induction e with
  | c n => intro x hx; simp [toList] at hx; subst hx; simp [dx, dy, dz]
  | mon a b d => intro x hx; simp [toList] at hx; subst hx; simp [dx, dy, dz]
  | add p q ihp ihq =>
    intro x hx
    rcases List.mem_append.1 hx with h | h
    · obtain ⟨h1, h2, h3⟩ := ihp x h
      exact ⟨h1.trans (le_max_left _ _), h2.trans (le_max_left _ _), h3.trans (le_max_left _ _)⟩
    · obtain ⟨h1, h2, h3⟩ := ihq x h
      exact ⟨h1.trans (le_max_right _ _), h2.trans (le_max_right _ _),
        h3.trans (le_max_right _ _)⟩
  | mul p q ihp ihq =>
    intro x hx
    simp only [toList, List.mem_flatMap, List.mem_map] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := hx
    obtain ⟨a1, a2, a3⟩ := ihp y hy
    obtain ⟨b1, b2, b3⟩ := ihq z hz
    exact ⟨by simp only [dx]; omega, by simp only [dy]; omega, by simp only [dz]; omega⟩

end Ex

open Ex

lemma regroup {R : Type*} [CommRing R] (D N : ℕ) (F : ℕ → R) (L : List Term)
    (hL : ∀ x ∈ L, code D x < N) :
    (L.map fun x => (x.1 : R) * F (code D x)).sum
      = ∑ k ∈ Finset.range N, (coefk D L k : R) * F k := by
  induction L with
  | nil => simp [coefk]
  | cons x L ih =>
    have hx : code D x < N := hL x (List.mem_cons_self)
    have ih' := ih (fun y hy => hL y (List.mem_cons_of_mem _ hy))
    simp only [List.map_cons, List.sum_cons, ih', coefk]
    have h1 : ∀ k ∈ Finset.range N,
        (((if code D x = k then x.1 else 0) + coefk D L k : ℤ) : R) * F k
          = (if code D x = k then (x.1 : R) * F k else 0) + (coefk D L k : R) * F k := by
      intro k _
      split_ifs <;> push_cast <;> ring
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_ite_eq]
    simp [hx]

lemma natAbs_coefk_le (D : ℕ) (L : List Term) (k : ℕ) : (coefk D L k).natAbs ≤ sumAbs L := by
  induction L with
  | nil => simp [coefk, sumAbs]
  | cons x L ih =>
    simp only [coefk, sumAbs, List.map_cons, List.sum_cons] at ih ⊢
    refine (Int.natAbs_add_le _ _).trans ?_
    have : (if code D x = k then x.1 else 0).natAbs ≤ x.1.natAbs := by
      split_ifs <;> simp
    omega

/-- Signed-digit uniqueness: a vanishing sum of digits of absolute value `< B` has all digits `0`. -/
lemma digit_unique (B : ℕ) (a : ℕ → ℤ) : ∀ N : ℕ, (∀ k < N, |a k| < B) →
    ∑ k ∈ Finset.range N, a k * (B : ℤ) ^ k = 0 → ∀ k < N, a k = 0 := by
  intro N
  induction N generalizing a with
  | zero => intro _ _ k hk; omega
  | succ N ih =>
    intro hb hs
    rw [Finset.sum_range_succ'] at hs
    have hB : (0 : ℤ) < B := lt_of_le_of_lt (abs_nonneg _) (hb 0 (Nat.succ_pos N))
    have hs' : ∑ k ∈ Finset.range N, a (k + 1) * (B : ℤ) ^ (k + 1) + a 0 * (B : ℤ) ^ 0 = 0 := hs
    have hfac : ∑ k ∈ Finset.range N, a (k + 1) * (B : ℤ) ^ (k + 1)
        = (B : ℤ) * ∑ k ∈ Finset.range N, a (k + 1) * (B : ℤ) ^ k := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [hfac] at hs'
    have hdvd : (B : ℤ) ∣ a 0 := by
      refine ⟨-∑ k ∈ Finset.range N, a (k + 1) * (B : ℤ) ^ k, ?_⟩
      simp only [pow_zero, mul_one] at hs'
      linarith
    have ha0 : a 0 = 0 := Int.eq_zero_of_abs_lt_dvd hdvd (hb 0 (Nat.succ_pos N))
    have hsum : ∑ k ∈ Finset.range N, a (k + 1) * (B : ℤ) ^ k = 0 := by
      rw [ha0] at hs'
      simp only [pow_zero, mul_one, add_zero] at hs'
      rcases mul_eq_zero.1 hs' with h | h
      · exact absurd h hB.ne'
      · exact h
    have := ih (fun k => a (k + 1)) (fun k hk => hb (k + 1) (by omega)) hsum
    intro k hk
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [h0]; exact ha0
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      exact this j (by omega)

lemma decode_code {D a b d : ℕ} (ha : a < D) (hb : b < D) (hd : d < D) :
    (a + D * b + D * D * d) % D = a ∧ (a + D * b + D * D * d) / D % D = b ∧
      (a + D * b + D * D * d) / D / D = d ∧ a + D * b + D * D * d < D * D * D := by
  have hD : 0 < D := by omega
  have e1 : a + D * b + D * D * d = a + D * (b + D * d) := by ring
  have h1 : (a + D * b + D * D * d) / D = b + D * d := by
    rw [e1, Nat.add_mul_div_left _ _ hD, Nat.div_eq_of_lt ha, zero_add]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
  · rw [h1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
  · rw [h1, Nat.add_mul_div_left _ _ hD, Nat.div_eq_of_lt hb, zero_add]
  · calc a + D * b + D * D * d < D + D * b + D * D * d := by omega
      _ = D * (b + 1) + D * D * d := by ring
      _ ≤ D * D + D * D * d := by
          have : D * (b + 1) ≤ D * D := Nat.mul_le_mul_left D hb
          omega
      _ = D * D * (d + 1) := by ring
      _ ≤ D * D * D := Nat.mul_le_mul_left _ hd

/-- **Soundness of the Kronecker check.** -/
theorem Ex.ev_eq_zero_of_kev (e : Ex) (w D : ℕ) (hx : e.dx < D) (hy : e.dy < D)
    (hz : e.dz < D) (hl : e.l1 < 2 ^ w) (hk : e.kev w D = 0) (u v t : ℝ) :
    e.ev u v t = 0 := by
  have hdeg : ∀ x ∈ e.toList, x.2.1 < D ∧ x.2.2.1 < D ∧ x.2.2.2 < D := by
    intro x hxm
    obtain ⟨h1, h2, h3⟩ := Ex.deg_le e x hxm
    exact ⟨by omega, by omega, by omega⟩
  have hcode : ∀ x ∈ e.toList, code D x < D * D * D := fun x hxm =>
    (decode_code (hdeg x hxm).1 (hdeg x hxm).2.1 (hdeg x hxm).2.2).2.2.2
  -- the Kronecker value, regrouped by monomial
  have h1 : e.kev w D = ∑ k ∈ Finset.range (D * D * D),
      (coefk D e.toList k) * (((2 ^ w : ℕ) : ℤ) ^ k) := by
    rw [Ex.kev_eq, Ex.evalW_eq_sumT _ (Ex.Wk_add w D) (Ex.Wk_zero w D)]
    have := regroup D (D * D * D) (fun k => (((2 ^ (w * k) : ℕ)) : ℤ)) e.toList hcode
    refine Eq.trans this ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pow_mul]; push_cast; rfl
  have hbound : ∀ k < D * D * D, |coefk D e.toList k| < ((2 ^ w : ℕ) : ℤ) := by
    intro k _
    have h := natAbs_coefk_le D e.toList k
    rw [Ex.sumAbs_toList] at h
    have : (coefk D e.toList k).natAbs < 2 ^ w := lt_of_le_of_lt h hl
    rw [← Int.natCast_natAbs]
    exact_mod_cast this
  have hzero := digit_unique (2 ^ w) (coefk D e.toList) (D * D * D) hbound (h1 ▸ hk)
  -- the real value, regrouped by monomial
  have h2 : e.ev u v t = ∑ k ∈ Finset.range (D * D * D), (coefk D e.toList k : ℝ) *
      (u ^ (k % D) * v ^ (k / D % D) * t ^ (k / D / D)) := by
    rw [Ex.ev_eq, Ex.evalW_eq_sumT _ (Ex.Wr_add u v t) (Ex.Wr_zero u v t)]
    have := regroup D (D * D * D) (fun k => u ^ (k % D) * v ^ (k / D % D) * t ^ (k / D / D))
      e.toList hcode
    simp only [sumT]
    rw [← this]
    congr 1
    refine List.map_congr_left fun x hxm => ?_
    obtain ⟨p1, p2, p3⟩ := hdeg x hxm
    obtain ⟨q1, q2, q3, -⟩ := decode_code p1 p2 p3
    simp only [code, q1, q2, q3, Ex.Wr]
  rw [h2]
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [hzero k (Finset.mem_range.1 hk)]
  simp

end Kron

/-! ## Builders for `Ex` with evaluation lemmas -/

namespace Kron
namespace Ex

variable (u v t : ℝ)

@[simp] lemma ev_c (n : ℤ) : (c n).ev u v t = n := rfl

@[simp] lemma ev_mon (a b d : ℕ) : (mon a b d).ev u v t = u ^ a * v ^ b * t ^ d := rfl

@[simp] lemma ev_add (p q : Ex) : (add p q).ev u v t = p.ev u v t + q.ev u v t := rfl

@[simp] lemma ev_mul (p q : Ex) : (mul p q).ev u v t = p.ev u v t * q.ev u v t := rfl

@[simp] lemma ev_U : U.ev u v t = u := by simp [U]

@[simp] lemma ev_V : V.ev u v t = v := by simp [V]

@[simp] lemma ev_T : T.ev u v t = t := by simp [T]

@[simp] lemma ev_neg (e : Ex) : (neg e).ev u v t = - e.ev u v t := by simp [neg]

@[simp] lemma ev_sub (e f : Ex) : (sub e f).ev u v t = e.ev u v t - f.ev u v t := by
  simp [sub, sub_eq_add_neg]

@[simp] lemma ev_smul (a : ℤ) (e : Ex) : (smul a e).ev u v t = a * e.ev u v t := by simp [smul]

@[simp] lemma ev_sq (e : Ex) : (sq e).ev u v t = e.ev u v t ^ 2 := by simp [sq, pow_two]

lemma ev_sumE (l : List Ex) : (sumE l).ev u v t = (l.map fun e => e.ev u v t).sum := by
  induction l with
  | nil => simp [sumE]
  | cons e l ih => simpa [sumE] using congrArg (fun x => e.ev u v t + x) ih

lemma list_sum_range_map (f : ℕ → ℝ) (r : ℕ) :
    ((List.range r).map f).sum = ∑ i ∈ Finset.range r, f i := by
  induction r with
  | zero => simp
  | succ r ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
                 simp

lemma ev_sumRange (r : ℕ) (f : ℕ → Ex) :
    (sumRange r f).ev u v t = ∑ i ∈ Finset.range r, (f i).ev u v t := by
  rw [sumRange, ev_sumE, List.map_map]
  exact list_sum_range_map (fun i => (f i).ev u v t) r

/-! ### Substitution of variables by variables or `1` -/

end Ex
end Kron

/- BEGIN CERT1 -/
section Cert1Block

open Kron Kron.Ex

namespace Cert

open ThreePoint

/-! ## `Q_k` as a polynomial expression -/

lemma ev_q3E (u v t : ℝ) : ∀ k, (q3E k).ev u v t = Q3 k u v t
  | 0 => by simp [q3E, Q3]
  | 1 => by simp [q3E, Q3]
  | k + 2 => by
    simp only [q3E, Q3, ev_sub, ev_mul, ev_smul, ev_T, ev_U, ev_V, ev_c, ev_sq,
      ev_q3E u v t (k + 1), ev_q3E u v t k]
    push_cast
    ring

/-! ## Quadratic forms: `L D Lᵀ` plus a diagonally dominant remainder -/

lemma qform_dd_nonneg (r : ℕ) (Δ : ℕ → ℕ → ℝ) (x : ℕ → ℝ)
    (hs : ∀ i ∈ Finset.range r, ∀ j ∈ Finset.range r, Δ i j = Δ j i)
    (hdd : ∀ i ∈ Finset.range r,
      ∑ j ∈ Finset.range r, (if i = j then 0 else |Δ i j|) ≤ Δ i i) :
    0 ≤ ∑ i ∈ Finset.range r, ∑ j ∈ Finset.range r, x i * Δ i j * x j := by
  set s := Finset.range r with hs_def
  have key : ∀ i j, (if i = j then Δ i i * x i ^ 2 else 0)
      - (if i = j then 0 else |Δ i j|) * (x i ^ 2 + x j ^ 2) / 2 ≤ x i * Δ i j * x j := by
    intro i j
    by_cases h : i = j
    · subst h; rw [if_pos rfl, if_pos rfl]; nlinarith
    · rw [if_neg h, if_neg h]
      have h1 : 2 * (|x i| * |x j|) ≤ |x i| ^ 2 + |x j| ^ 2 := by
        nlinarith [sq_nonneg (|x i| - |x j|)]
      rw [sq_abs, sq_abs] at h1
      have h2 : |x i * Δ i j * x j| = |Δ i j| * (|x i| * |x j|) := by
        rw [abs_mul, abs_mul]; ring
      have h3 : -(x i * Δ i j * x j) ≤ |x i * Δ i j * x j| := neg_le_abs _
      rw [h2] at h3
      have h4 : 0 ≤ |Δ i j| := abs_nonneg _
      nlinarith
  have hsum := Finset.sum_le_sum (s := s) fun i _ =>
    Finset.sum_le_sum (s := s) fun j _ => key i j
  refine le_trans ?_ hsum
  simp only [Finset.sum_sub_distrib]
  have e1 : ∑ i ∈ s, ∑ j ∈ s, (if i = j then Δ i i * x i ^ 2 else 0)
      = ∑ i ∈ s, Δ i i * x i ^ 2 := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_ite_eq]; simp [hi]
  set o : ℕ → ℕ → ℝ := fun i j => if i = j then 0 else |Δ i j| with ho
  have osymm : ∀ i ∈ s, ∀ j ∈ s, o j i = o i j := by
    intro i hi j hj
    simp only [ho]
    by_cases h : i = j
    · subst h; simp
    · have h' : ¬ j = i := fun e => h e.symm
      rw [if_neg h, if_neg h', hs i hi j hj]
  have e2 : ∑ i ∈ s, ∑ j ∈ s, o i j * (x i ^ 2 + x j ^ 2) / 2
      = ∑ i ∈ s, (∑ j ∈ s, o i j) * x i ^ 2 := by
    have ha : ∑ i ∈ s, ∑ j ∈ s, o i j * (x i ^ 2 + x j ^ 2) / 2
        = ∑ i ∈ s, ∑ j ∈ s, o i j * x i ^ 2 / 2 + ∑ i ∈ s, ∑ j ∈ s, o i j * x j ^ 2 / 2 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have hb : ∑ i ∈ s, ∑ j ∈ s, o i j * x j ^ 2 / 2 = ∑ i ∈ s, ∑ j ∈ s, o i j * x i ^ 2 / 2 := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
      rw [osymm j hj i hi]
    have hc : ∑ i ∈ s, ∑ j ∈ s, o i j * x i ^ 2 / 2
        = (∑ i ∈ s, (∑ j ∈ s, o i j) * x i ^ 2) / 2 := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul, Finset.sum_div]
    rw [ha, hb, hc]; ring
  rw [e1, e2, ← Finset.sum_sub_distrib]
  refine Finset.sum_nonneg fun i hi => ?_
  have := hdd i hi
  nlinarith [sq_nonneg (x i)]

/-! ## Integer data of a positive semidefinite block -/

namespace Blk

lemma list_sum_range_map {M : Type*} [AddCommMonoid M] (f : ℕ → M) (r : ℕ) :
    ((List.range r).map f).sum = ∑ i ∈ Finset.range r, f i := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

lemma ok_parts {r : ℕ} {b : Blk} (h : b.ok r = true) :
    (∀ i ∈ Finset.range r, 0 ≤ b.dq i) ∧
    (∀ i ∈ Finset.range r, ∀ j ∈ Finset.range r, b.del i j = b.del j i) ∧
    (∀ i ∈ Finset.range r,
      ∑ j ∈ Finset.range r, (if i = j then (0 : ℤ) else |b.del i j|) ≤ b.del i i) := by
  simp only [ok, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨fun i hi => (h i (Finset.mem_range.1 hi)).1.1, fun i hi j hj => ?_, fun i hi => ?_⟩
  · exact (h i (Finset.mem_range.1 hi)).1.2 j (Finset.mem_range.1 hj)
  · have := (h i (Finset.mem_range.1 hi)).2
    rwa [list_sum_range_map] at this

/-- Nonnegativity of the quadratic form of a checked block. -/
lemma qf_nonneg {r : ℕ} {b : Blk} (h : b.ok r = true) (x : ℕ → ℝ) :
    0 ≤ ∑ q ∈ Finset.range r, (b.dq q : ℝ) * (∑ a ∈ Finset.range r, (b.lq q a : ℝ) * x a) ^ 2
      + ∑ a ∈ Finset.range r, ∑ c ∈ Finset.range r, x a * (b.del a c : ℝ) * x c := by
  obtain ⟨hd, hs, hdd⟩ := ok_parts h
  refine add_nonneg (Finset.sum_nonneg fun q hq => ?_) ?_
  · exact mul_nonneg (by exact_mod_cast hd q hq) (sq_nonneg _)
  · refine qform_dd_nonneg r (fun a c => (b.del a c : ℝ)) x
      (fun i hi j hj => by simp only [hs i hi j hj]) (fun i hi => ?_)
    have := hdd i hi
    have h2 : ((∑ j ∈ Finset.range r, (if i = j then (0 : ℤ) else |b.del i j|) : ℤ) : ℝ)
        ≤ ((b.del i i : ℤ) : ℝ) := by exact_mod_cast this
    push_cast at h2
    refine le_trans (le_of_eq ?_) h2
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp

end Blk

end Cert

end Cert1Block

/- BEGIN CERT3FILE -/
section Cert3Block

open Kron Kron.Ex

namespace Cert

open ThreePoint

/-! ## Helpers: zero-skipping scaling, monomial-preserving substitution -/

lemma ev_smulNZ (a : ℤ) (e : Ex) (u v t : ℝ) : (smulNZ a e).ev u v t = a * e.ev u v t := by
  unfold smulNZ
  split_ifs with h
  · simp [h]
  · simp

lemma varVal_pow (u v t : ℝ) (i a : ℕ) :
    varVal u v t i ^ a = u ^ (if i = 0 then a else 0) * v ^ (if i = 1 then a else 0)
      * t ^ (if i = 2 then a else 0) := by
  match i with
  | 0 => simp [varVal]
  | 1 => simp [varVal]
  | 2 => simp [varVal]
  | i + 3 => simp [varVal]

lemma ev_sbst (i j k : ℕ) (e : Ex) (u v t : ℝ) :
    (sbst i j k e).ev u v t = e.ev (varVal u v t i) (varVal u v t j) (varVal u v t k) := by
  induction e with
  | c n => simp [sbst]
  | mon a b d =>
    simp only [sbst, ev_mon, pow_add, varVal_pow]
    ring
  | add p q ihp ihq => simp [sbst, ihp, ihq]
  | mul p q ihp ihq => simp [sbst, ihp, ihq]

/-! ## The `F`-blocks: `Λ · Fp(u,v)` -/

lemma sum3_comm (r : ℕ) (f : ℕ → ℕ → ℕ → ℝ) :
    ∑ a ∈ Finset.range r, ∑ c ∈ Finset.range r, ∑ q ∈ Finset.range r, f a c q
      = ∑ q ∈ Finset.range r, ∑ a ∈ Finset.range r, ∑ c ∈ Finset.range r, f a c q := by
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm]
  exact Finset.sum_comm

lemma cast_ent (r : ℕ) (b : Blk) (a c : ℕ) :
    (b.ent r a c : ℝ) = (∑ q ∈ Finset.range r, (b.dq q : ℝ) * b.lq q a * b.lq q c)
      + b.del a c := by
  simp only [Blk.ent, Int.cast_add, Blk.list_sum_range_map]
  push_cast
  rfl

lemma ev_fpE (r : ℕ) (b : Blk) (u v t : ℝ) :
    (fpE r b).ev u v t
      = ∑ a ∈ Finset.range r, ∑ c ∈ Finset.range r, (b.ent r a c : ℝ) * u ^ a * v ^ c := by
  simp only [fpE, ev_add, ev_sumRange, ev_smulNZ, ev_mul, ev_mon, pow_zero, mul_one, one_mul]
  have h1 : ∀ q ∈ Finset.range r, (b.dq q : ℝ) * ((∑ a ∈ Finset.range r, (b.lq q a : ℝ) * u ^ a)
      * (∑ c ∈ Finset.range r, (b.lq q c : ℝ) * v ^ c))
      = ∑ a ∈ Finset.range r, ∑ c ∈ Finset.range r,
        (b.dq q : ℝ) * b.lq q a * b.lq q c * u ^ a * v ^ c := by
    intro q _
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  rw [Finset.sum_congr rfl h1]
  have h2 : ∀ a ∈ Finset.range r, ∀ c ∈ Finset.range r, (b.ent r a c : ℝ) * u ^ a * v ^ c
      = (∑ q ∈ Finset.range r, (b.dq q : ℝ) * b.lq q a * b.lq q c * u ^ a * v ^ c)
        + (b.del a c : ℝ) * (u ^ a * v ^ c) := by
    intro a _ c _
    rw [cast_ent, add_mul, add_mul, Finset.sum_mul, Finset.sum_mul]
    congr 1
    ring
  rw [Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun c hc => h2 a ha c hc]
  simp only [Finset.sum_add_distrib]
  rw [← sum3_comm r (fun a c q => (b.dq q : ℝ) * b.lq q a * b.lq q c * u ^ a * v ^ c)]

/-! ## Block matrices and their quadratic forms -/

lemma sum_fin_eq_range (m : ℕ) (f : ℕ → ℕ → ℝ) :
    ∑ a : Fin m, ∑ b : Fin m, f a b = ∑ a ∈ Finset.range m, ∑ b ∈ Finset.range m, f a b := by
  rw [← Fin.sum_univ_eq_sum_range (fun a => ∑ b ∈ Finset.range m, f a b) m]
  exact Finset.sum_congr rfl fun a _ => Fin.sum_univ_eq_sum_range (fun b => f a b) m

lemma ev_fkE (r : ℕ) (b : Blk) (k : ℕ) (u v t : ℝ) :
    (fkE r b k).ev u v t = ∑ a ∈ Finset.range r, ∑ c ∈ Finset.range r,
      (b.ent r a c : ℝ) * (u ^ a * v ^ c * Q3 k u v t) := by
  rw [fkE, ev_mul, ev_fpE, ev_q3E, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

lemma matDot_fmat_Y3 (r Lam : ℕ) (b : Blk) (k : ℕ) (u v t : ℝ) :
    matDot (fmat r Lam b) (Y3 r k u v t) = (fkE r b k).ev u v t / Lam := by
  have h := sum_fin_eq_range r
    (fun a c => (b.ent r a c : ℝ) / Lam * (u ^ a * v ^ c * Q3 k u v t))
  simp only [matDot, fmat, Y3, Matrix.of_apply]
  refine h.trans ?_
  rw [ev_fkE, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

lemma Blk.ent_comm {r : ℕ} {b : Blk} (h : b.ok r = true) {a c : ℕ} (ha : a < r) (hc : c < r) :
    b.ent r a c = b.ent r c a := by
  obtain ⟨-, hs, -⟩ := Blk.ok_parts h
  simp only [Blk.ent, hs a (Finset.mem_range.2 ha) c (Finset.mem_range.2 hc),
    Blk.list_sum_range_map]
  congr 1
  exact Finset.sum_congr rfl fun q _ => by ring

lemma Blk.qf_ent (r : ℕ) (b : Blk) (x : ℕ → ℝ) :
    ∑ a ∈ Finset.range r, ∑ c ∈ Finset.range r, x a * (b.ent r a c : ℝ) * x c
      = ∑ q ∈ Finset.range r, (b.dq q : ℝ) * (∑ a ∈ Finset.range r, (b.lq q a : ℝ) * x a) ^ 2
        + ∑ a ∈ Finset.range r, ∑ c ∈ Finset.range r, x a * (b.del a c : ℝ) * x c := by
  have h1 : ∀ a c, x a * (b.ent r a c : ℝ) * x c
      = (∑ q ∈ Finset.range r, (b.dq q : ℝ) * (b.lq q a * x a) * (b.lq q c * x c))
        + x a * (b.del a c : ℝ) * x c := by
    intro a c
    rw [cast_ent, mul_add, add_mul, Finset.mul_sum, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  simp only [h1, Finset.sum_add_distrib]
  congr 1
  rw [sum3_comm r (fun a c q => (b.dq q : ℝ) * (b.lq q a * x a) * (b.lq q c * x c))]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [_root_.sq, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

lemma Blk.qf_ent_nonneg {r : ℕ} {b : Blk} (h : b.ok r = true) (x : ℕ → ℝ) :
    0 ≤ ∑ a ∈ Finset.range r, ∑ c ∈ Finset.range r, x a * (b.ent r a c : ℝ) * x c := by
  rw [Blk.qf_ent]
  exact Blk.qf_nonneg h x

lemma fmat_psd {r : ℕ} (Lam : ℕ) {b : Blk} (h : b.ok r = true) : (fmat r Lam b).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · refine Matrix.IsHermitian.ext fun i j => ?_
    simp only [fmat, Matrix.of_apply, star_trivial]
    rw [Blk.ent_comm h j.2 i.2]
  · intro x
    set x' : ℕ → ℝ := fun a => if ha : a < r then x ⟨a, ha⟩ else 0 with hx'
    have h0 := div_nonneg (Blk.qf_ent_nonneg h x') (Nat.cast_nonneg (α := ℝ) Lam)
    have hx'' : ∀ i : Fin r, x' i = x i := fun i => by simp [hx', i.2]
    have h1 : (∑ a ∈ Finset.range r, ∑ c ∈ Finset.range r, x' a * (b.ent r a c : ℝ) * x' c)
        / Lam = ∑ a : Fin r, ∑ c : Fin r, x a * ((b.ent r a c : ℝ) / Lam * x c) := by
      rw [← sum_fin_eq_range r (fun a c => x' a * (b.ent r a c : ℝ) * x' c), Finset.sum_div]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [hx'', hx'']
      ring
    rw [h1] at h0
    simpa [dotProduct, Matrix.mulVec, fmat, Matrix.of_apply, star_trivial, Finset.mul_sum]
      using h0

/-! ## Symmetrisation and the `F`-part of the identity -/

/-! ## SOS blocks with multipliers -/

lemma ev_sqfE (b : Blk) (zs : List (ℕ × ℕ × ℕ)) (u v t : ℝ) :
    (sqfE b zs).ev u v t
      = ∑ q ∈ Finset.range zs.length, (b.dq q : ℝ)
          * (∑ a ∈ Finset.range zs.length, (b.lq q a : ℝ) * zval zs u v t a) ^ 2
        + ∑ a ∈ Finset.range zs.length, ∑ c ∈ Finset.range zs.length,
          zval zs u v t a * (b.del a c : ℝ) * zval zs u v t c := by
  simp only [sqfE, ev_add, ev_sumRange, ev_smulNZ, ev_sq, zmon, zzmon, ev_mon, zval, pow_add]
  congr 1
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  ring

lemma sqfE_nonneg {b : Blk} {zs : List (ℕ × ℕ × ℕ)} (h : b.ok zs.length = true) (u v t : ℝ) :
    0 ≤ (sqfE b zs).ev u v t := by
  rw [ev_sqfE]
  exact Blk.qf_nonneg h (zval zs u v t)

lemma codeE_nonneg (an : ℤ) (ad : ℕ) (code : ℕ) {u v t : ℝ} (h : GramCut an ad u v t) :
    0 ≤ (codeE an ad code).ev u v t := by
  obtain ⟨⟨hu, hv, ht, hd⟩, hau, hav, hat⟩ := h
  have hu' := abs_le.1 ((sq_le_one_iff_abs_le_one u).1 hu)
  have hv' := abs_le.1 ((sq_le_one_iff_abs_le_one v).1 hv)
  have ht' := abs_le.1 ((sq_le_one_iff_abs_le_one t).1 ht)
  match code with
  | 0 => simp only [codeE, ev_sub, ev_c, ev_sq, ev_U]; push_cast; linarith
  | 1 => simp only [codeE, ev_sub, ev_c, ev_sq, ev_V]; push_cast; linarith
  | 2 => simp only [codeE, ev_sub, ev_c, ev_sq, ev_T]; push_cast; linarith
  | 3 =>
    simp only [codeE, ev_sub, ev_add, ev_c, ev_smul, ev_mul, ev_sq, ev_U, ev_V, ev_T]
    push_cast
    linarith
  | 4 => simp only [codeE, ev_sub, ev_c, ev_U]; push_cast; linarith [hu'.2]
  | 5 => simp only [codeE, ev_add, ev_c, ev_U]; push_cast; linarith [hu'.1]
  | 6 => simp only [codeE, ev_sub, ev_c, ev_V]; push_cast; linarith [hv'.2]
  | 7 => simp only [codeE, ev_add, ev_c, ev_V]; push_cast; linarith [hv'.1]
  | 8 => simp only [codeE, ev_sub, ev_c, ev_T]; push_cast; linarith [ht'.2]
  | 9 => simp only [codeE, ev_add, ev_c, ev_T]; push_cast; linarith [ht'.1]
  | 10 => simp only [codeE, ev_sub, ev_smul, ev_c, ev_U]; push_cast; linarith
  | 11 => simp only [codeE, ev_sub, ev_smul, ev_c, ev_V]; push_cast; linarith
  | 12 => simp only [codeE, ev_sub, ev_smul, ev_c, ev_T]; push_cast; linarith
  | j + 13 => simp only [codeE, ev_c]; norm_num

/-! ## The certificate and its soundness -/

open scoped RealInnerProductSpace

namespace Cert3

end Cert3

namespace Cert3

end Cert3

namespace Cert3

end Cert3

end Cert

end Cert3Block

/- END CERT3 -/

/- BEGIN M2 -/
namespace M2

/-! ## The number field `ℚ(√2, 2 sin (π/5))` -/

namespace K8

/-! ### Rational enclosures and positivity of elements of `K8` -/

end K8

namespace K8

end K8

/-! ### Polynomials with `K8` coefficients: dense lists, lowest degree first -/

namespace Pl

end Pl

open Pl

end M2
/- END M2 -/

/- BEGIN M3 -/
namespace M3

open scoped InnerProductSpace

end M3

/- BEGIN P3ext -/

/-! ## P3: Bregman (Taylor) lower bounds for the Coulomb pair potential (agent7) -/

namespace Base

end Base

/- END P3ext -/

/- BEGIN P1 -/

/-! ## P1: the bipyramid is a critical point of the Coulomb energy on the constraint set (agent7) -/

namespace Reg

open Base

end Reg

/- END P1 -/

/- BEGIN GAUGE -/

/-! ## G: gauge (Procrustes) lemma `exists_gauge` (agent7) -/

namespace Reg

open scoped RealInnerProductSpace

end Reg

/- END GAUGE -/

/- BEGIN P2 -/

/- BEGIN RegB (P2: exact energy identity; needs M0 = namespace Base and the Challenge preamble) -/
namespace RegB

open Base Finset

section vectors

variable (y : Fin 7 → R3)

end vectors

end RegB
/- END RegB -/

/- END P2 -/

/- BEGIN GV -/

namespace GV

open Base

open scoped InnerProductSpace

end GV

/- END GV -/

/- BEGIN TWOREGIME -/

namespace TwoRegime

open scoped InnerProductSpace

end TwoRegime

namespace TwoRegime

open scoped InnerProductSpace
open Base

end TwoRegime

namespace TwoRegime

open scoped InnerProductSpace
open Base

end TwoRegime

/- END TWOREGIME -/

/- BEGIN TR_D -/
namespace TwoRegime

open scoped InnerProductSpace
open Base

end TwoRegime

/- END TR_D -/

/- BEGIN TR_E -/
namespace ThreePoint

open Finset Matrix
open scoped RealInnerProductSpace

section FinalCut

variable {n : ℕ}

end FinalCut

end ThreePoint

namespace TwoRegime

open scoped InnerProductSpace
open Base

end TwoRegime

/- END TR_E -/

/- BEGIN TR_G -/
namespace TwoRegime

open scoped InnerProductSpace
open Base

end TwoRegime

namespace TwoRegime

open scoped InnerProductSpace
open Base

end TwoRegime

/- BEGIN TR_G3 -/
namespace TwoRegime

open scoped InnerProductSpace
open Base

end TwoRegime
/- END TR_G3 -/
/- BEGIN TR_G4 -/
namespace TwoRegime

open scoped InnerProductSpace
open Base

end TwoRegime
/- END TR_G4 -/
/- END TR_G -/

/- BEGIN INTERFACES -/
namespace Interfaces

open Finset Base

end Interfaces
/- END INTERFACES -/

/- BEGIN GLUE -/
namespace Glue

open Finset Base Interfaces

end Glue
/- END GLUE -/

/- BEGIN TR_F -/
namespace EPBounds

open Real

lemma sin_pi_div_five_sq : sin (π / 5) ^ 2 = (5 - √5) / 8 := by
  have h := sin_sq_add_cos_sq (π / 5)
  rw [cos_pi_div_five] at h
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith

lemma sin_two_pi_div_five : sin (2 * π / 5) = sin (π / 5) * ((1 + √5) / 2) := by
  have : 2 * π / 5 = 2 * (π / 5) := by ring
  rw [this, sin_two_mul, cos_pi_div_five]
  ring

end EPBounds
/- END TR_F -/
end ThomsonN7

section RegLocalSection
/- BEGIN REGLOCAL (agent7): perturbative strict local minimality of the pentagonal bipyramid.
   Splice AFTER Level1d (needs GAUGE = exists_gauge, P1/P3ext, Base, TwoRegime.LocalMinAt).
   Pieces in order: Loc1 (H, B3) | QCore1 (certificate defs/lemmas) | Q2 (expansion) | QCore2 (core) | Loc2 (glue). -/
open Real
open scoped RealInnerProductSpace
namespace ThomsonN7
/- BEGIN LOC1 (agent7): exact chart identity (H) and cubic Bregman lower bound (B3) in h = y - P.
   Splice AFTER the GAUGE block (needs P1, P3ext); compiles against Level1b.lean lines 1-3641. -/
namespace Reg
open Base

end Reg

/- END LOC1 -/

end ThomsonN7

/- BEGIN QCORE1 -/
namespace ThomsonN7
namespace Reg

end Reg
end ThomsonN7
/- END QCORE1 -/

/- BEGIN Q2 -/
open Real
open scoped RealInnerProductSpace
namespace ThomsonN7
namespace Reg
open Base

end Reg
end ThomsonN7

/- END Q2 -/

/- BEGIN QCORE2 -/
namespace ThomsonN7
namespace Reg

end Reg
end ThomsonN7
/- END QCORE2 -/

/- BEGIN LOC2 -/
open Real
open scoped RealInnerProductSpace
namespace ThomsonN7
namespace Reg
open Base

/-! ### The atom box for the penalised Hessian certificate -/

end Reg
end ThomsonN7

/- END LOC2 -/

namespace ThomsonN7
namespace Reg

end Reg

end ThomsonN7

/- END REGLOCAL -/
end RegLocalSection

/- BEGIN CASE1 -/
namespace ThomsonN7
namespace CutOneD

theorem peval_padd (p q : List ℤ) (y : ℝ) : peval (padd p q) y = peval p y + peval q y := by
  induction p generalizing q with
  | nil => simp [padd, peval]
  | cons a as ih =>
    cases q with
    | nil => simp [padd, peval]
    | cons b bs => simp only [padd, peval, ih]; push_cast; ring

theorem peval_pscale (c : ℤ) (p : List ℤ) (y : ℝ) : peval (pscale c p) y = c * peval p y := by
  induction p with
  | nil => simp [pscale, peval]
  | cons a as ih =>
    simp only [pscale, List.map_cons, peval] at ih ⊢
    rw [ih]; push_cast; ring

theorem peval_pneg (p : List ℤ) (y : ℝ) : peval (pneg p) y = - peval p y := by
  induction p with
  | nil => simp [pneg, peval]
  | cons a as ih =>
    simp only [pneg, List.map_cons, peval] at ih ⊢
    rw [ih]; push_cast; ring

theorem peval_pmul (p q : List ℤ) (y : ℝ) : peval (pmul p q) y = peval p y * peval q y := by
  induction p with
  | nil => simp [pmul, peval]
  | cons a as ih =>
    simp only [pmul, peval_padd, peval_pscale, peval, ih]; ring

theorem peval_compQ (Q : List ℤ) (y : ℝ) : peval (compQ Q) y = peval Q (1 - 2 * y ^ 2) := by
  induction Q with
  | nil => simp [compQ, peval]
  | cons c cs ih =>
    simp only [compQ, peval_padd, peval_pmul, ih, peval]; ring

theorem peval_eq_zero_of_all (p : List ℤ) (h : p.all (· == 0) = true) (y : ℝ) : peval p y = 0 := by
  induction p with
  | nil => simp [peval]
  | cons a as ih =>
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    simp only [peval, h.1, ih h.2]; simp

end CutOneD
end ThomsonN7

namespace ThomsonN7

namespace Case1Data
open ThomsonN7 ThomsonN7.Cert

end Case1Data

end ThomsonN7

namespace ThomsonN7
namespace Case1

open scoped InnerProductSpace
open ThomsonN7.Cert ThomsonN7.Cert.Cert3

/-! ### Chunked evaluation of the Kronecker check for `Case1Data.cf`

The identity expression `Case1Data.cf.idE` has about 147 000 nodes.  Evaluating `chk` on it in one
kernel call is correct but keeps every intermediate kernel term alive until the end of the
declaration.  Here the same check is split into separate declarations, one per piece of the
expression (`hE`, four `F`-blocks, eight `S`-blocks).  For every expression `e`, `c1Stat w D e`
computes, in one structural pass, the tuple `(ℓ¹-norm, deg u, deg v, deg t, Kronecker value)`
(`c1Stat_eq`).  The 13 pieces are evaluated by `decide +kernel` against exact literals, in 13
separate declarations; the statistics of `Case1Data.cf.idE` follow by the composition lemma
`c1Stat_idE` and closed arithmetic on the literals, and `chk` is then decided by its own definition
(`Nat.log2 ℓ¹ + 1 = 179`, `max deg + 1 = 11`, Kronecker value `0`).  The statement of `cf_ok` is
unchanged; the literals are data found by a program outside Lean and are only ever checked. -/

/-! The 13 pieces, each evaluated in its own declaration (`w = 179`, `D = 11`). -/

end Case1
end ThomsonN7

/- END CASE1 -/

/- BEGIN CASE2RED -/
namespace ThomsonN7
namespace Case1

section Case2Red

open scoped InnerProductSpace
open Base

end Case2Red

end Case1
end ThomsonN7
/- END CASE2RED -/

section Asm_Typed
open Finset Matrix
open scoped RealInnerProductSpace

namespace ThomsonN7
namespace ThreePoint

/-! # Typed (root-dependent) three-point bound

Every root `i` carries its own kernel `s i`; every pair `{i, j}` carries its own minorant `H i j`.
-/

section TypedRoot

/-- **Root positivity.**  For a fixed root `x i`, the Bachoc–Vallentin sum over `(j, l)` of the
unsymmetrised kernel `Y_k` paired with a PSD matrix is nonnegative. -/
theorem matDot_root_nonneg (m k : ℕ) {n : ℕ} (x : Fin n → R3) (hx : ∀ i, ‖x i‖ = 1) (i : Fin n)
    (F : Matrix (Fin m) (Fin m) ℝ) (hF : F.PosSemidef) :
    0 ≤ ∑ j, ∑ l, matDot F (Y3 m k ⟪x i, x j⟫ ⟪x i, x l⟫ ⟪x j, x l⟫) := by
  obtain ⟨r, v, hFv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hF
  have key3 : ∀ X : Fin m → Fin m → Fin r → ℝ,
      ∑ a, ∑ b, ∑ s, X a b s = ∑ s, ∑ a, ∑ b, X a b s := by
    intro X
    calc ∑ a, ∑ b, ∑ s, X a b s = ∑ a, ∑ s, ∑ b, X a b s :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ s, ∑ a, ∑ b, X a b s := Finset.sum_comm
  have hdot : ∀ M : Matrix (Fin m) (Fin m) ℝ, matDot F M = ∑ s, v s ⬝ᵥ M.mulVec (v s) := by
    intro M
    rw [hFv]
    simp only [matDot, Matrix.sum_apply, Matrix.vecMulVec_apply, star_trivial,
      dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
    rw [key3 (fun a b s => v s a * v s b * M a b)]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun b _ => ?_
    ring
  have hswap : ∀ f : Fin n → Fin n → Fin r → ℝ,
      ∑ j, ∑ l, ∑ s, f j l s = ∑ s, ∑ j, ∑ l, f j l s := by
    intro f
    calc ∑ j, ∑ l, ∑ s, f j l s = ∑ j, ∑ s, ∑ l, f j l s :=
          Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _ = ∑ s, ∑ j, ∑ l, f j l s := Finset.sum_comm
  simp only [hdot]
  rw [hswap]
  refine Finset.sum_nonneg fun s _ => ?_
  obtain ⟨e₁, e₂, hfr⟩ := exists_tangent_frame (x i) (hx i)
  exact quad_Y3_nonneg m k (fun j => ⟪x i, x j⟫)
    (fun j l => ⟪x j, x l⟫) (fun j => ⟪e₁, x j⟫) (fun j => ⟪e₂, x j⟫)
    (fun j => (hfr (x j) (x j) (hx j) (hx j)).1)
    (fun j l => (hfr (x j) (x l) (hx j) (hx l)).2) (v s)

end TypedRoot

section TypedComb

variable {n : ℕ}

theorem dsum_os6 (f : Fin n → Fin n → Fin n → ℝ) :
    dsum (fun i j l => f i j l + f i l j + f j i l + f j l i + f l i j + f l j i) = 6 * dsum f := by
  rw [dsum_add, dsum_add, dsum_add, dsum_add, dsum_add]
  have e1 : dsum (fun i j l => f i l j) = dsum f := dsum_swap23 f
  have e2 : dsum (fun i j l => f j i l) = dsum f := dsum_swap12 f
  have e3 : dsum (fun i j l => f j l i) = dsum f := dsum_cyc f
  have e4 : dsum (fun i j l => f l i j) = dsum f := (dsum_cyc (fun i j l => f l i j)).symm
  have e5 : dsum (fun i j l => f l j i) = dsum f := by
    have := dsum_swap12 (fun i j l => f l i j)
    exact this.trans e4
  rw [e1, e2, e3, e4, e5]
  ring

end TypedComb

end ThreePoint
end ThomsonN7

end Asm_Typed

section Asm_Typed2
open Finset Matrix
open scoped RealInnerProductSpace

namespace ThomsonN7
namespace ThreePoint

/-! # Typed three-point bound with free pair shares

Each triple `{i, j, l}` receives a share `W i j l` of the pair function of `{i, j}` (and
similarly for the constant), so that the total over the triples containing a pair is prescribed.
-/

section TypedComb2

variable {n : ℕ}

/-- The decomposition of the full root sum into distinct triples, marginals and constants. -/
theorem sum_root_decomp (s : Fin n → ℝ → ℝ → ℝ → ℝ) (τ : Fin n → Fin n → ℝ)
    (hsymm : ∀ i j, τ i j = τ j i) (hdiag : ∀ i, τ i i = 1) :
    ∑ i, ∑ j, ∑ l, s i (τ i j) (τ i l) (τ j l)
      = dsum (fun i j l => s i (τ i j) (τ i l) (τ j l))
        + ∑ i, ∑ j, (if i ≠ j then mrg s i (τ i j) else 0) + ∑ i, s i 1 1 1 := by
  set f : Fin n → Fin n → Fin n → ℝ := fun i j l => s i (τ i j) (τ i l) (τ j l) with hf
  set g : Fin n → Fin n → ℝ := fun i j => mrg s i (τ i j) with hg
  have hgd : ∀ i, g i i = 3 * s i 1 1 1 := by
    intro i
    simp only [hg, mrg, hdiag]
    ring
  have hQ : ∑ i, ∑ j, (if i ≠ j then g i j else 0)
      = ∑ i, ∑ j, g i j - 3 * ∑ i, s i 1 1 1 := by
    simp only [sum_ne_eq_sub, hgd, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hall := sum_all_eq (n := n) f
  have e1 : ∑ i, ∑ l, f i i l = ∑ i, ∑ j, s i 1 (τ i j) (τ i j) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [hf, hdiag]
  have e2 : ∑ i, ∑ j, f i j i = ∑ i, ∑ j, s i (τ i j) 1 (τ i j) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [hf, hdiag, ← hsymm i j]
  have e3 : ∑ i, ∑ j, f i j j = ∑ i, ∑ j, s i (τ i j) (τ i j) 1 := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [hf, hdiag]
  have e4 : ∑ i, f i i i = ∑ i, s i 1 1 1 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hf, hdiag]
  have eg : ∑ i, ∑ j, g i j
      = ∑ i, ∑ j, s i 1 (τ i j) (τ i j) + ∑ i, ∑ j, s i (τ i j) 1 (τ i j)
        + ∑ i, ∑ j, s i (τ i j) (τ i j) 1 := by
    simp only [hg, mrg, Finset.sum_add_distrib]
  have hall' : ∑ i, ∑ j, ∑ l, f i j l
      = dsum f + ∑ i, ∑ j, g i j - 2 * ∑ i, s i 1 1 1 := by
    rw [hall, e1, e2, e3, e4, eg]
    ring
  show ∑ i, ∑ j, ∑ l, f i j l = dsum f + ∑ i, ∑ j, (if i ≠ j then g i j else 0) + ∑ i, s i 1 1 1
  rw [hall', hQ]
  ring

/-- The sum over ordered distinct triples of a pair share. -/
theorem dsum_share (W : Fin n → Fin n → Fin n → ℝ → ℝ) (τ : Fin n → Fin n → ℝ)
    (Ht : Fin n → Fin n → ℝ → ℝ)
    (hW : ∀ i j, i ≠ j → ∀ t, ∑ l, (if i ≠ l ∧ j ≠ l then W i j l t else 0) = Ht i j t) :
    dsum (fun i j l => W i j l (τ i j))
      = ∑ i, ∑ j, (if i ≠ j then Ht i j (τ i j) else 0) := by
  unfold dsum
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases hij : i = j
  · simp [hij]
  · rw [if_pos hij, ← hW i j hij (τ i j)]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases h1 : i ≠ l ∧ j ≠ l
    · rw [if_pos h1, if_pos ⟨hij, h1⟩]
    · rw [if_neg h1, if_neg (fun h => h1 h.2)]

/-- **Typed three-point bound with free shares (combinatorial form).** -/
theorem typed_bound_comb2 (hn : 3 ≤ n) (s : Fin n → ℝ → ℝ → ℝ → ℝ)
    (H : Fin n → Fin n → ℝ → ℝ) (hH : ∀ i j t, H j i t = H i j t) (e : ℝ)
    (τ : Fin n → Fin n → ℝ) (hsymm : ∀ i j, τ i j = τ j i) (hdiag : ∀ i, τ i i = 1)
    (W : Fin n → Fin n → Fin n → ℝ → ℝ) (c : Fin n → Fin n → Fin n → ℝ)
    (hW : ∀ i j, i ≠ j → ∀ t, ∑ l, (if i ≠ l ∧ j ≠ l then W i j l t else 0)
      = H i j t - mrg s i t - mrg s j t)
    (hc : dsum c = 6 * (e + ∑ i, s i 1 1 1))
    (hroot : 0 ≤ ∑ i, ∑ j, ∑ l, s i (τ i j) (τ i l) (τ j l))
    (hpt : ∀ i j l, i ≠ j → i ≠ l → j ≠ l →
      0 ≤ W i j l (τ i j) + W i l j (τ i l) + W j l i (τ j l) - c i j l
        - (s i (τ i j) (τ i l) (τ j l) + s i (τ i l) (τ i j) (τ l j)
          + s j (τ j i) (τ j l) (τ i l) + s j (τ j l) (τ j i) (τ l i)
          + s l (τ l i) (τ l j) (τ i j) + s l (τ l j) (τ l i) (τ j i))) :
    e ≤ ∑ i, ∑ j ∈ Finset.Ioi i, H i j (τ i j) := by
  set f : Fin n → Fin n → Fin n → ℝ := fun i j l => s i (τ i j) (τ i l) (τ j l) with hf
  set g : Fin n → Fin n → Fin n → ℝ := fun i j l => W i j l (τ i j) with hg
  have h0 : 0 ≤ dsum (fun i j l => (g i j l + g i l j + g j l i) - c i j l
      - (f i j l + f i l j + f j i l + f j l i + f l i j + f l j i)) := by
    refine dsum_nonneg fun i j l hij hil hjl => ?_
    have := hpt i j l hij hil hjl
    simp only [hf, hg, hsymm l j, hsymm l i, hsymm j i] at this ⊢
    linarith
  rw [dsum_sub, dsum_sub, dsum_add, dsum_add, dsum_swap23 g, dsum_cyc g, dsum_os6 f, hc] at h0
  have hg' : dsum g = ∑ i, ∑ j, (if i ≠ j then (H i j (τ i j) - mrg s i (τ i j)
      - mrg s j (τ i j)) else 0) :=
    dsum_share W τ (fun i j t => H i j t - mrg s i t - mrg s j t) hW
  have hdec := sum_root_decomp s τ hsymm hdiag
  have hHH : ∑ i, ∑ j, (if i ≠ j then H i j (τ i j) else 0)
      = 2 * ∑ i, ∑ j ∈ Finset.Ioi i, H i j (τ i j) :=
    sum_ne_eq_two_sum_Ioi (fun i j => H i j (τ i j)) (fun i j => by rw [hH, hsymm])
  have hM : ∑ i, ∑ j, (if i ≠ j then mrg s j (τ i j) else 0)
      = ∑ i, ∑ j, (if i ≠ j then mrg s i (τ i j) else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases h : i = j
    · simp [h]
    · have h' : j ≠ i := fun e => h e.symm
      rw [if_pos h, if_pos h', hsymm]
  have hsplit : ∑ i, ∑ j, (if i ≠ j then (H i j (τ i j) - mrg s i (τ i j) - mrg s j (τ i j)) else 0)
      = ∑ i, ∑ j, (if i ≠ j then H i j (τ i j) else 0)
        - ∑ i, ∑ j, (if i ≠ j then mrg s i (τ i j) else 0)
        - ∑ i, ∑ j, (if i ≠ j then mrg s j (τ i j) else 0) := by
    simp only [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  rw [hg', hsplit, hHH, hM] at h0
  linarith

end TypedComb2

end ThreePoint
end ThomsonN7

end Asm_Typed2

section Asm_Typed7
open Finset Matrix
open scoped RealInnerProductSpace

namespace ThomsonN7
namespace ThreePoint

section Sym

theorem Q3_swap (k : ℕ) (u v t : ℝ) : Q3 k u v t = Q3 k v u t := by
  have key : ∀ k, Q3 k u v t = Q3 k v u t ∧ Q3 (k + 1) u v t = Q3 (k + 1) v u t := by
    intro k
    induction k with
    | zero => exact ⟨by simp only [Q3], by simp only [Q3]; ring⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      show Q3 (k + 2) u v t = Q3 (k + 2) v u t
      simp only [Q3]
      rw [ih.1, ih.2]
      ring
  exact (key k).1

theorem matDot_Y3_swap {m : ℕ} (F : Matrix (Fin m) (Fin m) ℝ) (hF : F.IsSymm) (k : ℕ)
    (u v t : ℝ) : matDot F (Y3 m k u v t) = matDot F (Y3 m k v u t) := by
  unfold matDot Y3
  simp only [Matrix.of_apply]
  rw [Finset.sum_comm (f := fun a b => F a b * (v ^ (a : ℕ) * u ^ (b : ℕ) * Q3 k v u t))]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have h1 : F b a = F a b := by
    have := congrFun (congrFun hF a) b
    simpa [Matrix.transpose_apply] using this
  rw [h1, Q3_swap k v u t]
  ring

end Sym

/-! # The `n = 7` typed instance: two poles (indices `0, 1`) and five ring points (`2..6`) -/

section Typed7

theorem mrg7 (SP SR : ℝ → ℝ → ℝ → ℝ) (i : Fin 7) (t : ℝ) :
    mrg (s7 SP SR) i t = if isP i then gm SP t else gm SR t := by
  unfold mrg s7 gm
  split_ifs <;> rfl

theorem hW7 (SP SR : ℝ → ℝ → ℝ → ℝ) (HA HB HC ψBa ψCb : ℝ → ℝ) :
    ∀ i j : Fin 7, i ≠ j → ∀ t, ∑ l, (if i ≠ l ∧ j ≠ l then W7 SP SR HA HB HC ψBa ψCb i j l t else 0)
      = H7 HA HB HC i j t - mrg (s7 SP SR) i t - mrg (s7 SP SR) j t := by
  intro i j hij t
  rw [mrg7, mrg7]
  fin_cases i <;> fin_cases j <;> simp at hij <;>
    simp [Fin.sum_univ_succ, W7, H7, isP] <;> ring

theorem hc7 (SP SR : ℝ → ℝ → ℝ → ℝ) (e cal cbe : ℝ) :
    dsum (c7 e (SP 1 1 1) (SR 1 1 1) cal cbe) = 6 * (e + ∑ i, s7 SP SR i 1 1 1) := by
  simp [dsum, Fin.sum_univ_succ, c7, isP, s7]
  ring

theorem pole_pair (alo ahi : ℝ) (τ : Fin 7 → Fin 7 → ℝ) (hsymm : ∀ i j, τ i j = τ j i)
    (hcut : alo ≤ τ 0 1 ∧ τ 0 1 ≤ ahi) (i j : Fin 7) (hi : isP i) (hj : isP j) (hij : i ≠ j) :
    alo ≤ τ i j ∧ τ i j ≤ ahi := by
  have h1 : i.val < 2 := hi
  have h2 : j.val < 2 := hj
  have h3 : i.val ≠ j.val := Fin.val_ne_of_ne hij
  rcases (by omega : (i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 0)) with ⟨a, b⟩ | ⟨a, b⟩
  · have ei : i = 0 := Fin.ext (by simpa using a)
    have ej : j = 1 := Fin.ext (by simpa using b)
    subst ei ej
    exact hcut
  · have ei : i = 1 := Fin.ext (by simpa using a)
    have ej : j = 0 := Fin.ext (by simpa using b)
    subst ei ej
    rw [hsymm]
    exact hcut

theorem not_three_poles (i j l : Fin 7) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hi : isP i) (hj : isP j) (hl : isP l) : False := by
  have h1 : i.val < 2 := hi
  have h2 : j.val < 2 := hj
  have h3 : l.val < 2 := hl
  have := Fin.val_ne_of_ne hij
  have := Fin.val_ne_of_ne hil
  have := Fin.val_ne_of_ne hjl
  omega

/-- The pointwise condition of `typed_bound_comb2` for the `n = 7` colouring, with the lower cut
`amin ≤ τ i j` on all pairs (`amin = -1` is no cut). -/
theorem hpt7 (SP SR : ℝ → ℝ → ℝ → ℝ)
    (hSP : ∀ a b c, SP a b c = SP b a c) (hSR : ∀ a b c, SR a b c = SR b a c)
    (HA HB HC ψBa ψCb : ℝ → ℝ) (e cal cbe alo ahi amin : ℝ)
    (τ : Fin 7 → Fin 7 → ℝ) (hsymm : ∀ i j, τ i j = τ j i)
    (hG : ∀ i j l, i ≠ j → i ≠ l → j ≠ l → GramOK (τ i j) (τ i l) (τ j l))
    (hmin : ∀ i j, i ≠ j → amin ≤ τ i j)
    (hcut : alo ≤ τ 0 1 ∧ τ 0 1 ≤ ahi)
    (hα : ∀ u v t, GramOK u v t → alo ≤ u → u ≤ ahi → amin ≤ v → amin ≤ t →
      0 ≤ lamA SP SR HA ψBa cal u v t)
    (hβ : ∀ u v t, GramOK u v t → amin ≤ u → amin ≤ v → amin ≤ t →
      0 ≤ lamB SP SR HB ψBa ψCb cbe u v t)
    (hγ : ∀ u v t, GramOK u v t → amin ≤ u → amin ≤ v → amin ≤ t →
      0 ≤ lamG SR HC ψCb ((e + 2 * SP 1 1 1 + 5 * SR 1 1 1 - 5 * cal - 20 * cbe) / 10) u v t) :
    ∀ i j l : Fin 7, i ≠ j → i ≠ l → j ≠ l →
      0 ≤ W7 SP SR HA HB HC ψBa ψCb i j l (τ i j) + W7 SP SR HA HB HC ψBa ψCb i l j (τ i l)
          + W7 SP SR HA HB HC ψBa ψCb j l i (τ j l) - c7 e (SP 1 1 1) (SR 1 1 1) cal cbe i j l
        - (s7 SP SR i (τ i j) (τ i l) (τ j l) + s7 SP SR i (τ i l) (τ i j) (τ l j)
          + s7 SP SR j (τ j i) (τ j l) (τ i l) + s7 SP SR j (τ j l) (τ j i) (τ l i)
          + s7 SP SR l (τ l i) (τ l j) (τ i j) + s7 SP SR l (τ l j) (τ l i) (τ j i)) := by
  intro i j l hij hil hjl
  have ha := hsymm j i
  have hb := hsymm l i
  have hc := hsymm l j
  have e1 := hSP (τ i j) (τ i l) (τ j l)
  have e2 := hSP (τ i j) (τ j l) (τ i l)
  have e3 := hSP (τ i l) (τ j l) (τ i j)
  have f1 := hSR (τ i j) (τ i l) (τ j l)
  have f2 := hSR (τ i j) (τ j l) (τ i l)
  have f3 := hSR (τ i l) (τ j l) (τ i j)
  by_cases hi : isP i <;> by_cases hj : isP j <;> by_cases hl : isP l
  · exact (not_three_poles i j l hij hil hjl hi hj hl).elim
  · -- poles `i, j`, ring `l`
    have h := hα (τ i j) (τ i l) (τ j l) (hG i j l hij hil hjl)
      (pole_pair alo ahi τ hsymm hcut i j hi hj hij).1 (pole_pair alo ahi τ hsymm hcut i j hi hj hij).2
      (hmin i l hil) (hmin j l hjl)
    simp only [lamA] at h
    simp only [W7, c7, s7, hi, hj, hl, ↓reduceIte, ha, hb, hc]
    linarith
  · -- poles `i, l`, ring `j`
    have h := hα (τ i l) (τ i j) (τ j l) (by
        have := hG i l j hil hij hjl.symm
        rwa [hsymm l j] at this)
      (pole_pair alo ahi τ hsymm hcut i l hi hl hil).1 (pole_pair alo ahi τ hsymm hcut i l hi hl hil).2
      (hmin i j hij) (hmin j l hjl)
    simp only [lamA] at h
    simp only [W7, c7, s7, hi, hj, hl, ↓reduceIte, ha, hb, hc]
    linarith
  · -- pole `i`, rings `j, l`
    have h := hβ (τ i j) (τ i l) (τ j l) (hG i j l hij hil hjl)
      (hmin i j hij) (hmin i l hil) (hmin j l hjl)
    simp only [lamB] at h
    simp only [W7, c7, s7, hi, hj, hl, ↓reduceIte, ha, hb, hc]
    linarith
  · -- poles `j, l`, ring `i`
    have h := hα (τ j l) (τ i j) (τ i l) (by
        have := hG j l i hjl hij.symm hil.symm
        rwa [hsymm j i, hsymm l i] at this)
      (pole_pair alo ahi τ hsymm hcut j l hj hl hjl).1 (pole_pair alo ahi τ hsymm hcut j l hj hl hjl).2
      (hmin i j hij) (hmin i l hil)
    simp only [lamA] at h
    simp only [W7, c7, s7, hi, hj, hl, ↓reduceIte, ha, hb, hc]
    linarith
  · -- pole `j`, rings `i, l`
    have h := hβ (τ i j) (τ j l) (τ i l) (by
        have := hG j i l hij.symm hjl hil
        rwa [hsymm j i] at this)
      (hmin i j hij) (hmin j l hjl) (hmin i l hil)
    simp only [lamB] at h
    simp only [W7, c7, s7, hi, hj, hl, ↓reduceIte, ha, hb, hc]
    linarith
  · -- pole `l`, rings `i, j`
    have h := hβ (τ i l) (τ j l) (τ i j) (by
        have := hG l i j hil.symm hjl.symm hij
        rwa [hsymm l i, hsymm l j] at this)
      (hmin i l hil) (hmin j l hjl) (hmin i j hij)
    simp only [lamB] at h
    simp only [W7, c7, s7, hi, hj, hl, ↓reduceIte, ha, hb, hc]
    linarith
  · -- three rings
    have h := hγ (τ i j) (τ i l) (τ j l) (hG i j l hij hil hjl)
      (hmin i j hij) (hmin i l hil) (hmin j l hjl)
    simp only [lamG] at h
    simp only [W7, c7, s7, hi, hj, hl, ↓reduceIte, ha, hb, hc]
    linarith

theorem Sk_swap (K : ℕ) (m : ℕ → ℕ) (F : (k : ℕ) → Matrix (Fin (m k)) (Fin (m k)) ℝ)
    (hF : ∀ k, k < K → (F k).PosSemidef) (a b c : ℝ) : Sk K m F a b c = Sk K m F b a c := by
  unfold Sk
  refine Finset.sum_congr rfl fun k hk => ?_
  exact matDot_Y3_swap (F k)
    (Matrix.isSymm_conjTranspose_iff.mp (congrArg Matrix.transpose (hF k (Finset.mem_range.mp hk)).isHermitian)) k a b c

theorem Sk_root_nonneg (K : ℕ) (m : ℕ → ℕ)
    (F : (k : ℕ) → Matrix (Fin (m k)) (Fin (m k)) ℝ) (hF : ∀ k, k < K → (F k).PosSemidef)
    {n : ℕ} (x : Fin n → R3) (hx : ∀ i, ‖x i‖ = 1) (i : Fin n) :
    0 ≤ ∑ j, ∑ l, Sk K m F ⟪x i, x j⟫ ⟪x i, x l⟫ ⟪x j, x l⟫ := by
  unfold Sk
  have hswap : ∀ (g : Fin n → Fin n → ℕ → ℝ),
      ∑ j, ∑ l, ∑ k ∈ Finset.range K, g j l k = ∑ k ∈ Finset.range K, ∑ j, ∑ l, g j l k := by
    intro g
    calc ∑ j, ∑ l, ∑ k ∈ Finset.range K, g j l k
        = ∑ j, ∑ k ∈ Finset.range K, ∑ l, g j l k :=
          Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _ = ∑ k ∈ Finset.range K, ∑ j, ∑ l, g j l k := Finset.sum_comm
  rw [hswap]
  exact Finset.sum_nonneg fun k hk =>
    matDot_root_nonneg (m k) k x hx i (F k) (hF k (Finset.mem_range.mp hk))

/-- **Typed three-point bound for `n = 7`, with a lower cut** (two poles `0, 1`, five ring points
`2..6`; all pair values `≥ amin`).

If the three type slacks `lamA` (pole-pole-ring, on a cut `alo ≤ t ≤ ahi` of the pole-pole
value), `lamB` (pole-ring-ring) and `lamG` (ring-ring-ring) are nonnegative on the Gram region
intersected with `≥ amin`, then `e ≤ H_A(t_01) + Σ_{pole,ring} H_B + Σ_{ring,ring} H_C`. -/
theorem typed7_bound_lo (K : ℕ) (m : ℕ → ℕ)
    (FP FR : (k : ℕ) → Matrix (Fin (m k)) (Fin (m k)) ℝ)
    (hFP : ∀ k, k < K → (FP k).PosSemidef) (hFR : ∀ k, k < K → (FR k).PosSemidef)
    (HA HB HC ψBa ψCb : ℝ → ℝ) (e cal cbe alo ahi amin : ℝ)
    (x : Fin 7 → R3) (hx : ∀ i, ‖x i‖ = 1)
    (hmin : ∀ i j, i ≠ j → amin ≤ ⟪x i, x j⟫)
    (hcut : alo ≤ ⟪x 0, x 1⟫ ∧ ⟪x 0, x 1⟫ ≤ ahi)
    (hα : ∀ u v t, GramOK u v t → alo ≤ u → u ≤ ahi → amin ≤ v → amin ≤ t →
      0 ≤ lamA (Sk K m FP) (Sk K m FR) HA ψBa cal u v t)
    (hβ : ∀ u v t, GramOK u v t → amin ≤ u → amin ≤ v → amin ≤ t →
      0 ≤ lamB (Sk K m FP) (Sk K m FR) HB ψBa ψCb cbe u v t)
    (hγ : ∀ u v t, GramOK u v t → amin ≤ u → amin ≤ v → amin ≤ t →
      0 ≤ lamG (Sk K m FR) HC ψCb
        ((e + 2 * Sk K m FP 1 1 1 + 5 * Sk K m FR 1 1 1 - 5 * cal - 20 * cbe) / 10) u v t) :
    e ≤ ∑ i, ∑ j ∈ Finset.Ioi i, H7 HA HB HC i j ⟪x i, x j⟫ := by
  refine typed_bound_comb2 (n := 7) (by norm_num) (s7 (Sk K m FP) (Sk K m FR))
    (H7 HA HB HC) ?_ e (fun i j => ⟪x i, x j⟫) (fun i j => real_inner_comm _ _)
    (fun i => by rw [real_inner_self_eq_norm_sq, hx i]; norm_num)
    (W7 (Sk K m FP) (Sk K m FR) HA HB HC ψBa ψCb)
    (c7 e (Sk K m FP 1 1 1) (Sk K m FR 1 1 1) cal cbe)
    (hW7 (Sk K m FP) (Sk K m FR) HA HB HC ψBa ψCb) (hc7 (Sk K m FP) (Sk K m FR) e cal cbe) ?_ ?_
  · intro i j t
    by_cases hi : isP i <;> by_cases hj : isP j <;> simp [H7, hi, hj]
  · refine Finset.sum_nonneg fun i _ => ?_
    by_cases hi : isP i
    · simp only [s7, hi, ↓reduceIte]
      exact Sk_root_nonneg K m FP hFP x hx i
    · simp only [s7, hi, ↓reduceIte]
      exact Sk_root_nonneg K m FR hFR x hx i
  · exact hpt7 (Sk K m FP) (Sk K m FR) (Sk_swap K m FP hFP) (Sk_swap K m FR hFR)
      HA HB HC ψBa ψCb e cal cbe alo ahi amin (fun i j => ⟪x i, x j⟫)
      (fun i j => real_inner_comm _ _)
      (fun i j l _ _ _ => gramOK_inner (x i) (x j) (x l) (hx i) (hx j) (hx l)) hmin hcut hα hβ hγ

end Typed7

end ThreePoint
end ThomsonN7

end Asm_Typed7

section Asm_T4
namespace ThomsonN7
namespace M6

/-! ### Integer interval arithmetic (exact, no rounding) -/

/-! ### Homogeneous Gram determinants and their interval enclosures -/

/-! ### Boxes, bisection and the two refutation checkers -/

end M6
end ThomsonN7

open scoped InnerProductSpace

namespace ThomsonN7
namespace T4

open M6

/-! ### Combinatorics of the ring: a 2-colouring of `K₅` without monochromatic triangle is a pentagon -/

/-! ### The ring colouring of a configuration -/

/-! ### The relabelling of the bipyramid -/

/-! ### Nominal Gram entries of the relabelled bipyramid -/

/-! ### Ring rigidity -/

end T4
end ThomsonN7

end Asm_T4

section Asm_Glue1
/-!
# Glue for the near-antipodal case (Case 2)

Abstract, numerics-independent assembly:

* `Glue.exists_minpair_perm`: every 7-configuration is a relabelling of one whose pair `(0,1)` has the
  smallest inner product;
* `Glue.RootedClaim`, `Glue.case2_of_rooted`, `Glue.seven_of_rooted`: the rooted claim implies both
  Challenge statements (through `Case1.seven_of_case2`);
* `Glue.rooted_of_cap_slabs`: a cap certificate plus finitely many slab certificates give the rooted
  claim;
* `Glue.slab_of_typed`, `Glue.cap_of_typed`: a typed pair-minorant bound gives the slab / cap claims
  (with the equality analysis through `M3.contact_rigidity`).
-/

namespace ThomsonN7
namespace Glue

section Rooted

open scoped InnerProductSpace
open Base

end Rooted

section Typed

open scoped InnerProductSpace
open Base

end Typed

end Glue
end ThomsonN7

end Asm_Glue1

section Asm_Glue2
/-!
# Glue for the near-sharp (tube) cap certificate, route S2

A typed pair-minorant bound `e <= sum_{i<j} H_cls(<y_i, y_j>)` which is only *near*-sharp
(`E(P) <= e + delta`) still gives the cap claim, provided

* the pair slacks `phi - H_cls` control the distance to the nodes (`slack <= delta` puts the inner
  product within `tau` of a node of its class);
* the tube rigidity `TubeRigid tau` (closeness of all 21 inner products to the class nodes gives a
  relabelling of the pentagonal bipyramid within `tau` in every Gram entry);
* the local statement `LocalGramA` holds on the window `tau` (Regime B).

The proof is: `E(y) <= E(P)` implies `sum of slacks <= delta`, hence every slack `<= delta`, hence the
tube, hence the window, hence the local statement.
-/

namespace ThomsonN7
namespace Glue

section Tube

open scoped InnerProductSpace
open Base

end Tube

end Glue
end ThomsonN7

end Asm_Glue2

section Asm_Glue2b
namespace ThomsonN7
namespace Glue
section TubeFromT4
open scoped RealInnerProductSpace

end TubeFromT4
end Glue
end ThomsonN7

end Asm_Glue2b

section Asm_Glue3
/-!
# Glue3: the typed three-point bound (`Typed7`) feeds the cap / slab glue (`Glue1`, `Glue2`)

`ThreePoint.typed7_bound` bounds `e` by the typed double sum `∑ i<j, H7 HA HB HC i j ⟪x i, x j⟫`.
Here we identify `H7` with the class selector `Glue.cls3` (poles are the indices `0, 1`) and
restate the bound in exactly the shape needed by `Glue.cap_of_typed`, `Glue.cap_of_typed_tube`
and `Glue.slab_of_typed`.
-/

namespace ThomsonN7
namespace Glue

section Bridge

open scoped InnerProductSpace
open Base

/-- The typed selector `H7` of `Typed7` is the class selector `cls3` of `Glue1`. -/
lemma H7_eq_cls3 (HA HB HC : ℝ → ℝ) (i j : Fin 7) (t : ℝ) :
    ThreePoint.H7 HA HB HC i j t = cls3 HA HB HC i j t := by
  have h1 : ThreePoint.isP i ↔ i.val ≤ 1 := by unfold ThreePoint.isP; omega
  have h2 : ThreePoint.isP j ↔ j.val ≤ 1 := by unfold ThreePoint.isP; omega
  unfold ThreePoint.H7 cls3
  by_cases hi : i.val ≤ 1 <;> by_cases hj : j.val ≤ 1 <;> simp [h1, h2, hi, hj]

/-- The double sums of `H7` and `cls3` agree. -/
lemma sum_H7_eq_sum_cls3 (HA HB HC : ℝ → ℝ) (g : Fin 7 → Fin 7 → ℝ) :
    ∑ i : Fin 7, ∑ j ∈ Finset.Ioi i, ThreePoint.H7 HA HB HC i j (g i j) =
      ∑ i : Fin 7, ∑ j ∈ Finset.Ioi i, cls3 HA HB HC i j (g i j) := by
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact H7_eq_cls3 HA HB HC i j _

end Bridge

section Assembly

open scoped InnerProductSpace
open Base

end Assembly

end Glue
end ThomsonN7

end Asm_Glue3

section Asm_Glue4
/-!
# Glue4: the final interface (`CapSpec`, `SlabSpec`) and the assembly `seven_of_specs`

The near-sharp cap and the margin slabs are certified by *typed* three-point data
(`Typed7`): PSD blocks `FP FR`, class minorants `HA HB HC`, multipliers `ψBa ψCb`, constants
`cal cbe`, together with one-dimensional facts on the minorants.  `CapSpec a0` (resp.
`SlabSpec lo hi`) is the proposition "such data exist"; every certificate producer has to prove
one of these propositions and nothing else.  `seven_of_specs` is the assembly: a cap spec at
`a 0` and slab specs on `[a k, a (k+1)]` for `k < K`, with `a K ≥ -9/10`, give both Challenge
statements for `N = 7`.

The tube-rigidity hypothesis of the near-sharp cap and the local (Regime B) statement are
discharged here once and for all (`Glue.tubeRigid_of_le`, `Glue.localGramA_of_le`).
-/

namespace ThomsonN7
namespace Glue

section Final

open scoped InnerProductSpace
open Base

end Final

end Glue
end ThomsonN7

end Asm_Glue4

section Asm_EPEnc
/-!  agent9: 40-digit enclosure of the minimal energy `E(P)` (for the near-sharp cap route).  -/

namespace ThomsonN7
namespace Glue
section EPEnc
open Real

lemma sqrt2_enc60 : (1414213562373095048801688724209698078569671875376948073176679/1000000000000000000000000000000000000000000000000000000000000:ℝ) ≤ √2 ∧ √2 ≤ (35355339059327376220042218105242451964241796884423701829417/25000000000000000000000000000000000000000000000000000000000:ℝ) := by
  constructor
  · exact (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
  · exact Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩

lemma sqrt5_enc60 : (2236067977499789696409173668731276235440618359611525724270897/1000000000000000000000000000000000000000000000000000000000000:ℝ) ≤ √5 ∧ √5 ≤ (1118033988749894848204586834365638117720309179805762862135449/500000000000000000000000000000000000000000000000000000000000:ℝ) := by
  constructor
  · exact (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
  · exact Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩

lemma sin_pi_div_five_enc60 : (36736578268279570573044122164942048037353277352696624442017/62500000000000000000000000000000000000000000000000000000000:ℝ) ≤ sin (π / 5) ∧ sin (π / 5) ≤ (587785252292473129168705954639072768597652437643145991072273/1000000000000000000000000000000000000000000000000000000000000:ℝ) := by
  have hpos : 0 < sin (π / 5) := sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [pi_pos])
  have hsq := EPBounds.sin_pi_div_five_sq
  obtain ⟨h5l, h5u⟩ := sqrt5_enc60
  constructor
  · refine le_of_sq_le_sq ?_ hpos.le
    have h : ((36736578268279570573044122164942048037353277352696624442017/62500000000000000000000000000000000000000000000000000000000:ℝ))^2 ≤ (5 - (1118033988749894848204586834365638117720309179805762862135449/500000000000000000000000000000000000000000000000000000000000:ℝ)) / 8 := by norm_num
    rw [hsq]; linarith
  · refine le_of_sq_le_sq ?_ (by norm_num)
    have h : (5 - (2236067977499789696409173668731276235440618359611525724270897/1000000000000000000000000000000000000000000000000000000000000:ℝ)) / 8 ≤ ((587785252292473129168705954639072768597652437643145991072273/1000000000000000000000000000000000000000000000000000000000000:ℝ))^2 := by norm_num
    rw [hsq]; linarith

lemma pent_formula_enc60 :
    (2749119669932377435234055288292254784954290675400566755703294260891298019502848863829080584715823163195763171851924111216693219925026887457700757192016552400988256247789361356038783/190211303259030714423287866675876428681139726825150044489461341270161735474419585794589163301350513554082924534014861115400000000000000000000000000000000000000000000000000000000000:ℝ) ≤ 1 / 2 + 5 * √2 + 5 / (2 * sin (π / 5)) + 5 / (2 * sin (2 * π / 5)) ∧
    1 / 2 + 5 * √2 + 5 / (2 * sin (π / 5)) + 5 / (2 * sin (2 * π / 5)) ≤ (8590998968538679485106422775913296202982158360626771111572787709008136802664564722236982378865706250355829161488401108250568180672808974029458937792907486302049850635875288467833/594410322684470982572774583362113839628561646328593889029565496515121113275428212520708832082656592896884997083885396245000000000000000000000000000000000000000000000000000000000:ℝ) := by
  obtain ⟨h2l, h2u⟩ := sqrt2_enc60
  obtain ⟨h5l, h5u⟩ := sqrt5_enc60
  obtain ⟨hal, hau⟩ := sin_pi_div_five_enc60
  have hpos : 0 < sin (π / 5) := by linarith [show (0:ℝ) < (36736578268279570573044122164942048037353277352696624442017/62500000000000000000000000000000000000000000000000000000000:ℝ) by norm_num]
  rw [EPBounds.sin_two_pi_div_five]
  have hs5 : 0 < √5 := Real.sqrt_pos.2 (by norm_num)
  have h1 : 5 / (2 * sin (π / 5)) ≤ 5 / (2 * (36736578268279570573044122164942048037353277352696624442017/62500000000000000000000000000000000000000000000000000000000:ℝ)) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have h1' : 5 / (2 * (587785252292473129168705954639072768597652437643145991072273/1000000000000000000000000000000000000000000000000000000000000:ℝ)) ≤ 5 / (2 * sin (π / 5)) :=
    div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  have hb : 0 < sin (π / 5) * ((1 + √5) / 2) := by positivity
  have hbl : (36736578268279570573044122164942048037353277352696624442017/62500000000000000000000000000000000000000000000000000000000:ℝ) * ((1 + (2236067977499789696409173668731276235440618359611525724270897/1000000000000000000000000000000000000000000000000000000000000:ℝ)) / 2) ≤ sin (π / 5) * ((1 + √5) / 2) :=
    mul_le_mul hal (by linarith) (by norm_num) (by linarith)
  have hbu : sin (π / 5) * ((1 + √5) / 2) ≤ (587785252292473129168705954639072768597652437643145991072273/1000000000000000000000000000000000000000000000000000000000000:ℝ) * ((1 + (1118033988749894848204586834365638117720309179805762862135449/500000000000000000000000000000000000000000000000000000000000:ℝ)) / 2) :=
    mul_le_mul hau (by linarith) (by linarith) (by norm_num)
  have h2 : 5 / (2 * (sin (π / 5) * ((1 + √5) / 2))) ≤
      5 / (2 * ((36736578268279570573044122164942048037353277352696624442017/62500000000000000000000000000000000000000000000000000000000:ℝ) * ((1 + (2236067977499789696409173668731276235440618359611525724270897/1000000000000000000000000000000000000000000000000000000000000:ℝ)) / 2))) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  have h2' : 5 / (2 * ((587785252292473129168705954639072768597652437643145991072273/1000000000000000000000000000000000000000000000000000000000000:ℝ) * ((1 + (1118033988749894848204586834365638117720309179805762862135449/500000000000000000000000000000000000000000000000000000000000:ℝ)) / 2))) ≤
      5 / (2 * (sin (π / 5) * ((1 + √5) / 2))) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  constructor
  · norm_num at h1' h2' ⊢; linarith
  · norm_num at h1 h2 ⊢; linarith

/-- **40-digit enclosure of the minimum energy**:
`144529774142213429350444915306029287904778/10^40 ≤ E(P) ≤ 144529774142213429350444915306029287904779/10^40`. -/
lemma coulombEnergy_pent_enc40 :
    (144529774142213429350444915306029287904778:ℝ) / 10^40 ≤ coulombEnergy pentBipyramid ∧
    coulombEnergy pentBipyramid ≤ (144529774142213429350444915306029287904779:ℝ) / 10^40 := by
  rw [pentBipyramid_energy]
  obtain ⟨hl, hu⟩ := pent_formula_enc60
  constructor
  · refine le_trans ?_ hl; norm_num
  · refine le_trans hu ?_; norm_num

/-- Upper enclosure in the form used by the near-sharp cap (`hEδ`). -/
lemma coulombEnergy_pent_le_of {e δ : ℝ} (h : (144529774142213429350444915306029287904779:ℝ) / 10^40 ≤ e + δ) :
    coulombEnergy pentBipyramid ≤ e + δ :=
  le_trans coulombEnergy_pent_enc40.2 h

end EPEnc
end Glue
end ThomsonN7

end Asm_EPEnc

section Asm_Coerce
/-!
# One-dimensional facts for the typed cap / slab certificates (CoerceCert)

The typed three-point bound uses class minorants `H_cls ≤ phi` of the pair potential
`phi t = (√(2 - 2t))⁻¹`.  For a polynomial `H = Q / Dq` write `y = √(2 - 2t) / 2 ∈ (0, 1]`, so
`t = 1 - 2 y²`, `phi = 1 / (2 y)` and

  `phi t - H t = F(y) / (2 y Dq)`,   `F(y) = Dq - 2 y Q(1 - 2 y²)`,

a *polynomial* in `y` (no square roots, no sign case split).  Hence

* `H ≤ phi` on a `y`-interval is the polynomial inequality `F ≥ 0` (`PlainCert`);
* exact double contact at a rational node `y = p / q` is the factorisation `F = (q y - p)² G`
  (`Contact1`; two nodes: `Contact2`; simple contact at the boundary `y = 1`: `ContactA`), and
  `G ≥ g0 > 0` gives *coercivity*: `phi - H ≤ δ` forces `y` (hence `t`) close to the node.

Positivity of a polynomial on a rational `y`-interval is certified by exact Bernstein pieces
(`BPiece`), checked by list arithmetic in the kernel (no SDP data, no rounding).
-/

namespace ThomsonN7
namespace Glue
namespace Coerce

open CutOneD Base

/-! ## A. Polynomial helpers and Bernstein pieces -/

theorem peval_ppow (p : List ℤ) (n : ℕ) (y : ℝ) : peval (ppow p n) y = peval p y ^ n := by
  induction n with
  | zero => simp [ppow, peval]
  | succ n ih => simp only [ppow, peval_pmul, ih, pow_succ]; ring

theorem bernSum_nonneg (a b : List ℤ) (n : ℕ) (y : ℝ) (ha : 0 ≤ peval a y) (hb : 0 ≤ peval b y)
    (bs : List ℕ) : ∀ i : ℕ, 0 ≤ peval (bernSum a b n i bs) y := by
  induction bs with
  | nil => intro i; simp [bernSum, peval]
  | cons β bs ih =>
    intro i
    simp only [bernSum, peval_padd, peval_pscale, peval_pmul, peval_ppow]
    exact add_nonneg (mul_nonneg (by positivity) (mul_nonneg (pow_nonneg ha _) (pow_nonneg hb _)))
      (ih (i + 1))

theorem BPiece.nonneg (P : List ℤ) (c : BPiece) (hc : c.check P = true) {y : ℝ}
    (h0 : (c.u1 : ℝ) ≤ c.u2 * y) (h1 : (c.w2 : ℝ) * y ≤ c.w1) : 0 ≤ peval P y := by
  simp only [BPiece.check, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨hL, -⟩, -⟩, hz⟩ := hc
  have h := peval_eq_zero_of_all _ hz y
  simp only [BPiece.diff, peval_padd, peval_pscale, peval_pneg] at h
  have ha : 0 ≤ peval [-c.u1, (c.u2 : ℤ)] y := by
    simp only [peval]; push_cast; linarith
  have hb : 0 ≤ peval [c.w1, -(c.w2 : ℤ)] y := by
    simp only [peval]; push_cast; linarith
  have hs := bernSum_nonneg _ _ (c.β.length - 1) y ha hb c.β 0
  have hLam : (0 : ℝ) < c.Lam := by exact_mod_cast hL
  have h2 : 0 ≤ (c.Lam : ℝ) * peval P y := by push_cast at h; linarith
  exact nonneg_of_mul_nonneg_right h2 hLam

theorem chainOK_nonneg (P : List ℤ) (cs : List BPiece) :
    ∀ (l1 : ℤ) (l2 : ℕ) (r1 : ℤ) (r2 : ℕ), 0 < l2 → 0 < r2 → chainOK P cs l1 l2 r1 r2 = true →
      ∀ y : ℝ, (l1 : ℝ) ≤ l2 * y → (r2 : ℝ) * y ≤ r1 → 0 ≤ peval P y := by
  induction cs with
  | nil => intro l1 l2 r1 r2 _ _ h; simp [chainOK] at h
  | cons c cs ih =>
    intro l1 l2 r1 r2 hl hr h y hy0 hy1
    simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h
    obtain ⟨⟨hc, hleft⟩, hright⟩ := h
    have hu2 : 0 < c.u2 := by
      simp only [BPiece.check, Bool.and_eq_true, decide_eq_true_eq] at hc; exact hc.1.1.2
    have hw2 : 0 < c.w2 := by
      simp only [BPiece.check, Bool.and_eq_true, decide_eq_true_eq] at hc; exact hc.1.2
    have hlR : (0 : ℝ) < l2 := by exact_mod_cast hl
    have hrR : (0 : ℝ) < r2 := by exact_mod_cast hr
    have hu2R : (0 : ℝ) < c.u2 := by exact_mod_cast hu2
    have hw2R : (0 : ℝ) < c.w2 := by exact_mod_cast hw2
    -- left endpoint of the piece is below `y`
    have hleftR : (c.u1 : ℝ) * l2 ≤ l1 * c.u2 := by exact_mod_cast hleft
    have hpl : (c.u1 : ℝ) ≤ c.u2 * y := by
      have : (c.u1 : ℝ) * l2 ≤ c.u2 * (l2 * y) := by nlinarith
      nlinarith
    by_cases hyc : (c.w2 : ℝ) * y ≤ c.w1
    · exact c.nonneg P hc hpl hyc
    · rcases hright with hr1 | hr2
      · exfalso
        have hr1R : (r1 : ℝ) * c.w2 ≤ c.w1 * r2 := by exact_mod_cast hr1
        apply hyc
        have : (r2 : ℝ) * (c.w2 * y) ≤ r2 * c.w1 := by nlinarith
        nlinarith
      · refine ih c.w1 c.w2 r1 r2 hw2 hr hr2 y ?_ hy1
        exact le_of_lt (not_le.1 hyc)

/-! ## B. The substitution `y = √(2 - 2t) / 2` -/

theorem yOf_pos {t : ℝ} (h : t < 1) : 0 < yOf t := by
  unfold yOf
  have : 0 < 2 - 2 * t := by linarith
  positivity

theorem yOf_sq {t : ℝ} (h : t ≤ 1) : yOf t ^ 2 = (1 - t) / 2 := by
  unfold yOf
  rw [div_pow, Real.sq_sqrt (by linarith)]
  ring

theorem one_sub_two_yOf_sq {t : ℝ} (h : t ≤ 1) : 1 - 2 * yOf t ^ 2 = t := by
  rw [yOf_sq h]; ring

theorem yOf_le_one {t : ℝ} (h1 : -1 ≤ t) (h2 : t < 1) : yOf t ≤ 1 := by
  have hy := yOf_pos h2
  have := yOf_sq h2.le
  nlinarith

/-- `y ≥ yh` as soon as `t ≤ 1 - 2 yh²`. -/
theorem le_yOf_of_hi {t yh : ℝ} (h2 : t < 1) (hyh : 0 ≤ yh) (h : t ≤ 1 - 2 * yh ^ 2) :
    yh ≤ yOf t := by
  have hy := yOf_pos h2
  have := yOf_sq h2.le
  nlinarith

theorem phi_eq_yOf (t : ℝ) : phi t = 1 / (2 * yOf t) := by
  unfold phi yOf
  have : 2 * (√(2 - 2 * t) / 2) = √(2 - 2 * t) := by ring
  rw [this, one_div]

theorem peval_Fpoly (Q : List ℤ) (Dq : ℕ) (y : ℝ) :
    peval (Fpoly Q Dq) y = Dq - 2 * y * peval Q (1 - 2 * y ^ 2) := by
  simp only [Fpoly, peval_padd, peval_pneg, peval_pmul, peval_compQ, peval]
  push_cast
  ring

/-- **The slack as a polynomial quotient**: `phi t - Q(t)/Dq = F(y) / (2 y Dq)`. -/
theorem phi_sub_H {Q : List ℤ} {Dq : ℕ} (hD : 0 < Dq) {t : ℝ} (h : t < 1) :
    phi t - peval Q t / Dq = peval (Fpoly Q Dq) (yOf t) / (2 * yOf t * Dq) := by
  have hy := yOf_pos h
  have hD' : (0 : ℝ) < Dq := by exact_mod_cast hD
  rw [peval_Fpoly, one_sub_two_yOf_sq h.le, phi_eq_yOf t]
  field_simp

/-- If `F ≥ 0` at `y = yOf t` then `H t ≤ phi t`. -/
theorem H_le_phi_of_F {Q : List ℤ} {Dq : ℕ} (hD : 0 < Dq) {t : ℝ} (h : t < 1)
    (hF : 0 ≤ peval (Fpoly Q Dq) (yOf t)) : peval Q t / Dq ≤ phi t := by
  have hy := yOf_pos h
  have hD' : (0 : ℝ) < Dq := by exact_mod_cast hD
  have := phi_sub_H hD h (Q := Q)
  have h0 : 0 ≤ phi t - peval Q t / Dq := by rw [this]; positivity
  linarith

/-- The slack bound: `phi t - Q(t)/Dq ≤ δ` gives `F(y) ≤ 2 Dq δ` when `y ≤ 1` and `F ≥ 0`. -/
theorem F_le_of_slack {Q : List ℤ} {Dq : ℕ} (hD : 0 < Dq) {t δ : ℝ} (h : t < 1)
    (hy1 : yOf t ≤ 1) (hF : 0 ≤ peval (Fpoly Q Dq) (yOf t))
    (hs : phi t - peval Q t / Dq ≤ δ) : peval (Fpoly Q Dq) (yOf t) ≤ 2 * Dq * δ := by
  have hy := yOf_pos h
  have hD' : (0 : ℝ) < Dq := by exact_mod_cast hD
  rw [phi_sub_H hD h, div_le_iff₀ (by positivity)] at hs
  have hδ : 0 ≤ δ := by
    have h0 : 0 ≤ peval (Fpoly Q Dq) (yOf t) / (2 * yOf t * Dq) := by positivity
    have := phi_sub_H hD h (Q := Q)
    have h1 : peval (Fpoly Q Dq) (yOf t) / (2 * yOf t * Dq) ≤ δ := by
      rw [div_le_iff₀ (by positivity)]; exact hs
    linarith
  nlinarith [mul_nonneg hD'.le hδ, mul_nonneg (mul_nonneg hD'.le hδ) hy.le]

/-! ## C. Plain certificates: `H ≤ phi` on a `y`-interval -/

/-! ## D. Contact certificates with coercivity -/

/-- From `|y - y_ν| ≤ η` to the `t`-distance of `t = 1 - 2y²` from the node `1 - 2 y_ν²`. -/
theorem abs_t_sub_node_le {y yn η : ℝ} (hy : 0 < y) (hyn : 0 ≤ yn) (h : |y - yn| ≤ η) :
    |(1 - 2 * y ^ 2) - (1 - 2 * yn ^ 2)| ≤ 2 * η * (2 * yn + η) := by
  obtain ⟨h1, h2⟩ := abs_le.1 h
  have hη : 0 ≤ η := le_trans (abs_nonneg _) h
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg hη hy.le, mul_nonneg hη hyn]

/-- The distance bound for `t` from the distance bound for `y`. -/
theorem abs_t_sub_le {y yn η ν τ : ℝ} (hy : 0 < y) (hyn : 0 ≤ yn) (h : |y - yn| ≤ η)
    (hτ : |1 - 2 * yn ^ 2 - ν| + 2 * η * (2 * yn + η) ≤ τ) : |(1 - 2 * y ^ 2) - ν| ≤ τ := by
  have h1 := abs_t_sub_node_le hy hyn h
  have h2 : |(1 - 2 * y ^ 2) - ν| ≤ |(1 - 2 * y ^ 2) - (1 - 2 * yn ^ 2)| + |1 - 2 * yn ^ 2 - ν| := by
    have := abs_add_le ((1 - 2 * y ^ 2) - (1 - 2 * yn ^ 2)) (1 - 2 * yn ^ 2 - ν)
    have e : (1 - 2 * y ^ 2) - (1 - 2 * yn ^ 2) + (1 - 2 * yn ^ 2 - ν) = (1 - 2 * y ^ 2) - ν := by
      ring
    rwa [e] at this
  linarith

theorem peval_lin (p q : ℕ) (y : ℝ) : peval (lin p q) y = q * y - p := by
  simp only [lin, peval]; push_cast; ring

/-- Two nodes: if `|(y - y1)(y - y2)| ≤ η |y1 - y2| / 2` then `y` is within `η` of a node. -/
theorem two_node_alt {y y1 y2 η : ℝ} (hη : 0 ≤ η)
    (h : |(y - y1) * (y - y2)| ≤ η * |y1 - y2| / 2) : |y - y1| ≤ η ∨ |y - y2| ≤ η := by
  by_contra hcon
  push Not at hcon
  obtain ⟨ha, hb⟩ := hcon
  have hab : |y1 - y2| ≤ |y - y1| + |y - y2| := by
    have := abs_sub_le y1 y y2
    rwa [abs_sub_comm y1 y] at this
  rw [abs_mul] at h
  have ha0 : 0 < |y - y1| := lt_of_le_of_lt hη ha
  have hb0 : 0 < |y - y2| := lt_of_le_of_lt hη hb
  rcases le_total |y - y1| |y - y2| with hle | hle
  · nlinarith [mul_lt_mul_of_pos_right ha hb0]
  · nlinarith [mul_lt_mul_of_pos_left hb ha0]

theorem ContactA.factor (c : ContactA) (hc : c.check = true) (y : ℝ) :
    peval (Fpoly c.Q c.Dq) y = (1 - y) * peval c.G y := by
  simp only [ContactA.check, Bool.and_eq_true, decide_eq_true_eq] at hc
  have h := peval_eq_zero_of_all _ hc.1.2 y
  simp only [peval_padd, peval_pneg, peval_pmul, peval] at h
  push_cast at h
  linarith [h]

theorem ContactA.G_ge (c : ContactA) (hc : c.check = true) {y : ℝ}
    (h0 : (c.ya1 : ℝ) ≤ c.ya2 * y) (h1 : y ≤ 1) : (c.g0n : ℝ) / c.g0d ≤ peval c.G y := by
  simp only [ContactA.check, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨-, -⟩, hg0d⟩, hya⟩, -⟩, hch⟩ := hc
  have := chainOK_nonneg _ c.pieces c.ya1 c.ya2 1 1 hya one_pos hch y h0 (by simpa using h1)
  simp only [peval_padd, peval_pscale, peval_pneg, peval] at this
  have hd : (0 : ℝ) < c.g0d := by exact_mod_cast hg0d
  rw [div_le_iff₀ hd]
  push_cast at this
  linarith

/-- **Coercivity at the boundary node `t = -1`.**  For `t ≤ a0` (with `ya² ≤ (1 - a0)/2`,
`ya = ya1/ya2 ≥ 0`): `H ≤ phi`, and a slack `≤ δ` with `8 Dq δ ≤ g0 τ` forces `t + 1 ≤ τ`. -/
theorem ContactA.tube (c : ContactA) (hc : c.check = true) {δ τ a0 : ℝ}
    (hya : 0 ≤ (c.ya1 : ℝ) / c.ya2) (ha0 : ((c.ya1 : ℝ) / c.ya2) ^ 2 ≤ (1 - a0) / 2)
    (ha1 : a0 < 1) (hδ : 8 * c.Dq * δ ≤ ((c.g0n : ℝ) / c.g0d) * τ)
    {t : ℝ} (h1 : -1 ≤ t) (h2 : t ≤ a0) :
    peval c.Q t / c.Dq ≤ phi t ∧ (phi t - peval c.Q t / c.Dq ≤ δ → |t + 1| ≤ τ) := by
  have hc' := hc
  simp only [ContactA.check, Bool.and_eq_true, decide_eq_true_eq] at hc'
  obtain ⟨⟨⟨⟨⟨hD, hg0n⟩, hg0d⟩, hya2⟩, -⟩, -⟩ := hc'
  have h2' : t < 1 := lt_of_le_of_lt h2 ha1
  have hy := yOf_pos h2'
  have hy1 := yOf_le_one h1 h2'
  have hya2R : (0 : ℝ) < c.ya2 := by exact_mod_cast hya2
  have hyl : (c.ya1 : ℝ) / c.ya2 ≤ yOf t :=
    le_yOf_of_hi h2' hya (by linarith)
  have hyl' : (c.ya1 : ℝ) ≤ c.ya2 * yOf t := by
    rw [div_le_iff₀ hya2R] at hyl; linarith
  have hG := c.G_ge hc hyl' hy1
  have hg0 : (0 : ℝ) < (c.g0n : ℝ) / c.g0d := by positivity
  have hF : 0 ≤ peval (Fpoly c.Q c.Dq) (yOf t) := by
    rw [c.factor hc]; exact mul_nonneg (by linarith) (hg0.le.trans hG)
  refine ⟨H_le_phi_of_F hD h2' hF, fun hs => ?_⟩
  have hFle := F_le_of_slack hD h2' hy1 hF hs
  rw [c.factor hc] at hFle
  have h3 : ((c.g0n : ℝ) / c.g0d) * (1 - yOf t) ≤ 2 * c.Dq * δ :=
    le_trans (by nlinarith [sub_nonneg.2 hy1]) hFle
  have hsq := yOf_sq h2'.le
  have h4 : 4 * (1 - yOf t) ≤ τ := by
    refine le_of_mul_le_mul_left (a := (c.g0n : ℝ) / c.g0d) ?_ hg0
    nlinarith [h3, hδ]
  rw [abs_of_nonneg (by linarith)]
  nlinarith [sq_nonneg (yOf t - 1)]

/-! ## E. Shapes of the hypotheses `hA hB hC` of `cap_of_typed_tube7` and closeness of the nodes -/

/-- `hA` (pole--pole class, node `-1`) from a boundary-node certificate. -/
theorem ContactA.hA (c : ContactA) (hc : c.check = true) {δ τ a0 : ℝ}
    (hya : 0 ≤ (c.ya1 : ℝ) / c.ya2) (ha0 : ((c.ya1 : ℝ) / c.ya2) ^ 2 ≤ (1 - a0) / 2)
    (ha1 : a0 < 1) (hδ : 8 * c.Dq * δ ≤ ((c.g0n : ℝ) / c.g0d) * τ) :
    ∀ t, -1 ≤ t → t ≤ a0 →
      peval c.Q t / c.Dq ≤ phi t ∧ (phi t - peval c.Q t / c.Dq ≤ δ → |t + 1| ≤ τ) :=
  fun _ h1 h2 => c.tube hc hya ha0 ha1 hδ h1 h2

/-- The rational node `tn` is within `ε` of `c1 = (√5 - 1)/4` given rational bounds on `√5`. -/
theorem abs_node_sub_c1_le {tn ε lo hi : ℝ} (hlo : lo ≤ √5) (hhi : √5 ≤ hi)
    (h1 : 4 * tn + 1 - 4 * ε ≤ lo) (h2 : hi ≤ 4 * tn + 1 + 4 * ε) : |tn - c1| ≤ ε := by
  unfold c1
  rw [abs_le]
  constructor <;> linarith

/-- The rational node `tn` is within `ε` of `c2 = -(1 + √5)/4` given rational bounds on `√5`. -/
theorem abs_node_sub_c2_le {tn ε lo hi : ℝ} (hlo : lo ≤ √5) (hhi : √5 ≤ hi)
    (h1 : -4 * tn - 1 - 4 * ε ≤ lo) (h2 : hi ≤ -4 * tn - 1 + 4 * ε) : |tn - c2| ≤ ε := by
  unfold c2
  rw [abs_le]
  constructor <;> linarith

end Coerce
end Glue
end ThomsonN7

end Asm_Coerce

section Asm_Coerce2
/-!
# Relaxed contact certificates (Coerce2)

`Coerce.Contact1` / `Contact2` need an *exact* double root of `F` at a rational node, which integer
SDP data cannot provide.  Here the factorisation is relaxed to

  `s · F = (q y - p)² · G + R`   (resp. `(q1 y - p1)² (q2 y - p2)² · G + R`)

with integers `s > 0`, polynomials `G, R` with `G ≥ g0 > 0` and `R ≥ 0` on `[0, 1]` (both by exact
Bernstein chains).  Then `F ≥ 0` on `[0, 1]` (so `H ≤ phi`), and `F ≤ 2 Dq δ` forces
`g0 (q y - p)² ≤ 2 s Dq δ`, i.e. the same coercivity as in the exact case with `Dq` replaced by
`s Dq`.
-/

namespace ThomsonN7
namespace Glue
namespace Coerce

open CutOneD Base

/-! ## A. One node -/

theorem Contact1R.factor (c : Contact1R) (hc : c.check = true) (y : ℝ) :
    c.s * peval (Fpoly c.Q c.Dq) y = (c.q * y - c.p) ^ 2 * peval c.G y + peval c.R y := by
  simp only [Contact1R.check, Bool.and_eq_true, decide_eq_true_eq] at hc
  have h := peval_eq_zero_of_all _ hc.1.1.2 y
  simp only [peval_padd, peval_pneg, peval_pmul, peval_pscale, peval_lin] at h
  push_cast at h
  nlinarith [h]

theorem Contact1R.G_ge (c : Contact1R) (hc : c.check = true) {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) :
    (c.g0n : ℝ) / c.g0d ≤ peval c.G y := by
  simp only [Contact1R.check, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, hg0d⟩, -⟩, hch⟩, -⟩ := hc
  have := chainOK_nonneg _ c.pieces 0 1 1 1 one_pos one_pos hch y (by simpa using h0)
    (by simpa using h1)
  simp only [peval_padd, peval_pscale, peval_pneg, peval] at this
  have hd : (0 : ℝ) < c.g0d := by exact_mod_cast hg0d
  rw [div_le_iff₀ hd]
  push_cast at this
  linarith

theorem Contact1R.R_nonneg (c : Contact1R) (hc : c.check = true) {y : ℝ} (h0 : 0 ≤ y)
    (h1 : y ≤ 1) : 0 ≤ peval c.R y := by
  simp only [Contact1R.check, Bool.and_eq_true, decide_eq_true_eq] at hc
  have := chainOK_nonneg _ c.piecesR 0 1 1 1 one_pos one_pos hc.2 y (by simpa using h0)
    (by simpa using h1)
  exact this

/-- **Coercivity, one node, relaxed.**  `2 s Dq δ ≤ g0 (q η)²` puts `t` within `τ` of `ν`. -/
theorem Contact1R.tube (c : Contact1R) (hc : c.check = true) {δ η ν τ : ℝ} (hη : 0 ≤ η)
    (hδ : 2 * c.s * c.Dq * δ ≤ ((c.g0n : ℝ) / c.g0d) * (c.q * η) ^ 2)
    (hτ : |1 - 2 * ((c.p : ℝ) / c.q) ^ 2 - ν| + 2 * η * (2 * ((c.p : ℝ) / c.q) + η) ≤ τ)
    {t : ℝ} (h1 : -1 ≤ t) (h2 : t < 1) :
    peval c.Q t / c.Dq ≤ phi t ∧ (phi t - peval c.Q t / c.Dq ≤ δ → |t - ν| ≤ τ) := by
  have hc' := hc
  simp only [Contact1R.check, Bool.and_eq_true, decide_eq_true_eq] at hc'
  obtain ⟨⟨⟨⟨⟨⟨⟨hD, hq⟩, hs⟩, hg0n⟩, hg0d⟩, -⟩, -⟩, -⟩ := hc'
  have hy := yOf_pos h2
  have hy1 := yOf_le_one h1 h2
  have hG := c.G_ge hc hy.le hy1
  have hR := c.R_nonneg hc hy.le hy1
  have hfac := c.factor hc (yOf t)
  have hg0 : (0 : ℝ) < (c.g0n : ℝ) / c.g0d := by positivity
  have hqR : (0 : ℝ) < c.q := by exact_mod_cast hq
  have hsR : (0 : ℝ) < c.s := by exact_mod_cast hs
  have hLG : ((c.g0n : ℝ) / c.g0d) * (c.q * yOf t - c.p) ^ 2 ≤
      (c.q * yOf t - c.p) ^ 2 * peval c.G (yOf t) := by
    nlinarith [sq_nonneg (c.q * yOf t - c.p)]
  have hsF : ((c.g0n : ℝ) / c.g0d) * (c.q * yOf t - c.p) ^ 2 ≤
      c.s * peval (Fpoly c.Q c.Dq) (yOf t) := by linarith
  have hF : 0 ≤ peval (Fpoly c.Q c.Dq) (yOf t) := by
    have h0 : 0 ≤ (c.s : ℝ) * peval (Fpoly c.Q c.Dq) (yOf t) :=
      le_trans (mul_nonneg hg0.le (sq_nonneg _)) hsF
    exact nonneg_of_mul_nonneg_right h0 hsR
  refine ⟨H_le_phi_of_F hD h2 hF, fun hs' => ?_⟩
  have hFle := F_le_of_slack hD h2 hy1 hF hs'
  have h3 : ((c.g0n : ℝ) / c.g0d) * (c.q * yOf t - c.p) ^ 2 ≤
      ((c.g0n : ℝ) / c.g0d) * (c.q * η) ^ 2 := by
    calc ((c.g0n : ℝ) / c.g0d) * (c.q * yOf t - c.p) ^ 2
        ≤ c.s * peval (Fpoly c.Q c.Dq) (yOf t) := hsF
      _ ≤ c.s * (2 * c.Dq * δ) := mul_le_mul_of_nonneg_left hFle hsR.le
      _ = 2 * c.s * c.Dq * δ := by ring
      _ ≤ _ := hδ
  have h4 : (c.q * yOf t - c.p) ^ 2 ≤ (c.q * η) ^ 2 := le_of_mul_le_mul_left h3 hg0
  have h5 : |c.q * yOf t - c.p| ≤ c.q * η := abs_le_of_sq_le_sq h4 (by positivity)
  have h6 : |yOf t - (c.p : ℝ) / c.q| ≤ η := by
    have e : (c.q : ℝ) * yOf t - c.p = c.q * (yOf t - (c.p : ℝ) / c.q) := by field_simp
    rw [e, abs_mul, abs_of_pos hqR] at h5
    exact le_of_mul_le_mul_left h5 hqR
  have := abs_t_sub_le hy (by positivity) h6 hτ
  rwa [one_sub_two_yOf_sq h2.le] at this

/-- `hB` (pole--ring class, node `0`) from a relaxed one-node certificate. -/
theorem Contact1R.hB (c : Contact1R) (hc : c.check = true) {δ η τ : ℝ} (hη : 0 ≤ η)
    (hδ : 2 * c.s * c.Dq * δ ≤ ((c.g0n : ℝ) / c.g0d) * (c.q * η) ^ 2)
    (hτ : |1 - 2 * ((c.p : ℝ) / c.q) ^ 2| + 2 * η * (2 * ((c.p : ℝ) / c.q) + η) ≤ τ) :
    ∀ t, -1 ≤ t → t < 1 →
      peval c.Q t / c.Dq ≤ phi t ∧ (phi t - peval c.Q t / c.Dq ≤ δ → |t| ≤ τ) := by
  intro t h1 h2
  have := c.tube hc (ν := 0) hη hδ (by simpa using hτ) h1 h2
  simpa using this

/-! ## B. Two nodes -/

theorem Contact2R.factor (c : Contact2R) (hc : c.check = true) (y : ℝ) :
    c.s * peval (Fpoly c.Q c.Dq) y =
      ((c.q1 * y - c.p1) * (c.q2 * y - c.p2)) ^ 2 * peval c.G y + peval c.R y := by
  simp only [Contact2R.check, Bool.and_eq_true, decide_eq_true_eq] at hc
  have h := peval_eq_zero_of_all _ hc.1.1.2 y
  simp only [peval_padd, peval_pneg, peval_pmul, peval_pscale, peval_lin] at h
  push_cast at h
  nlinarith [h]

theorem Contact2R.G_ge (c : Contact2R) (hc : c.check = true) {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) :
    (c.g0n : ℝ) / c.g0d ≤ peval c.G y := by
  simp only [Contact2R.check, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, hg0d⟩, -⟩, hch⟩, -⟩ := hc
  have := chainOK_nonneg _ c.pieces 0 1 1 1 one_pos one_pos hch y (by simpa using h0)
    (by simpa using h1)
  simp only [peval_padd, peval_pscale, peval_pneg, peval] at this
  have hd : (0 : ℝ) < c.g0d := by exact_mod_cast hg0d
  rw [div_le_iff₀ hd]
  push_cast at this
  linarith

theorem Contact2R.R_nonneg (c : Contact2R) (hc : c.check = true) {y : ℝ} (h0 : 0 ≤ y)
    (h1 : y ≤ 1) : 0 ≤ peval c.R y := by
  simp only [Contact2R.check, Bool.and_eq_true, decide_eq_true_eq] at hc
  have := chainOK_nonneg _ c.piecesR 0 1 1 1 one_pos one_pos hc.2 y (by simpa using h0)
    (by simpa using h1)
  exact this

/-- **Coercivity, two nodes, relaxed.** -/
theorem Contact2R.tube (c : Contact2R) (hc : c.check = true) {δ η ν1 ν2 τ : ℝ} (hη : 0 ≤ η)
    (hδ : 2 * c.s * c.Dq * δ ≤ ((c.g0n : ℝ) / c.g0d) *
      (c.q1 * c.q2 * η * ((c.p1 : ℝ) / c.q1 - (c.p2 : ℝ) / c.q2) / 2) ^ 2)
    (hτ1 : |1 - 2 * ((c.p1 : ℝ) / c.q1) ^ 2 - ν1| + 2 * η * (2 * ((c.p1 : ℝ) / c.q1) + η) ≤ τ)
    (hτ2 : |1 - 2 * ((c.p2 : ℝ) / c.q2) ^ 2 - ν2| + 2 * η * (2 * ((c.p2 : ℝ) / c.q2) + η) ≤ τ)
    {t : ℝ} (h1 : -1 ≤ t) (h2 : t < 1) :
    peval c.Q t / c.Dq ≤ phi t ∧
      (phi t - peval c.Q t / c.Dq ≤ δ → |t - ν1| ≤ τ ∨ |t - ν2| ≤ τ) := by
  have hc' := hc
  simp only [Contact2R.check, Bool.and_eq_true, decide_eq_true_eq] at hc'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hD, hq1⟩, hq2⟩, hs⟩, hg0n⟩, hg0d⟩, -⟩, -⟩, -⟩ := hc'
  have hy := yOf_pos h2
  have hy1 := yOf_le_one h1 h2
  have hG := c.G_ge hc hy.le hy1
  have hR := c.R_nonneg hc hy.le hy1
  have hfac := c.factor hc (yOf t)
  have hg0 : (0 : ℝ) < (c.g0n : ℝ) / c.g0d := by positivity
  have hq1R : (0 : ℝ) < c.q1 := by exact_mod_cast hq1
  have hq2R : (0 : ℝ) < c.q2 := by exact_mod_cast hq2
  have hsR : (0 : ℝ) < c.s := by exact_mod_cast hs
  set A := (c.q1 * yOf t - c.p1) * (c.q2 * yOf t - c.p2) with hA
  have hLG : ((c.g0n : ℝ) / c.g0d) * A ^ 2 ≤ A ^ 2 * peval c.G (yOf t) := by
    nlinarith [sq_nonneg A]
  have hsF : ((c.g0n : ℝ) / c.g0d) * A ^ 2 ≤ c.s * peval (Fpoly c.Q c.Dq) (yOf t) := by
    linarith
  have hF : 0 ≤ peval (Fpoly c.Q c.Dq) (yOf t) := by
    have h0 : 0 ≤ (c.s : ℝ) * peval (Fpoly c.Q c.Dq) (yOf t) :=
      le_trans (mul_nonneg hg0.le (sq_nonneg _)) hsF
    exact nonneg_of_mul_nonneg_right h0 hsR
  refine ⟨H_le_phi_of_F hD h2 hF, fun hs' => ?_⟩
  have hFle := F_le_of_slack hD h2 hy1 hF hs'
  set B := c.q1 * c.q2 * η * ((c.p1 : ℝ) / c.q1 - (c.p2 : ℝ) / c.q2) / 2 with hB
  have h3 : ((c.g0n : ℝ) / c.g0d) * A ^ 2 ≤ ((c.g0n : ℝ) / c.g0d) * B ^ 2 := by
    calc ((c.g0n : ℝ) / c.g0d) * A ^ 2 ≤ c.s * peval (Fpoly c.Q c.Dq) (yOf t) := hsF
      _ ≤ c.s * (2 * c.Dq * δ) := mul_le_mul_of_nonneg_left hFle hsR.le
      _ = 2 * c.s * c.Dq * δ := by ring
      _ ≤ _ := hδ
  have h4 : A ^ 2 ≤ B ^ 2 := le_of_mul_le_mul_left h3 hg0
  have h5 : |A| ≤ |B| := sq_le_sq.1 h4
  have hA' : A = c.q1 * c.q2 * ((yOf t - (c.p1 : ℝ) / c.q1) * (yOf t - (c.p2 : ℝ) / c.q2)) := by
    rw [hA]; field_simp
  have hB' : |B| = c.q1 * c.q2 * (η * |(c.p1 : ℝ) / c.q1 - (c.p2 : ℝ) / c.q2| / 2) := by
    rw [hB]
    have : c.q1 * c.q2 * η * ((c.p1 : ℝ) / c.q1 - (c.p2 : ℝ) / c.q2) / 2 =
        (c.q1 * c.q2 * η / 2) * ((c.p1 : ℝ) / c.q1 - (c.p2 : ℝ) / c.q2) := by ring
    rw [this, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ c.q1 * c.q2 * η / 2)]
    ring
  rw [hA', hB', abs_mul, abs_of_pos (by positivity : (0 : ℝ) < c.q1 * c.q2)] at h5
  have h6 := le_of_mul_le_mul_left h5 (by positivity : (0 : ℝ) < c.q1 * c.q2)
  rcases two_node_alt hη h6 with h7 | h7
  · left
    have := abs_t_sub_le hy (by positivity) h7 hτ1
    rwa [one_sub_two_yOf_sq h2.le] at this
  · right
    have := abs_t_sub_le hy (by positivity) h7 hτ2
    rwa [one_sub_two_yOf_sq h2.le] at this

/-- `hC` (ring--ring class, nodes `c1, c2`) from a relaxed two-node certificate. -/
theorem Contact2R.hC (c : Contact2R) (hc : c.check = true) {δ η τ ε1 ε2 : ℝ} (hη : 0 ≤ η)
    (hδ : 2 * c.s * c.Dq * δ ≤ ((c.g0n : ℝ) / c.g0d) *
      (c.q1 * c.q2 * η * ((c.p1 : ℝ) / c.q1 - (c.p2 : ℝ) / c.q2) / 2) ^ 2)
    (hn1 : |1 - 2 * ((c.p1 : ℝ) / c.q1) ^ 2 - c1| ≤ ε1)
    (hn2 : |1 - 2 * ((c.p2 : ℝ) / c.q2) ^ 2 - c2| ≤ ε2)
    (hτ1 : ε1 + 2 * η * (2 * ((c.p1 : ℝ) / c.q1) + η) ≤ τ)
    (hτ2 : ε2 + 2 * η * (2 * ((c.p2 : ℝ) / c.q2) + η) ≤ τ) :
    ∀ t, -1 ≤ t → t < 1 →
      peval c.Q t / c.Dq ≤ phi t ∧
        (phi t - peval c.Q t / c.Dq ≤ δ → |t - c1| ≤ τ ∨ |t - c2| ≤ τ) := by
  intro t h1 h2
  exact c.tube hc hη hδ (by linarith) (by linarith) h1 h2

end Coerce
end Glue
end ThomsonN7

end Asm_Coerce2

section Asm_CertF
/-! # Fast (linear-traversal) checking of sum-of-squares blocks

The blocks `⟨d, l, Δ⟩` of `Cert1` are read by random access (`List.getD`), which costs `O(r³)`
kernel steps per block.  Here the same quadratic form and the same positivity check are
implemented by traversing the coefficient lists once, and proved equivalent to the random-access
versions.  Also: packed integer data (one natural-number literal per array, decoded in the kernel).
-/

namespace ThomsonN7

open Kron Kron.Ex
namespace Cert

open ThreePoint

/-! ## Packed integer data -/

/-! ## The quadratic form of a block, by list traversal -/

lemma getD_tail_succ (xs : List ℤ) (a : ℕ) : xs.tail.getD a 0 = xs.getD (a + 1) 0 := by
  cases xs <;> simp

lemma getD_tail_succ' (xs : List (List ℤ)) (a : ℕ) : xs.tail.getD a [] = xs.getD (a + 1) [] := by
  cases xs <;> simp

lemma ev_linF (u v t : ℝ) : ∀ (τs : List (ℕ × ℕ × ℕ)) (xs : List ℤ),
    (linF τs xs).ev u v t
      = ∑ a ∈ Finset.range τs.length, (xs.getD a 0 : ℝ) * mv u v t (τs.getD a (0, 0, 0)) := by
  intro τs
  induction τs with
  | nil => intro xs; simp [linF]
  | cons τ τs ih =>
    intro xs
    rw [List.length_cons, Finset.sum_range_succ', linF, ev_add, ev_smulNZ, ih xs.tail]
    simp only [ev_mon, mv, List.getD_cons_succ, List.getD_cons_zero, getD_tail_succ]
    rw [add_comm]
    congr 1
    cases xs <;> simp

lemma ev_rowF (u v t : ℝ) (ta : ℕ × ℕ × ℕ) : ∀ (τs : List (ℕ × ℕ × ℕ)) (xs : List ℤ),
    (rowF ta τs xs).ev u v t
      = ∑ a ∈ Finset.range τs.length,
          (xs.getD a 0 : ℝ) * (mv u v t ta * mv u v t (τs.getD a (0, 0, 0))) := by
  intro τs
  induction τs with
  | nil => intro xs; simp [rowF]
  | cons τ τs ih =>
    intro xs
    rw [List.length_cons, Finset.sum_range_succ', rowF, ev_add, ev_smulNZ, ih xs.tail]
    simp only [ev_mon, mv, List.getD_cons_succ, List.getD_cons_zero, getD_tail_succ, pow_add]
    rw [add_comm]
    congr 1
    cases xs <;> simp [mul_comm, mul_left_comm, mul_assoc]

lemma ev_quadF (u v t : ℝ) (zs : List (ℕ × ℕ × ℕ)) : ∀ (tas : List (ℕ × ℕ × ℕ))
    (rows : List (List ℤ)),
    (quadF zs tas rows).ev u v t
      = ∑ a ∈ Finset.range tas.length, ∑ c ∈ Finset.range zs.length,
          ((rows.getD a []).getD c 0 : ℝ)
            * (mv u v t (tas.getD a (0, 0, 0)) * mv u v t (zs.getD c (0, 0, 0))) := by
  intro tas
  induction tas with
  | nil => intro rows; simp [quadF]
  | cons ta tas ih =>
    intro rows
    rw [List.length_cons, Finset.sum_range_succ', quadF, ev_add, ev_rowF, ih rows.tail]
    simp only [getD_tail_succ']
    rw [add_comm]
    congr 1
    cases rows <;> simp

lemma ev_sqF (u v t : ℝ) (zs : List (ℕ × ℕ × ℕ)) : ∀ (fs : List (ℕ × ℕ × ℕ)) (ds : List ℤ)
    (ls : List (List ℤ)),
    (sqF zs fs ds ls).ev u v t
      = ∑ q ∈ Finset.range fs.length, (ds.getD q 0 : ℝ)
          * (∑ a ∈ Finset.range zs.length, ((ls.getD q []).getD a 0 : ℝ)
              * mv u v t (zs.getD a (0, 0, 0))) ^ 2 := by
  intro fs
  induction fs with
  | nil => intro ds ls; simp [sqF]
  | cons f fs ih =>
    intro ds ls
    rw [List.length_cons, Finset.sum_range_succ', sqF, ev_add, ev_smulNZ, ev_sq, ev_linF,
      ih ds.tail ls.tail]
    simp only [getD_tail_succ, getD_tail_succ']
    rw [add_comm]
    congr 1
    cases ds <;> cases ls <;> simp

/-- The list-traversal form of a block has the same value as the random-access form. -/
lemma ev_sqfF (b : Blk) (zs : List (ℕ × ℕ × ℕ)) (u v t : ℝ) :
    (sqfF b zs).ev u v t = (sqfE b zs).ev u v t := by
  rw [sqfF, ev_add, ev_sqF, ev_quadF, ev_sqfE]
  have h2 : (∑ a ∈ Finset.range zs.length, ∑ c ∈ Finset.range zs.length,
        ((b.Δ.getD a []).getD c 0 : ℝ)
          * (mv u v t (zs.getD a (0, 0, 0)) * mv u v t (zs.getD c (0, 0, 0))))
      = ∑ a ∈ Finset.range zs.length, ∑ c ∈ Finset.range zs.length,
        zval zs u v t a * (b.del a c : ℝ) * zval zs u v t c := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    simp only [Blk.del, zval, zt, mv]
    ring
  rw [h2]
  rfl

/-! ## The positivity check, by list traversal -/

lemma getD_map_list (f : List ℤ → List ℤ) (hf : f [] = []) (M : List (List ℤ)) (i : ℕ) :
    (M.map f).getD i [] = f (M.getD i []) := by
  have := List.getD_map M ([] : List ℤ) (n := i) f
  rwa [hf] at this

lemma transposeSq_getD : ∀ (n : ℕ) (M : List (List ℤ)) (i : ℕ), i < n → ∀ j,
    ((transposeSq n M).getD i []).getD j 0 = (M.getD j []).getD i 0 := by
  intro n
  induction n with
  | zero => intro M i hi; omega
  | succ n ih =>
    intro M i hi j
    cases i with
    | zero =>
      simp only [transposeSq, List.getD_cons_zero]
      have := List.getD_map M ([] : List ℤ) (n := j) (fun row => row.headD 0)
      simp only [List.headD_nil] at this
      rw [this]
      generalize M.getD j [] = row
      cases row <;> simp
    | succ i =>
      simp only [transposeSq, List.getD_cons_succ]
      rw [ih (M.map List.tail) i (by omega) j, getD_map_list List.tail rfl]
      generalize M.getD j [] = row
      cases row <;> simp

lemma offAbs_eq (i : ℕ) : ∀ (row : List ℤ) (k : ℕ), offAbs i k row
    = ∑ j ∈ Finset.range row.length, (if i = k + j then (0 : ℤ) else |row.getD j 0|) := by
  intro row
  induction row with
  | nil => intro k; simp [offAbs]
  | cons x xs ih =>
    intro k
    rw [List.length_cons, Finset.sum_range_succ', offAbs, ih (k + 1)]
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show k + 1 + j = k + (j + 1) by omega]

lemma sum_range_le_offAbs (i r : ℕ) (row : List ℤ) :
    ∑ j ∈ Finset.range r, (if i = j then (0 : ℤ) else |row.getD j 0|) ≤ offAbs i 0 row := by
  rw [offAbs_eq]
  simp only [zero_add]
  set g : ℕ → ℤ := fun j => if i = j then (0 : ℤ) else |row.getD j 0| with hg
  have hnn : ∀ j, 0 ≤ g j := fun j => by simp only [hg]; split_ifs <;> simp
  have hz : ∀ j, row.length ≤ j → g j = 0 := fun j hj => by
    simp only [hg, List.getD_eq_default _ _ hj]; split_ifs <;> simp
  calc ∑ j ∈ Finset.range r, g j ≤ ∑ j ∈ Finset.range (r + row.length), g j :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.2 (Nat.le_add_right _ _)) fun j _ _ => hnn j
    _ = ∑ j ∈ Finset.range row.length, g j := by
        symm
        refine Finset.sum_subset (Finset.range_subset_range.2 (Nat.le_add_left _ _)) ?_
        intro j hj hj'
        exact hz j (by simpa using hj')

lemma domAll_spec : ∀ (M : List (List ℤ)) (k : ℕ), domAll k M = true → ∀ i,
    offAbs (k + i) 0 (M.getD i []) ≤ (M.getD i []).getD (k + i) 0 := by
  intro M
  induction M with
  | nil => intro k _ i; simp [offAbs]
  | cons row rows ih =>
    intro k h i
    simp only [domAll, Bool.and_eq_true, decide_eq_true_eq] at h
    cases i with
    | zero => simpa using h.1
    | succ i =>
      have := ih (k + 1) h.2 i
      simpa [show k + (i + 1) = k + 1 + i by omega] using this

lemma getD_nonneg_of_all : ∀ {l : List ℤ}, (∀ x ∈ l, 0 ≤ x) → ∀ i, 0 ≤ l.getD i 0 := by
  intro l
  induction l with
  | nil => intro _ i; simp
  | cons x xs ih =>
    intro h i
    cases i with
    | zero => simpa using h x (by simp)
    | succ i => simpa using ih (fun y hy => h y (by simp [hy])) i

/-- Soundness of the fast check: it implies the random-access check of `Cert1`. -/
lemma okF_sound {r : ℕ} {b : Blk} (h : okF r b = true) : b.ok r = true := by
  simp only [okF, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hd, hsym⟩, hdom⟩ := h
  have hsym' : ∀ i < r, ∀ j < r, b.del i j = b.del j i := by
    intro i hi j hj
    have h1 : ((b.Δ.map (List.take r)).getD i []).getD j 0 = (b.Δ.getD i []).getD j 0 := by
      rw [getD_map_list (List.take r) (by simp)]
      simp [List.getD_eq_getElem?_getD, hj]
    rw [hsym] at h1
    rw [transposeSq_getD r b.Δ i hi j] at h1
    simp only [Blk.del]
    exact h1.symm
  simp only [Blk.ok, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  intro i hi
  refine ⟨⟨?_, fun j hj => hsym' i hi j hj⟩, ?_⟩
  · exact getD_nonneg_of_all hd i
  · rw [Blk.list_sum_range_map (fun j => if i = j then (0 : ℤ) else |b.del i j|) r]
    have h2 := domAll_spec b.Δ 0 hdom i
    simp only [zero_add] at h2
    refine le_trans (sum_range_le_offAbs i r (b.Δ.getD i [])) (le_trans h2 ?_)
    simp [Blk.del]

end Cert
end ThomsonN7

end Asm_CertF

section Asm_CertT
namespace ThomsonN7

open Kron Kron.Ex
namespace Cert

open ThreePoint

/-! ## Multiplier atoms of the typed certificates -/

lemma codeT_nonneg (an : ℤ) (ad : ℕ) (bn : ℤ) (bd : ℕ) (j : ℕ) {u v t : ℝ}
    (h : GramCut an ad u v t) (hb : (bd : ℝ) * u ≤ bn) :
    0 ≤ (codeT an ad bn bd j).ev u v t := by
  unfold codeT
  split_ifs with hj
  · simp only [ev_sub, ev_c, ev_smul, ev_U]
    push_cast
    linarith
  · exact codeE_nonneg an ad j h

lemma gT_nonneg (an : ℤ) (ad : ℕ) (bn : ℤ) (bd : ℕ) (g : List ℕ) {u v t : ℝ}
    (h : GramCut an ad u v t) (hb : (bd : ℝ) * u ≤ bn) :
    0 ≤ (gT an ad bn bd g).ev u v t := by
  induction g with
  | nil => simp [gT]
  | cons code g ih =>
    simp only [gT, List.foldr_cons, ev_mul] at ih ⊢
    exact mul_nonneg (codeT_nonneg an ad bn bd code h hb) ih

lemma tblkE_nonneg (an : ℤ) (ad : ℕ) (bn : ℤ) (bd : ℕ) {s : TBlk}
    (h : okF s.z.length s.B = true) {u v t : ℝ} (hg : GramCut an ad u v t)
    (hb : (bd : ℝ) * u ≤ bn) : 0 ≤ (tblkE an ad bn bd s).ev u v t := by
  rw [tblkE, ev_mul, ev_sqfF]
  exact mul_nonneg (gT_nonneg an ad bn bd s.g hg hb) (sqfE_nonneg (okF_sound h) _ _ _)

lemma tsum_nonneg (an : ℤ) (ad : ℕ) (bn : ℤ) (bd : ℕ) (S : List TBlk)
    (hS : S.all (fun s => okF s.z.length s.B) = true) {u v t : ℝ} (hg : GramCut an ad u v t)
    (hb : (bd : ℝ) * u ≤ bn) :
    0 ≤ ((S.map (tblkE an ad bn bd)).map fun e => e.ev u v t).sum := by
  refine List.sum_nonneg fun x hx => ?_
  simp only [List.mem_map] at hx
  obtain ⟨e, ⟨s, hs, rfl⟩, rfl⟩ := hx
  exact tblkE_nonneg an ad bn bd (List.all_eq_true.mp hS s hs) hg hb

/-! ## Kronecker values of the quadratic form of a block -/

lemma cast_kev (w D : ℕ) (e : Ex) :
    ((e.kev w D : ℤ) : ℝ) = e.ev ((2 : ℝ) ^ w) ((2 : ℝ) ^ (w * D)) ((2 : ℝ) ^ (w * D * D)) := by
  induction e with
  | c n => simp [Ex.kev, Ex.ev]
  | mon a b d =>
    simp only [Ex.kev, Ex.ev]
    push_cast
    rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
    congr 1
    ring
  | add p q ihp ihq => simp only [Ex.kev, Ex.ev, Int.cast_add, ihp, ihq]
  | mul p q ihp ihq => simp only [Ex.kev, Ex.ev, Int.cast_mul, ihp, ihq]

lemma zval_two (zs : List (ℕ × ℕ × ℕ)) (w D a : ℕ) :
    zval zs ((2 : ℝ) ^ w) ((2 : ℝ) ^ (w * D)) ((2 : ℝ) ^ (w * D * D)) a
      = ((kw w D zs a : ℤ) : ℝ) := by
  simp only [zval, kw]
  push_cast
  rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
  congr 1
  ring

lemma kev_sqfF (b : Blk) (zs : List (ℕ × ℕ × ℕ)) (w D : ℕ) :
    (sqfF b zs).kev w D = sqfVal b zs.length (kw w D zs) := by
  apply Int.cast_injective (α := ℝ)
  rw [cast_kev, ev_sqfF, ev_sqfE]
  simp only [sqfVal, zval_two]
  push_cast
  rfl

/-! ## Size bounds of packed blocks -/

lemma natAbs_field_le (B x : ℕ) (hB : 0 < B) :
    ((((x % (1 <<< B) : ℕ) : ℤ) - ((1 <<< (B - 1) : ℕ) : ℤ))).natAbs ≤ 2 ^ (B - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, B = k + 1 := ⟨B - 1, by omega⟩
  have h1 : (1 <<< (k + 1) : ℕ) = 2 * 2 ^ k := by
    rw [Nat.one_shiftLeft, pow_succ]; ring
  have h2 : (1 <<< (k + 1 - 1) : ℕ) = 2 ^ k := by
    rw [Nat.add_sub_cancel, Nat.one_shiftLeft]
  have h3 : x % (1 <<< (k + 1)) < 2 * 2 ^ k := by
    rw [← h1]; exact Nat.mod_lt _ (by rw [h1]; positivity)
  rw [h2, Nat.add_sub_cancel]
  omega

lemma unpackI_natAbs_le (B : ℕ) (hB : 0 < B) : ∀ (n x : ℕ), ∀ v ∈ unpackI B n x,
    v.natAbs ≤ 2 ^ (B - 1)
  | 0, _ => by simp [unpackI]
  | n + 1, x => by
    intro v hv
    simp only [unpackI, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact natAbs_field_le B x hB
    · exact unpackI_natAbs_le B hB n (x >>> B) v hv

lemma unpackM_natAbs_le (B cols : ℕ) (hB : 0 < B) : ∀ (rows x : ℕ), ∀ row ∈ unpackM B cols rows x,
    ∀ v ∈ row, v.natAbs ≤ 2 ^ (B - 1)
  | 0, _ => by simp [unpackM]
  | rows + 1, x => by
    intro row hrow v hv
    simp only [unpackM, List.mem_cons] at hrow
    rcases hrow with rfl | hrow
    · exact unpackI_natAbs_le B hB cols _ v hv
    · exact unpackM_natAbs_le B cols hB rows _ row hrow v hv

lemma l1_smulNZ_le (a : ℤ) (e : Ex) : (smulNZ a e).l1 ≤ a.natAbs * e.l1 := by
  unfold smulNZ
  split_ifs with h
  · simp [Ex.l1]
  · simp [Ex.smul, Ex.l1]

lemma l1_linF_le (M : ℕ) : ∀ (τs : List (ℕ × ℕ × ℕ)) (xs : List ℤ),
    (∀ x ∈ xs, x.natAbs ≤ M) → (linF τs xs).l1 ≤ τs.length * M
  | [], xs, _ => by simp [linF, Ex.l1]
  | τ :: τs, xs, h => by
    have hh : (xs.headD 0).natAbs ≤ M := by
      cases xs with
      | nil => simp
      | cons x xs => exact h x (by simp)
    have ht : ∀ x ∈ xs.tail, x.natAbs ≤ M := fun x hx => h x (List.mem_of_mem_tail hx)
    have h0 := l1_linF_le M τs xs.tail ht
    have h1 := l1_smulNZ_le (xs.headD 0) (mon τ.1 τ.2.1 τ.2.2)
    simp only [linF, Ex.l1, List.length_cons] at h1 h0 ⊢
    nlinarith

lemma l1_rowF_le (ta : ℕ × ℕ × ℕ) (M : ℕ) : ∀ (τs : List (ℕ × ℕ × ℕ)) (xs : List ℤ),
    (∀ x ∈ xs, x.natAbs ≤ M) → (rowF ta τs xs).l1 ≤ τs.length * M
  | [], xs, _ => by simp [rowF, Ex.l1]
  | τ :: τs, xs, h => by
    have hh : (xs.headD 0).natAbs ≤ M := by
      cases xs with
      | nil => simp
      | cons x xs => exact h x (by simp)
    have ht : ∀ x ∈ xs.tail, x.natAbs ≤ M := fun x hx => h x (List.mem_of_mem_tail hx)
    have h0 := l1_rowF_le ta M τs xs.tail ht
    have h1 := l1_smulNZ_le (xs.headD 0)
      (mon (ta.1 + τ.1) (ta.2.1 + τ.2.1) (ta.2.2 + τ.2.2))
    simp only [rowF, Ex.l1, List.length_cons] at h1 h0 ⊢
    nlinarith

lemma l1_quadF_le (zs : List (ℕ × ℕ × ℕ)) (M : ℕ) : ∀ (tas : List (ℕ × ℕ × ℕ))
    (rows : List (List ℤ)), (∀ row ∈ rows, ∀ x ∈ row, x.natAbs ≤ M) →
    (quadF zs tas rows).l1 ≤ tas.length * (zs.length * M)
  | [], rows, _ => by simp [quadF, Ex.l1]
  | ta :: tas, rows, h => by
    have hh : ∀ x ∈ rows.headD [], x.natAbs ≤ M := by
      cases rows with
      | nil => simp
      | cons row rows => exact h row (by simp)
    have ht : ∀ row ∈ rows.tail, ∀ x ∈ row, x.natAbs ≤ M :=
      fun row hr => h row (List.mem_of_mem_tail hr)
    have h0 := l1_quadF_le zs M tas rows.tail ht
    have h1 := l1_rowF_le ta M zs (rows.headD []) hh
    simp only [quadF, Ex.l1, List.length_cons] at h1 h0 ⊢
    nlinarith

lemma l1_sqF_le (zs : List (ℕ × ℕ × ℕ)) (Md Ml : ℕ) : ∀ (fs : List (ℕ × ℕ × ℕ))
    (ds : List ℤ) (ls : List (List ℤ)), (∀ x ∈ ds, x.natAbs ≤ Md) →
    (∀ row ∈ ls, ∀ x ∈ row, x.natAbs ≤ Ml) →
    (sqF zs fs ds ls).l1 ≤ fs.length * (Md * (zs.length * Ml) ^ 2)
  | [], ds, ls, _, _ => by simp [sqF, Ex.l1]
  | f :: fs, ds, ls, hd, hl => by
    have hh : (ds.headD 0).natAbs ≤ Md := by
      cases ds with
      | nil => simp
      | cons x xs => exact hd x (by simp)
    have hd' : ∀ x ∈ ds.tail, x.natAbs ≤ Md := fun x hx => hd x (List.mem_of_mem_tail hx)
    have hh2 : ∀ x ∈ ls.headD [], x.natAbs ≤ Ml := by
      cases ls with
      | nil => simp
      | cons row rows => exact hl row (by simp)
    have hl' : ∀ row ∈ ls.tail, ∀ x ∈ row, x.natAbs ≤ Ml :=
      fun row hr => hl row (List.mem_of_mem_tail hr)
    have h0 := l1_sqF_le zs Md Ml fs ds.tail ls.tail hd' hl'
    have h1 := l1_smulNZ_le (ds.headD 0) (Ex.sq (linF zs (ls.headD [])))
    have h2 := l1_linF_le Ml zs (ls.headD []) hh2
    have h3 : (Ex.sq (linF zs (ls.headD []))).l1 ≤ (zs.length * Ml) ^ 2 := by
      simp only [Ex.sq, Ex.l1, pow_two]
      exact Nat.mul_le_mul h2 h2
    have h4 : (ds.headD 0).natAbs * (Ex.sq (linF zs (ls.headD []))).l1
        ≤ Md * (zs.length * Ml) ^ 2 := Nat.mul_le_mul hh h3
    simp only [sqF, Ex.l1, List.length_cons] at h0 h1 ⊢
    nlinarith

lemma l1_sqfF_le (b : Blk) (zs : List (ℕ × ℕ × ℕ)) (Md Ml MD : ℕ)
    (hd : ∀ x ∈ b.d, x.natAbs ≤ Md) (hl : ∀ row ∈ b.l, ∀ x ∈ row, x.natAbs ≤ Ml)
    (hD : ∀ row ∈ b.Δ, ∀ x ∈ row, x.natAbs ≤ MD) :
    (sqfF b zs).l1 ≤ zs.length * (Md * (zs.length * Ml) ^ 2) + zs.length * (zs.length * MD) := by
  have h1 := l1_sqF_le zs Md Ml zs b.d b.l hd hl
  have h2 := l1_quadF_le zs MD zs b.Δ hD
  simp only [sqfF, Ex.l1]
  omega

/-! ### Degrees -/

lemma degK_zero (e : Ex) : degK 0 e = e.dx := by
  induction e with
  | c n => simp [degK, Ex.dx]
  | mon a b d => simp [degK, Ex.dx, proj]
  | add p q ihp ihq => simp [degK, Ex.dx, ihp, ihq]
  | mul p q ihp ihq => simp [degK, Ex.dx, ihp, ihq]

lemma degK_one (e : Ex) : degK 1 e = e.dy := by
  induction e with
  | c n => simp [degK, Ex.dy]
  | mon a b d => simp [degK, Ex.dy, proj]
  | add p q ihp ihq => simp [degK, Ex.dy, ihp, ihq]
  | mul p q ihp ihq => simp [degK, Ex.dy, ihp, ihq]

lemma degK_two (e : Ex) : degK 2 e = e.dz := by
  induction e with
  | c n => simp [degK, Ex.dz]
  | mon a b d => simp [degK, Ex.dz, proj]
  | add p q ihp ihq => simp [degK, Ex.dz, ihp, ihq]
  | mul p q ihp ihq => simp [degK, Ex.dz, ihp, ihq]

lemma proj_add (k : ℕ) (a b : ℕ × ℕ × ℕ) :
    proj k (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2) = proj k a + proj k b := by
  unfold proj
  split_ifs <;> rfl

lemma proj_eta (k : ℕ) (a : ℕ × ℕ × ℕ) : proj k (a.1, a.2.1, a.2.2) = proj k a := rfl

lemma mxs_cons (k : ℕ) (τ : ℕ × ℕ × ℕ) (τs : List (ℕ × ℕ × ℕ)) :
    mxs k (τ :: τs) = max (proj k τ) (mxs k τs) := rfl

lemma degK_smulNZ_le (k : ℕ) (a : ℤ) (e : Ex) : degK k (smulNZ a e) ≤ degK k e := by
  unfold smulNZ
  split_ifs with h
  · simp [degK]
  · simp [Ex.smul, degK]

lemma degK_linF_le (k : ℕ) : ∀ (τs : List (ℕ × ℕ × ℕ)) (xs : List ℤ),
    degK k (linF τs xs) ≤ mxs k τs
  | [], xs => by simp [linF, degK, mxs]
  | τ :: τs, xs => by
    have h0 := degK_linF_le k τs xs.tail
    have h1 := degK_smulNZ_le k (xs.headD 0) (mon τ.1 τ.2.1 τ.2.2)
    simp only [linF, degK, mxs_cons, proj_eta] at h0 h1 ⊢
    omega

lemma degK_rowF_le (k : ℕ) (ta : ℕ × ℕ × ℕ) : ∀ (τs : List (ℕ × ℕ × ℕ)) (xs : List ℤ),
    degK k (rowF ta τs xs) ≤ proj k ta + mxs k τs
  | [], xs => by simp [rowF, degK, mxs]
  | τ :: τs, xs => by
    have h0 := degK_rowF_le k ta τs xs.tail
    have h1 := degK_smulNZ_le k (xs.headD 0)
      (mon (ta.1 + τ.1) (ta.2.1 + τ.2.1) (ta.2.2 + τ.2.2))
    simp only [rowF, degK, mxs_cons, proj_add] at h0 h1 ⊢
    omega

lemma degK_quadF_le (k : ℕ) (zs : List (ℕ × ℕ × ℕ)) : ∀ (tas : List (ℕ × ℕ × ℕ))
    (rows : List (List ℤ)), degK k (quadF zs tas rows) ≤ mxs k tas + mxs k zs
  | [], rows => by simp [quadF, degK, mxs]
  | ta :: tas, rows => by
    have h0 := degK_quadF_le k zs tas rows.tail
    have h1 := degK_rowF_le k ta zs (rows.headD [])
    simp only [quadF, degK, mxs_cons] at h0 h1 ⊢
    omega

lemma degK_sqF_le (k : ℕ) (zs : List (ℕ × ℕ × ℕ)) : ∀ (fs : List (ℕ × ℕ × ℕ)) (ds : List ℤ)
    (ls : List (List ℤ)), degK k (sqF zs fs ds ls) ≤ 2 * mxs k zs
  | [], ds, ls => by simp [sqF, degK]
  | f :: fs, ds, ls => by
    have h0 := degK_sqF_le k zs fs ds.tail ls.tail
    have h1 := degK_smulNZ_le k (ds.headD 0) (Ex.sq (linF zs (ls.headD [])))
    have h2 := degK_linF_le k zs (ls.headD [])
    simp only [sqF, degK, Ex.sq] at h0 h1 ⊢
    omega

lemma degK_sqfF_le (k : ℕ) (b : Blk) (zs : List (ℕ × ℕ × ℕ)) :
    degK k (sqfF b zs) ≤ 2 * mxs k zs := by
  have h1 := degK_sqF_le k zs zs b.d b.l
  have h2 := degK_quadF_le k zs zs b.Δ
  simp only [sqfF, degK]
  omega

/-! ## Analytic bounds of typed blocks -/

lemma TBlk.l1_le (s : TBlk) (h : s.wf = true) : (sqfF s.B s.z).l1 ≤ s.l1B := by
  simp only [TBlk.wf, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hd, hl⟩, hD⟩, -⟩ := h
  exact l1_sqfF_le s.B s.z _ _ _ (unpackI_natAbs_le s.Bd hd _ _)
    (unpackM_natAbs_le s.Bl s.r hl _ _) (unpackM_natAbs_le s.BD s.r hD _ _)

lemma l1_tblkE_le (an : ℤ) (ad : ℕ) (bn : ℤ) (bd : ℕ) (s : TBlk) (h : s.wf = true) :
    (tblkE an ad bn bd s).l1 ≤ (gT an ad bn bd s.g).l1 * s.l1B := by
  rw [tblkE, Ex.l1]
  exact Nat.mul_le_mul_left _ (s.l1_le h)

lemma degK_tblkE_le (k : ℕ) (an : ℤ) (ad : ℕ) (bn : ℤ) (bd : ℕ) (s : TBlk) :
    degK k (tblkE an ad bn bd s) ≤ degK k (gT an ad bn bd s.g) + 2 * mxs k s.z := by
  rw [tblkE, degK]
  have := degK_sqfF_le k s.B s.z
  omega

/-! ## Sums of expressions -/

lemma sumE_cons (x : Ex) (l : List Ex) : sumE (x :: l) = add x (sumE l) := rfl

lemma kev_sumE_map {α : Type*} (w D : ℕ) (f : α → Ex) : ∀ l : List α,
    (sumE (l.map f)).kev w D = (l.map fun x => (f x).kev w D).sum
  | [] => by simp [sumE, Ex.kev]
  | x :: l => by
    rw [List.map_cons, sumE_cons, Ex.kev, kev_sumE_map w D f l]
    simp

lemma l1_sumE_map {α : Type*} (f : α → Ex) (b : α → ℕ) : ∀ l : List α,
    (∀ x ∈ l, (f x).l1 ≤ b x) → (sumE (l.map f)).l1 ≤ (l.map b).sum
  | [], _ => by simp [sumE, Ex.l1]
  | x :: l, h => by
    rw [List.map_cons, sumE_cons, Ex.l1]
    have h1 := h x (by simp)
    have h2 := l1_sumE_map f b l (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons, List.sum_cons]
    omega

lemma degK_sumE_map {α : Type*} (k : ℕ) (f : α → Ex) (b : α → ℕ) : ∀ l : List α,
    (∀ x ∈ l, degK k (f x) ≤ b x) → degK k (sumE (l.map f)) ≤ (l.map b).foldr max 0
  | [], _ => by simp [sumE, degK]
  | x :: l, h => by
    rw [List.map_cons, sumE_cons, degK]
    have h1 := h x (by simp)
    have h2 := degK_sumE_map k f b l (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons, List.foldr_cons]
    omega

lemma kev_sub (w D : ℕ) (a b : Ex) : (sub a b).kev w D = a.kev w D - b.kev w D := by
  simp [Ex.sub, Ex.neg, Ex.kev, sub_eq_add_neg]

lemma l1_sub (a b : Ex) : (sub a b).l1 = a.l1 + b.l1 := by
  simp [Ex.sub, Ex.neg, Ex.l1]

lemma degK_sub (k : ℕ) (a b : Ex) : degK k (sub a b) = max (degK k a) (degK k b) := by
  simp [Ex.sub, Ex.neg, degK]

/-! ## The hybrid check -/

theorem hybChk_sound (fq : ℕ → ℕ → TBlk → ℤ)
    (hfq : ∀ w D s, s.wf = true → fq w D s = (sqfF s.B s.z).kev w D)
    (Fx : Ex) (an : ℤ) (ad : ℕ) (bn : ℤ) (bd : ℕ) (S : List TBlk)
    (h : hybChk fq Fx an ad bn bd S = true) (u v t : ℝ) :
    (idT Fx an ad bn bd S).ev u v t = 0 := by
  simp only [hybChk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hwf, hval⟩ := h
  have hwf' : ∀ s ∈ S, s.wf = true := fun s hs => List.all_eq_true.mp hwf s hs
  -- degree bounds
  have hdeg : ∀ k, degK k (idT Fx an ad bn bd S) ≤ idDeg k Fx an ad bn bd S := by
    intro k
    have h1 : degK k (sumE (S.map (tblkE an ad bn bd)))
        ≤ (S.map fun s => degK k (gT an ad bn bd s.g) + 2 * mxs k s.z).foldr max 0 :=
      degK_sumE_map k _ _ S fun s _ => degK_tblkE_le k an ad bn bd s
    rw [idT, degK_sub, idDeg]
    exact max_le_max le_rfl h1
  -- `ℓ¹` bound
  have hl1 : (idT Fx an ad bn bd S).l1 ≤ idL Fx an ad bn bd S := by
    have h1 : (sumE (S.map (tblkE an ad bn bd))).l1
        ≤ (S.map fun s => (gT an ad bn bd s.g).l1 * s.l1B).sum :=
      l1_sumE_map _ _ S fun s hs => l1_tblkE_le an ad bn bd s (hwf' s hs)
    rw [idT, l1_sub, idL]
    omega
  -- the Kronecker value
  have hk : (idT Fx an ad bn bd S).kev (hybW Fx an ad bn bd S) (hybD Fx an ad bn bd S) = 0 := by
    have hmap : (S.map fun s => (tblkE an ad bn bd s).kev (hybW Fx an ad bn bd S)
          (hybD Fx an ad bn bd S))
        = S.map fun s => (gT an ad bn bd s.g).kev (hybW Fx an ad bn bd S)
            (hybD Fx an ad bn bd S) * fq (hybW Fx an ad bn bd S) (hybD Fx an ad bn bd S) s := by
      refine List.map_congr_left fun s hs => ?_
      rw [tblkE, Ex.kev, hfq _ _ s (hwf' s hs)]
    rw [idT, kev_sub, kev_sumE_map, hmap]
    exact hval
  refine Ex.ev_eq_zero_of_kev _ (hybW Fx an ad bn bd S) (hybD Fx an ad bn bd S) ?_ ?_ ?_ ?_ hk u v t
  · rw [← degK_zero]
    have := hdeg 0
    simp only [hybD]
    omega
  · rw [← degK_one]
    have := hdeg 1
    simp only [hybD]
    omega
  · rw [← degK_two]
    have := hdeg 2
    simp only [hybD]
    omega
  · exact lt_of_le_of_lt hl1 Nat.lt_log2_self

end Cert
end ThomsonN7

namespace ThomsonN7

open Kron Kron.Ex
namespace Cert

/-! # Flat (Nat-only inner loops) evaluation of the quadratic form of a packed block -/

lemma rowsN_length (B cols : ℕ) (ps : List ℕ) : ∀ rows x, (rowsN B cols ps rows x).length = rows
  | 0, _ => rfl
  | rows + 1, x => by simp [rowsN, rowsN_length B cols ps rows]

lemma dotN_spec (B : ℕ) : ∀ (ps : List ℕ) (x : ℕ),
    (dotN B ps x : ℤ) - offB B * (ps.sum : ℕ)
      = ∑ a ∈ Finset.range ps.length, (unpackI B ps.length x).getD a 0 * (ps.getD a 0 : ℤ) := by
  intro ps
  induction ps with
  | nil => intro x; simp [dotN]
  | cons p ps ih =>
    intro x
    have h := ih (x >>> B)
    rw [List.length_cons, Finset.sum_range_succ', unpackI]
    simp only [dotN, List.getD_cons_succ, List.getD_cons_zero, List.sum_cons]
    generalize ps.sum = S at h ⊢
    simp only [offB] at h ⊢
    push_cast at h ⊢
    linarith

lemma rowsN_spec (B cols : ℕ) (ps : List ℕ) (hps : ps.length = cols) :
    ∀ (rows x q : ℕ), q < rows →
      (((rowsN B cols ps rows x).getD q 0 : ℕ) : ℤ) - offB B * (ps.sum : ℕ)
        = ∑ a ∈ Finset.range cols,
            ((unpackM B cols rows x).getD q []).getD a 0 * (ps.getD a 0 : ℤ) := by
  intro rows
  induction rows with
  | zero => intro x q hq; omega
  | succ rows ih =>
    intro x q hq
    cases q with
    | zero =>
      have := dotN_spec B ps (x % (1 <<< (B * cols)))
      rw [hps] at this
      simpa [rowsN, unpackM] using this
    | succ q =>
      simp only [rowsN, unpackM, List.getD_cons_succ]
      exact ih _ q (by omega)

lemma comb1_spec (Bd Bl : ℕ) (Pt : ℤ) : ∀ (Ls : List ℕ) (xd : ℕ),
    comb1 Bd Bl Pt Ls xd
      = ∑ q ∈ Finset.range Ls.length, (unpackI Bd Ls.length xd).getD q 0
          * ((((Ls.getD q 0 : ℕ) : ℤ) - offB Bl * Pt) * (((Ls.getD q 0 : ℕ) : ℤ) - offB Bl * Pt)) := by
  intro Ls
  induction Ls with
  | nil => intro xd; simp [comb1]
  | cons L Ls ih =>
    intro xd
    rw [List.length_cons, Finset.sum_range_succ', comb1, ih, unpackI]
    simp only [List.getD_cons_succ, List.getD_cons_zero, offB]
    ring

lemma comb2_spec (BD : ℕ) (Pt : ℤ) : ∀ (ps Ds : List ℕ), ps.length = Ds.length →
    comb2 BD Pt ps Ds
      = ∑ a ∈ Finset.range ps.length, (ps.getD a 0 : ℤ) * (((Ds.getD a 0 : ℕ) : ℤ) - offB BD * Pt) := by
  intro ps
  induction ps with
  | nil => intro Ds h; simp [comb2]
  | cons p ps ih =>
    intro Ds h
    cases Ds with
    | nil => simp at h
    | cons Dv Ds =>
      simp only [List.length_cons, add_left_inj] at h
      rw [List.length_cons, Finset.sum_range_succ', comb2, ih Ds h]
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      ring

lemma weights_length (w D : ℕ) (z : List (ℕ × ℕ × ℕ)) : (weights w D z).length = z.length := by
  simp [weights]

lemma getD_weights (w D : ℕ) (zs : List (ℕ × ℕ × ℕ)) (a : ℕ) (ha : a < zs.length) :
    (((weights w D zs).getD a 0 : ℕ) : ℤ) = kw w D zs a := by
  simp only [weights, kw, zt]
  rw [List.getD_eq_getElem _ _ ha, List.getD_eq_getElem _ _ (by simpa using ha)]
  simp

/-- The flat evaluator computes the Kronecker value of the quadratic form of a packed block. -/
lemma fqFlat_spec (w D : ℕ) (s : TBlk) (h : s.wf = true) :
    fqFlat w D s = (sqfF s.B s.z).kev w D := by
  simp only [TBlk.wf, Bool.and_eq_true, decide_eq_true_eq] at h
  have hz : s.z.length = s.r := h.2
  rw [kev_sqfF, sqfVal]
  have hpl : (weights w D s.z).length = s.r := by rw [weights_length, hz]
  have hLl := rowsN_length s.Bl s.r (weights w D s.z) s.r s.xl
  have hDl := rowsN_length s.BD s.r (weights w D s.z) s.r s.xD
  have hP : ∀ a < s.r, (((weights w D s.z).getD a 0 : ℕ) : ℤ) = kw w D s.z a :=
    fun a ha => getD_weights w D s.z a (by omega)
  unfold fqFlat
  rw [comb1_spec, comb2_spec _ _ _ _ (by rw [hpl, hDl]), hLl, hpl, hz]
  congr 1
  · refine Finset.sum_congr rfl fun q hq => ?_
    have hrow := rowsN_spec s.Bl s.r (weights w D s.z) hpl s.r s.xl q (Finset.mem_range.mp hq)
    have hsum : (∑ a ∈ Finset.range s.r, s.B.lq q a * kw w D s.z a)
        = (((rowsN s.Bl s.r (weights w D s.z) s.r s.xl).getD q 0 : ℕ) : ℤ)
          - offB s.Bl * (((weights w D s.z).sum : ℕ) : ℤ) := by
      rw [hrow]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [hP a (Finset.mem_range.mp ha)]
      rfl
    rw [hsum]
    simp only [TBlk.B, mkBlk, Blk.dq]
    ring
  · refine Finset.sum_congr rfl fun a ha => ?_
    have ha' := Finset.mem_range.mp ha
    have hrow := rowsN_spec s.BD s.r (weights w D s.z) hpl s.r s.xD a ha'
    have hsum : (∑ c ∈ Finset.range s.r, s.B.del a c * kw w D s.z c)
        = (((rowsN s.BD s.r (weights w D s.z) s.r s.xD).getD a 0 : ℕ) : ℤ)
          - offB s.BD * (((weights w D s.z).sum : ℕ) : ℤ) := by
      rw [hrow]
      refine Finset.sum_congr rfl fun c hc => ?_
      rw [hP c (Finset.mem_range.mp hc)]
      rfl
    rw [hP a ha', ← hsum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring

lemma fqCur_spec : ∀ w D s, s.wf = true → fqCur w D s = (sqfF s.B s.z).kev w D :=
  fun w D s h => fqFlat_spec w D s h

end Cert
end ThomsonN7

namespace ThomsonN7

open Kron Kron.Ex
namespace Cert

open ThreePoint
open scoped RealInnerProductSpace

/-! ## One-variable polynomials, marginals, kernel sums -/

lemma ev_h1E (h : List ℤ) (x y z : ℝ) :
    (h1E h).ev x y z = ∑ j ∈ Finset.range h.length, (h.getD j 0 : ℝ) * x ^ j := by
  simp only [h1E, ev_sumRange, ev_smulNZ, ev_mon, pow_zero, mul_one]

lemma ev_hvE (h : List ℤ) (i : ℕ) (u v t : ℝ) :
    (hvE h i).ev u v t
      = ∑ j ∈ Finset.range h.length, (h.getD j 0 : ℝ) * varVal u v t i ^ j := by
  rw [hvE, ev_sbst, ev_h1E]

lemma ev_gmE (S : Ex) (i : ℕ) (u v t : ℝ) :
    (gmE S i).ev u v t
      = S.ev 1 (varVal u v t i) (varVal u v t i) + S.ev (varVal u v t i) 1 (varVal u v t i)
        + S.ev (varVal u v t i) (varVal u v t i) 1 := by
  simp only [gmE, ev_add, ev_sbst]
  rfl

lemma vv0 (u v t : ℝ) : varVal u v t 0 = u := rfl
lemma vv1 (u v t : ℝ) : varVal u v t 1 = v := rfl
lemma vv2 (u v t : ℝ) : varVal u v t 2 = t := rfl
lemma vv3 (u v t : ℝ) : varVal u v t 3 = 1 := rfl

lemma Sk_fmat (K : ℕ) (m : ℕ → ℕ) (Lam : ℕ) (bl : ℕ → Blk) (a b c : ℝ) :
    Sk K m (fun k => fmat (m k) Lam (bl k)) a b c = (SE K m bl).ev a b c / Lam := by
  unfold Sk SE
  rw [ev_sumRange, Finset.sum_div]
  exact Finset.sum_congr rfl fun k _ => matDot_fmat_Y3 (m k) Lam (bl k) k a b c

/-! ## The three type slacks, scaled to integer polynomials -/

section RealSide

variable (K : ℕ) (m : ℕ → ℕ) (Lam : ℕ) (blP blR : ℕ → Blk)

lemma ev_lamAE (hL : 0 < Lam) (HA ψBa : List ℤ) (cal : ℤ) (u v t : ℝ) :
    (lamAE HA ψBa cal (SE K m blP) (SE K m blR)).ev u v t
      = 5 * Lam * lamA (Sk K m (fun k => fmat (m k) Lam (blP k)))
          (Sk K m (fun k => fmat (m k) Lam (blR k))) (polyR Lam HA) (polyR Lam ψBa)
          ((cal : ℝ) / Lam) u v t := by
  have hL' : (Lam : ℝ) ≠ 0 := by positivity
  simp only [lamAE, lamA, gm, polyR, Sk_fmat, ev_sub, ev_add, ev_smul, ev_c, ev_gmE, ev_sbst,
    ev_hvE, vv0, vv1, vv2]
  push_cast
  field_simp
  ring

lemma ev_lamBE (hL : 0 < Lam) (HB ψBa ψCb : List ℤ) (cbe : ℤ) (u v t : ℝ) :
    (lamBE HB ψBa ψCb cbe (SE K m blP) (SE K m blR)).ev u v t
      = 4 * Lam * lamB (Sk K m (fun k => fmat (m k) Lam (blP k)))
          (Sk K m (fun k => fmat (m k) Lam (blR k))) (polyR Lam HB) (polyR Lam ψBa)
          (polyR Lam ψCb) ((cbe : ℝ) / Lam) u v t := by
  have hL' : (Lam : ℝ) ≠ 0 := by positivity
  simp only [lamBE, lamB, gm, polyR, Sk_fmat, ev_sub, ev_add, ev_smul, ev_c, ev_gmE, ev_sbst,
    ev_hvE, vv0, vv1, vv2]
  push_cast
  field_simp
  ring

lemma ev_lamGE (hL : 0 < Lam) (HC ψCb : List ℤ) (e cal cbe : ℤ) (u v t : ℝ) :
    (lamGE HC ψCb e cal cbe (SE K m blP) (SE K m blR)).ev u v t
      = 30 * Lam * lamG (Sk K m (fun k => fmat (m k) Lam (blR k))) (polyR Lam HC)
          (polyR Lam ψCb)
          (((e : ℝ) / Lam + 2 * Sk K m (fun k => fmat (m k) Lam (blP k)) 1 1 1
            + 5 * Sk K m (fun k => fmat (m k) Lam (blR k)) 1 1 1 - 5 * ((cal : ℝ) / Lam)
            - 20 * ((cbe : ℝ) / Lam)) / 10) u v t := by
  have hL' : (Lam : ℝ) ≠ 0 := by positivity
  simp only [lamGE, tgE, lamG, gm, polyR, Sk_fmat, ev_sub, ev_add, ev_smul, ev_c, ev_gmE,
    ev_sbst, ev_hvE, vv0, vv1, vv2, vv3]
  push_cast
  field_simp
  ring

end RealSide

/-! ## The certificate -/

namespace TCert

variable (cf : TCert)

lemma idA_ev (h : cf.chkA = true) (u v t : ℝ) : cf.idA.ev u v t = 0 :=
  hybChk_sound fqCur fqCur_spec _ _ _ _ _ _ h u v t

lemma idB_ev (h : cf.chkB = true) (u v t : ℝ) : cf.idB.ev u v t = 0 :=
  hybChk_sound fqCur fqCur_spec _ _ _ _ _ _ h u v t

lemma idG_ev (h : cf.chkG = true) (u v t : ℝ) : cf.idG.ev u v t = 0 :=
  hybChk_sound fqCur fqCur_spec _ _ _ _ _ _ h u v t

lemma checkMeta_parts (h : cf.checkMeta = true) :
    0 < cf.Lam ∧ 0 < cf.ad ∧ 0 < cf.bd ∧ 0 < cf.mA ∧ 0 < cf.mB ∧ 0 < cf.mG ∧
    (∀ k < cf.K, (cf.blkP k).ok (cf.m k) = true) ∧
    (∀ k < cf.K, (cf.blkR k).ok (cf.m k) = true) ∧
    (cf.SA.all (fun s => okF s.z.length s.B) = true) ∧
    (cf.SB.all (fun s => okF s.z.length s.B) = true) ∧
    (cf.SG.all (fun s => okF s.z.length s.B) = true) := by
  simp only [checkMeta, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, fun k hk => ?_, fun k hk => ?_, h9, h10, h11⟩
  · exact (List.all_eq_true.mp h7) k (List.mem_range.mpr hk)
  · exact (List.all_eq_true.mp h8) k (List.mem_range.mpr hk)

/-! ### The real data of a certificate -/

lemma hFP (hm : cf.checkMeta = true) : ∀ k, k < cf.K → (cf.FPm k).PosSemidef :=
  fun k hk => fmat_psd cf.Lam ((cf.checkMeta_parts hm).2.2.2.2.2.2.1 k hk)

lemma hFR (hm : cf.checkMeta = true) : ∀ k, k < cf.K → (cf.FRm k).PosSemidef :=
  fun k hk => fmat_psd cf.Lam ((cf.checkMeta_parts hm).2.2.2.2.2.2.2.1 k hk)

lemma gramCut_of_le' (an : ℤ) (ad : ℕ) (hA : 0 < ad) {u v t : ℝ} (hg : GramOK u v t)
    (hu : (an : ℝ) / ad ≤ u) (hv : (an : ℝ) / ad ≤ v) (ht : (an : ℝ) / ad ≤ t) :
    GramCut an ad u v t := by
  have hp : (0 : ℝ) < ad := by exact_mod_cast hA
  refine ⟨hg, ?_, ?_, ?_⟩
  · rw [div_le_iff₀ hp] at hu; linarith
  · rw [div_le_iff₀ hp] at hv; linarith
  · rw [div_le_iff₀ hp] at ht; linarith

lemma nonneg_of_scaled {L A S : ℝ} (hL : 0 < L) (hS : 0 ≤ S) (h : L * A - S = 0) : 0 ≤ A := by
  by_contra hneg
  have := mul_neg_of_pos_of_neg hL (not_le.1 hneg)
  linarith

lemma le_one_of_gramOK {u v t : ℝ} (hg : GramOK u v t) : u ≤ 1 :=
  (abs_le.1 ((sq_le_one_iff_abs_le_one u).1 hg.1)).2

lemma alpha_nonneg (hm : cf.checkMeta = true) (hA : cf.chkA = true) {u v t : ℝ}
    (hg : GramOK u v t) (hu : cf.alo ≤ u) (hu' : u ≤ cf.ahi) (hv : cf.alo ≤ v)
    (ht : cf.alo ≤ t) :
    0 ≤ lamA (Sk cf.K cf.m cf.FPm) (Sk cf.K cf.m cf.FRm) cf.HAf cf.ψBaf cf.calf u v t := by
  obtain ⟨hL, hAd, hBd, hmA, -, -, -, -, hSA, -, -⟩ := cf.checkMeta_parts hm
  have hgc := gramCut_of_le' cf.an cf.ad hAd hg hu hv ht
  have hbd : (0 : ℝ) < cf.bd := by exact_mod_cast hBd
  have hb : (cf.bd : ℝ) * u ≤ cf.bn := by
    have := (le_div_iff₀ hbd).1 hu'
    linarith
  have h0 := cf.idA_ev hA u v t
  simp only [idA, idT, FA, ev_sub, ev_smul, ev_sumE, SPE, SRE,
    ev_lamAE cf.K cf.m cf.Lam cf.blkP cf.blkR hL] at h0
  push_cast at h0
  have hS := tsum_nonneg cf.an cf.ad cf.bn cf.bd cf.SA hSA hgc hb
  have hLr : (0 : ℝ) < cf.Lam := by exact_mod_cast hL
  have hmr : (0 : ℝ) < cf.mA := by exact_mod_cast hmA
  change 0 ≤ lamA (Sk cf.K cf.m (fun k => fmat (cf.m k) cf.Lam (cf.blkP k)))
    (Sk cf.K cf.m (fun k => fmat (cf.m k) cf.Lam (cf.blkR k))) (polyR cf.Lam cf.HA)
    (polyR cf.Lam cf.ψBa) ((cf.cal : ℝ) / cf.Lam) u v t
  refine nonneg_of_scaled (L := cf.mA * 5 * cf.Lam) (mul_pos (mul_pos hmr (by norm_num)) hLr)
    hS ?_
  linear_combination h0

lemma beta_nonneg (hm : cf.checkMeta = true) (hB : cf.chkB = true) {u v t : ℝ}
    (hg : GramOK u v t) (hu : cf.alo ≤ u) (hv : cf.alo ≤ v) (ht : cf.alo ≤ t) :
    0 ≤ lamB (Sk cf.K cf.m cf.FPm) (Sk cf.K cf.m cf.FRm) cf.HBf cf.ψBaf cf.ψCbf cf.cbef
      u v t := by
  obtain ⟨hL, hAd, -, -, hmB, -, -, -, -, hSB, -⟩ := cf.checkMeta_parts hm
  have hgc := gramCut_of_le' cf.an cf.ad hAd hg hu hv ht
  have hb : ((1 : ℕ) : ℝ) * u ≤ ((1 : ℤ) : ℝ) := by
    have := le_one_of_gramOK hg
    simpa using this
  have h0 := cf.idB_ev hB u v t
  simp only [idB, idT, FB, ev_sub, ev_smul, ev_sumE, SPE, SRE,
    ev_lamBE cf.K cf.m cf.Lam cf.blkP cf.blkR hL] at h0
  push_cast at h0
  have hS := tsum_nonneg cf.an cf.ad 1 1 cf.SB hSB hgc hb
  have hLr : (0 : ℝ) < cf.Lam := by exact_mod_cast hL
  have hmr : (0 : ℝ) < cf.mB := by exact_mod_cast hmB
  change 0 ≤ lamB (Sk cf.K cf.m (fun k => fmat (cf.m k) cf.Lam (cf.blkP k)))
    (Sk cf.K cf.m (fun k => fmat (cf.m k) cf.Lam (cf.blkR k))) (polyR cf.Lam cf.HB)
    (polyR cf.Lam cf.ψBa) (polyR cf.Lam cf.ψCb) ((cf.cbe : ℝ) / cf.Lam) u v t
  refine nonneg_of_scaled (L := cf.mB * 4 * cf.Lam) (mul_pos (mul_pos hmr (by norm_num)) hLr)
    hS ?_
  linear_combination h0

lemma gamma_nonneg (hm : cf.checkMeta = true) (hG : cf.chkG = true) {u v t : ℝ}
    (hg : GramOK u v t) (hu : cf.alo ≤ u) (hv : cf.alo ≤ v) (ht : cf.alo ≤ t) :
    0 ≤ lamG (Sk cf.K cf.m cf.FRm) cf.HCf cf.ψCbf
      ((cf.ef + 2 * Sk cf.K cf.m cf.FPm 1 1 1 + 5 * Sk cf.K cf.m cf.FRm 1 1 1 - 5 * cf.calf
        - 20 * cf.cbef) / 10) u v t := by
  obtain ⟨hL, hAd, -, -, -, hmG, -, -, -, -, hSG⟩ := cf.checkMeta_parts hm
  have hgc := gramCut_of_le' cf.an cf.ad hAd hg hu hv ht
  have hb : ((1 : ℕ) : ℝ) * u ≤ ((1 : ℤ) : ℝ) := by
    have := le_one_of_gramOK hg
    simpa using this
  have h0 := cf.idG_ev hG u v t
  simp only [idG, idT, FG, ev_sub, ev_smul, ev_sumE, SPE, SRE,
    ev_lamGE cf.K cf.m cf.Lam cf.blkP cf.blkR hL] at h0
  push_cast at h0
  have hS := tsum_nonneg cf.an cf.ad 1 1 cf.SG hSG hgc hb
  have hLr : (0 : ℝ) < cf.Lam := by exact_mod_cast hL
  have hmr : (0 : ℝ) < cf.mG := by exact_mod_cast hmG
  change 0 ≤ lamG (Sk cf.K cf.m (fun k => fmat (cf.m k) cf.Lam (cf.blkR k)))
    (polyR cf.Lam cf.HC) (polyR cf.Lam cf.ψCb)
    (((cf.e : ℝ) / cf.Lam + 2 * Sk cf.K cf.m (fun k => fmat (cf.m k) cf.Lam (cf.blkP k)) 1 1 1
      + 5 * Sk cf.K cf.m (fun k => fmat (cf.m k) cf.Lam (cf.blkR k)) 1 1 1
      - 5 * ((cf.cal : ℝ) / cf.Lam) - 20 * ((cf.cbe : ℝ) / cf.Lam)) / 10) u v t
  refine nonneg_of_scaled (L := cf.mG * 30 * cf.Lam) (mul_pos (mul_pos hmr (by norm_num)) hLr)
    hS ?_
  linear_combination h0

/-- **Soundness of a typed certificate with lower cut.** -/
theorem sound_lo (hm : cf.checkMeta = true) (hA : cf.chkA = true) (hB : cf.chkB = true)
    (hG : cf.chkG = true) (x : Fin 7 → R3) (hx : ∀ i, ‖x i‖ = 1)
    (hmin : ∀ i j, i ≠ j → cf.alo ≤ ⟪x i, x j⟫)
    (hcut : cf.alo ≤ ⟪x 0, x 1⟫ ∧ ⟪x 0, x 1⟫ ≤ cf.ahi) :
    cf.ef ≤ ∑ i, ∑ j ∈ Finset.Ioi i, H7 cf.HAf cf.HBf cf.HCf i j ⟪x i, x j⟫ :=
  typed7_bound_lo cf.K cf.m cf.FPm cf.FRm (cf.hFP hm) (cf.hFR hm) cf.HAf cf.HBf cf.HCf
    cf.ψBaf cf.ψCbf cf.ef cf.calf cf.cbef cf.alo cf.ahi cf.alo x hx hmin hcut
    (fun _ _ _ hg h1 h2 h3 h4 => cf.alpha_nonneg hm hA hg h1 h2 h3 h4)
    (fun _ _ _ hg h1 h2 h3 => cf.beta_nonneg hm hB hg h1 h2 h3)
    (fun _ _ _ hg h1 h2 h3 => cf.gamma_nonneg hm hG hg h1 h2 h3)

end TCert

end Cert
end ThomsonN7

end Asm_CertT

section Asm_SlabHead
/-!
# One-dimensional facts for the typed slab certificates: `H ≤ φ` on an interval

`φ(t) = (√(2 - 2t))⁻¹`.  For `t < 1` put `y = √((1 - t)/2) > 0`, so that `t = 1 - 2 y²` and
`φ(t) = 1/(2y)`.  A polynomial `H(t) = Q(t)/Lam` satisfies `H ≤ φ` iff `q(y) = Lam - 2 y Q(1 - 2y²) ≥ 0`.

A certificate for `q ≥ 0` on `{ν₂ y² ≤ μ₂}` (i.e. `t ≥ lo`) or `{ν₂ y² ≤ μ₂, μ₁ ≤ ν₁ y²}`
(i.e. `lo ≤ t ≤ hi`) is an exact polynomial identity

  `m · Lam · q(y) = Σ_T mult_T(y) · Σ (weight · square)`

where `mult_T` is a product of a subset of the atoms `y`, `μ₂ - ν₂ y²`, `ν₁ y² - μ₁`, and all
weights are natural numbers.  The identity is checked by kernel evaluation of integer polynomials.
-/

namespace ThomsonN7
namespace SlabOneD

/-! ## Fast check by evaluation at a large integer point (Kronecker substitution)

If an integer polynomial `R` satisfies `R(X) = 0` and all its coefficients have absolute value
`< X`, then `R = 0`.  The coefficient bound is obtained from `ℓ¹`-norm majorants along the same
expression tree as the identity, so the kernel only evaluates a few hundred big-integer operations
instead of expanding all polynomial products. -/

end SlabOneD
end ThomsonN7

end Asm_SlabHead

section Asm_Bridge
/-!
# Bridge: the certificate checker `Cert.TCert.sound_lo` feeds `Glue.SlabSpec` / `Glue.CapSpec`

`TCert.sound_lo` bounds `ef` by the typed double sum `∑ i<j, H7 HAf HBf HCf i j ⟪x i, x j⟫`.
Here we restate it with the class selector `Glue.cls3` (via `Glue3.sum_H7_eq_sum_cls3`) and, for a
certificate whose four boolean checks hold, produce the final interface of `Glue4`.  The remaining
inputs are the one-dimensional facts about the minorants (`HAf ≤ phi`, ...) and the numerical
comparison of `ef` with the energy `E(P)`.
-/

namespace ThomsonN7
namespace Glue

section Bridge

open scoped InnerProductSpace
open Base

/-- The bound of `TCert.sound_lo`, in the shape of the `cls3` sums, for minimal-pair
configurations in the slab `alo ≤ ⟪y 0, y 1⟫ ≤ ahi`. -/
theorem tcert_bound (cf : Cert.TCert) (hm : cf.checkMeta = true)
    (hA : cf.chkA = true) (hB : cf.chkB = true) (hG : cf.chkG = true) :
    ∀ y ∈ SphereConfig 7, cf.alo ≤ ⟪y 0, y 1⟫_ℝ → ⟪y 0, y 1⟫_ℝ ≤ cf.ahi →
      (∀ i j, i ≠ j → ⟪y 0, y 1⟫_ℝ ≤ ⟪y i, y j⟫_ℝ) →
      cf.ef ≤ ∑ i : Fin 7, ∑ j ∈ Finset.Ioi i, cls3 cf.HAf cf.HBf cf.HCf i j ⟪y i, y j⟫_ℝ := by
  intro y hy hlo hhi hmin
  rw [← sum_H7_eq_sum_cls3 cf.HAf cf.HBf cf.HCf (fun i j => ⟪y i, y j⟫_ℝ)]
  exact Cert.TCert.sound_lo cf hm hA hB hG y hy.1 (fun i j hij => hlo.trans (hmin i j hij))
    ⟨hlo, hhi⟩

/-- The bound of `TCert.sound_lo` for a cap certificate (`alo = -1`). -/
theorem tcert_bound_cap (cf : Cert.TCert) (hm : cf.checkMeta = true)
    (hA : cf.chkA = true) (hB : cf.chkB = true) (hG : cf.chkG = true)
    (halo : cf.alo = -1) :
    ∀ y ∈ SphereConfig 7, ⟪y 0, y 1⟫_ℝ ≤ cf.ahi →
      (∀ i j, i ≠ j → ⟪y 0, y 1⟫_ℝ ≤ ⟪y i, y j⟫_ℝ) →
      cf.ef ≤ ∑ i : Fin 7, ∑ j ∈ Finset.Ioi i, cls3 cf.HAf cf.HBf cf.HCf i j ⟪y i, y j⟫_ℝ := by
  intro y hy hhi hmin
  refine tcert_bound cf hm hA hB hG y hy ?_ hhi hmin
  rw [halo]
  exact neg_one_le_inner_of_unit (hy.1 0) (hy.1 1)

/-- **Cap specification from a certificate** (`alo = -1`, `ahi = a0`). -/
theorem capSpec_of_tcert (cf : Cert.TCert) (hm : cf.checkMeta = true)
    (hA : cf.chkA = true) (hB : cf.chkB = true) (hG : cf.chkG = true)
    (halo : cf.alo = -1) {δ τ : ℝ} (hτ : τ ≤ 1 / 165000)
    (hE : (144529774142213429350444915306029287904779 : ℝ) / 10 ^ 40 ≤ cf.ef + δ)
    (hHA : ∀ t, -1 ≤ t → t ≤ cf.ahi → cf.HAf t ≤ phi t ∧ (phi t - cf.HAf t ≤ δ → |t + 1| ≤ τ))
    (hHB : ∀ t, -1 ≤ t → t < 1 → cf.HBf t ≤ phi t ∧ (phi t - cf.HBf t ≤ δ → |t| ≤ τ))
    (hHC : ∀ t, -1 ≤ t → t < 1 →
      cf.HCf t ≤ phi t ∧ (phi t - cf.HCf t ≤ δ → |t - c1| ≤ τ ∨ |t - c2| ≤ τ)) :
    CapSpec cf.ahi :=
  ⟨cf.ef, δ, τ, cf.HAf, cf.HBf, cf.HCf, hτ, coulombEnergy_pent_le_of hE,
    tcert_bound_cap cf hm hA hB hG halo, hHA, hHB, hHC⟩

end Bridge

end Glue
end ThomsonN7

end Asm_Bridge

section Asm_Bridge1D
/-!
# Bridge1D: agent2's one-dimensional slab facts (`SlabOneD`) feed `Bridge`

`SlabOneD.peval Q t / Lam` is the polynomial `polyR Lam Q t` of `CertT`; a generated slab
`SlabOneD.Slab_x.HA_le_phi` therefore gives `HAf ≤ phi` on the slab of a certificate whose
`HA`, `Lam` are the data of `Slab_x.certHA`.
-/

namespace ThomsonN7
namespace Glue

section Bridge1D

open scoped InnerProductSpace
open Base

/-- `SlabOneD.peval` is the sum `∑ j, Q_j t^j`. -/
lemma peval_eq_sum (Q : List ℤ) (t : ℝ) :
    SlabOneD.peval Q t = ∑ j ∈ Finset.range Q.length, (Q.getD j 0 : ℝ) * t ^ j := by
  induction Q with
  | nil => simp [SlabOneD.peval]
  | cons a as ih =>
    rw [SlabOneD.peval, ih, List.length_cons, Finset.sum_range_succ', Finset.mul_sum]
    simp only [List.getD_cons_zero, List.getD_cons_succ, pow_zero, mul_one, pow_succ]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

/-- `polyR` is `peval / Lam`. -/
lemma polyR_eq_peval (Lam : ℕ) (Q : List ℤ) (t : ℝ) :
    Cert.polyR Lam Q t = SlabOneD.peval Q t / Lam := by
  rw [Cert.polyR, peval_eq_sum]

end Bridge1D

end Glue
end ThomsonN7

end Asm_Bridge1D

section Asm_Bridge2
/-!
# Bridge2: near-sharp cap specification from a certificate and its contact factorisations

`Bridge.capSpec_of_tcert` asks for coercive one-dimensional facts about the three minorants
`HAf, HBf, HCf` of a cap certificate.  `Coerce` produces exactly these facts from an exact
factorisation of `F = Dq - 2 y Q(1 - 2 y²)` at rational `y`-nodes (`ContactA`, `Contact1`,
`Contact2`).  Here the two are glued: the contact data are attached to a certificate `cf` by the
equalities `c.Q = cf.HX`, `c.Dq = cf.Lam`.
-/

namespace ThomsonN7
namespace Glue

section Bridge2

open scoped InnerProductSpace
open Base

/-- `SlabOneD.peval` and `CutOneD.peval` are the same Horner evaluation. -/
lemma slab_peval_eq_cut (Q : List ℤ) (t : ℝ) : SlabOneD.peval Q t = CutOneD.peval Q t := by
  induction Q with
  | nil => rfl
  | cons a as ih => simp only [SlabOneD.peval, CutOneD.peval, ih]

/-- `polyR` is `CutOneD.peval / Lam`. -/
lemma polyR_eq_cut (Lam : ℕ) (Q : List ℤ) (t : ℝ) :
    Cert.polyR Lam Q t = CutOneD.peval Q t / Lam := by
  rw [polyR_eq_peval, slab_peval_eq_cut]

/-- Rational lower bounds for `√5`. -/
lemma le_sqrt5_of {lo : ℝ} (h : lo ^ 2 ≤ 5) : lo ≤ √5 :=
  (le_abs_self lo).trans (Real.abs_le_sqrt h)

/-- Rational upper bounds for `√5`. -/
lemma sqrt5_le_of {hi : ℝ} (h0 : 0 ≤ hi) (h : 5 ≤ hi ^ 2) : √5 ≤ hi :=
  Real.sqrt_le_iff.2 ⟨h0, h⟩

/-- A rational node close to `c₁`, from rational bounds `lo ≤ √5 ≤ hi`. -/
lemma node_c1_of {tn ε lo hi : ℝ} (hlo : lo ^ 2 ≤ 5) (h0 : 0 ≤ hi) (hhi : 5 ≤ hi ^ 2)
    (h1 : 4 * tn + 1 - 4 * ε ≤ lo) (h2 : hi ≤ 4 * tn + 1 + 4 * ε) : |tn - c1| ≤ ε :=
  Coerce.abs_node_sub_c1_le (le_sqrt5_of hlo) (sqrt5_le_of h0 hhi) h1 h2

/-- A rational node close to `c₂`, from rational bounds `lo ≤ √5 ≤ hi`. -/
lemma node_c2_of {tn ε lo hi : ℝ} (hlo : lo ^ 2 ≤ 5) (h0 : 0 ≤ hi) (hhi : 5 ≤ hi ^ 2)
    (h1 : -4 * tn - 1 - 4 * ε ≤ lo) (h2 : hi ≤ -4 * tn - 1 + 4 * ε) : |tn - c2| ≤ ε :=
  Coerce.abs_node_sub_c2_le (le_sqrt5_of hlo) (sqrt5_le_of h0 hhi) h1 h2

end Bridge2

end Glue
end ThomsonN7

end Asm_Bridge2

section Asm_Bridge3
/-!
# Bridge3: near-sharp cap specification with relaxed contacts

Same as `Bridge2.capSpec_of_contacts`, but the pole--ring and ring--ring minorants come with the
*relaxed* factorisations `s F = (q y - p)² G + R` (`Coerce.Contact1R`, `Coerce.Contact2R`), which
integer SDP data can satisfy; the pole--pole minorant keeps the exact simple contact at `y = 1`.
-/

namespace ThomsonN7
namespace Glue

section Bridge3

open scoped InnerProductSpace
open Base

/-- **Cap specification from a certificate and relaxed contact factorisations.** -/
theorem capSpec_of_contactsR (cf : Cert.TCert) (hm : cf.checkMeta = true)
    (hA : cf.chkA = true) (hB : cf.chkB = true) (hG : cf.chkG = true)
    (halo : cf.alo = -1)
    (cA : Coerce.ContactA) (cB : Coerce.Contact1R) (cC : Coerce.Contact2R)
    (hcA : cA.check = true) (hcB : cB.check = true) (hcC : cC.check = true)
    (hQA : cA.Q = cf.HA) (hDA : cA.Dq = cf.Lam)
    (hQB : cB.Q = cf.HB) (hDB : cB.Dq = cf.Lam)
    (hQC : cC.Q = cf.HC) (hDC : cC.Dq = cf.Lam)
    {δ η τ ε1 ε2 : ℝ} (hτ : τ ≤ 1 / 165000)
    (hE : (144529774142213429350444915306029287904779 : ℝ) / 10 ^ 40 ≤ cf.ef + δ)
    (hη : 0 ≤ η)
    (hya : 0 ≤ (cA.ya1 : ℝ) / cA.ya2)
    (ha0 : ((cA.ya1 : ℝ) / cA.ya2) ^ 2 ≤ (1 - cf.ahi) / 2) (ha1 : cf.ahi < 1)
    (hδA : 8 * cA.Dq * δ ≤ ((cA.g0n : ℝ) / cA.g0d) * τ)
    (hδB : 2 * cB.s * cB.Dq * δ ≤ ((cB.g0n : ℝ) / cB.g0d) * (cB.q * η) ^ 2)
    (hτB : |1 - 2 * ((cB.p : ℝ) / cB.q) ^ 2| + 2 * η * (2 * ((cB.p : ℝ) / cB.q) + η) ≤ τ)
    (hδC : 2 * cC.s * cC.Dq * δ ≤ ((cC.g0n : ℝ) / cC.g0d) *
      (cC.q1 * cC.q2 * η * ((cC.p1 : ℝ) / cC.q1 - (cC.p2 : ℝ) / cC.q2) / 2) ^ 2)
    (hn1 : |1 - 2 * ((cC.p1 : ℝ) / cC.q1) ^ 2 - c1| ≤ ε1)
    (hn2 : |1 - 2 * ((cC.p2 : ℝ) / cC.q2) ^ 2 - c2| ≤ ε2)
    (hτ1 : ε1 + 2 * η * (2 * ((cC.p1 : ℝ) / cC.q1) + η) ≤ τ)
    (hτ2 : ε2 + 2 * η * (2 * ((cC.p2 : ℝ) / cC.q2) + η) ≤ τ) :
    CapSpec cf.ahi := by
  refine capSpec_of_tcert cf hm hA hB hG halo hτ hE ?_ ?_ ?_
  · intro t h1 h2
    have := Coerce.ContactA.hA cA hcA hya ha0 ha1 hδA t h1 h2
    rw [hQA, hDA] at this
    rwa [Cert.TCert.HAf, polyR_eq_cut]
  · intro t h1 h2
    have := Coerce.Contact1R.hB cB hcB hη hδB hτB t h1 h2
    rw [hQB, hDB] at this
    rwa [Cert.TCert.HBf, polyR_eq_cut]
  · intro t h1 h2
    have := Coerce.Contact2R.hC cC hcC hη hδC hn1 hn2 hτ1 hτ2 t h1 h2
    rw [hQC, hDC] at this
    rwa [Cert.TCert.HCf, polyR_eq_cut]

end Bridge3

end Glue
end ThomsonN7

end Asm_Bridge3

section Asm_cap_tc
namespace ThomsonN7
open Kron Kron.Ex
namespace Cert
open ThreePoint

theorem tc_cap_meta : tc_cap.checkMeta = true := by decide +kernel

theorem tc_cap_A : tc_cap.chkA = true := by decide +kernel

theorem tc_cap_B : tc_cap.chkB = true := by decide +kernel

theorem tc_cap_G : tc_cap.chkG = true := by decide +kernel

end Cert
end ThomsonN7

end Asm_cap_tc

section Asm_cap_ct
namespace ThomsonN7
namespace Final

theorem capA_check : capA.check = true := by decide +kernel

theorem capB_check : capB.check = true := by decide +kernel

theorem capC_check : capC.check = true := by decide +kernel

end Final
end ThomsonN7

end Asm_cap_ct

section Asm_cap_capspec
namespace ThomsonN7
namespace Final

/-- The near-sharp cap `⟪y 0, y 1⟫ ≤ -99/100` (certificate `cap`). -/
theorem capspec_cap : Glue.CapSpec (-99 / 100 : ℝ) := by
  have hbd : Cert.tc_cap.ahi = (-99 / 100 : ℝ) := by norm_num [Cert.TCert.ahi, Cert.tc_cap]
  rw [← hbd]
  refine Glue.capSpec_of_contactsR Cert.tc_cap Cert.tc_cap_meta Cert.tc_cap_A Cert.tc_cap_B Cert.tc_cap_G
    (by norm_num [Cert.TCert.alo, Cert.tc_cap]) capA capB capC capA_check capB_check capC_check
    rfl rfl rfl rfl rfl rfl (δ := (511168595372501 / 1000000000000000000000000000000 : ℝ)) (η := (1591 / 1000000000 : ℝ))
    (τ := (1 / 165000 : ℝ)) (ε1 := (2493602707684171662254911060859550477 / 4611686018427387904000000000000000000000000000000000 : ℝ)) (ε2 := (768508195246682507822694144076581 / 2882303761517117440000000000000000000000000000000 : ℝ))
    ?hτ ?hE ?hη ?hya ?ha0 ?ha1 ?hδA ?hδB ?hτB ?hδC ?hn1 ?hn2 ?hτ1 ?hτ2
  · norm_num
  · norm_num [Cert.TCert.ef, Cert.tc_cap]
  · norm_num
  · norm_num [capA]
  · rw [hbd]; norm_num [capA]
  · rw [hbd]; norm_num
  · norm_num [capA, Cert.tc_cap]
  · norm_num [capB, Cert.tc_cap]
  · norm_num [capB]
  · norm_num [capC, Cert.tc_cap]
  · exact Glue.node_c1_of (lo := (559016994374947424102293417182819 / 250000000000000000000000000000000 : ℝ)) (hi := (2236067977499789696409173668731277 / 1000000000000000000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [capC]) (by norm_num [capC])
  · exact Glue.node_c2_of (lo := (559016994374947424102293417182819 / 250000000000000000000000000000000 : ℝ)) (hi := (2236067977499789696409173668731277 / 1000000000000000000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [capC]) (by norm_num [capC])
  · norm_num [capC]
  · norm_num [capC]

end Final
end ThomsonN7

end Asm_cap_capspec

section Asm_s99_98_tc
namespace ThomsonN7
open Kron Kron.Ex
namespace Cert
open ThreePoint

end Cert
end ThomsonN7

end Asm_s99_98_tc

section Asm_s99_98_1d
namespace ThomsonN7
namespace SlabOneD

namespace Slab_s99_98

end Slab_s99_98

end SlabOneD
end ThomsonN7

end Asm_s99_98_1d

section Asm_s99_98_spec
namespace ThomsonN7
namespace Final

end Final
end ThomsonN7

end Asm_s99_98_spec

section Asm_s98_96_tc
namespace ThomsonN7
open Kron Kron.Ex
namespace Cert
open ThreePoint

end Cert
end ThomsonN7

end Asm_s98_96_tc

section Asm_s98_96_1d
namespace ThomsonN7
namespace SlabOneD

namespace Slab_s98_96

end Slab_s98_96

end SlabOneD
end ThomsonN7

end Asm_s98_96_1d

section Asm_s98_96_spec
namespace ThomsonN7
namespace Final

end Final
end ThomsonN7

end Asm_s98_96_spec

section Asm_s96_94_tc
namespace ThomsonN7
open Kron Kron.Ex
namespace Cert
open ThreePoint

end Cert
end ThomsonN7

end Asm_s96_94_tc

section Asm_s96_94_1d
namespace ThomsonN7
namespace SlabOneD

namespace Slab_s96_94

end Slab_s96_94

end SlabOneD
end ThomsonN7

end Asm_s96_94_1d

section Asm_s96_94_spec
namespace ThomsonN7
namespace Final

end Final
end ThomsonN7

end Asm_s96_94_spec

section Asm_s94_93_tc
namespace ThomsonN7
open Kron Kron.Ex
namespace Cert
open ThreePoint

end Cert
end ThomsonN7

end Asm_s94_93_tc

section Asm_s94_93_1d
namespace ThomsonN7
namespace SlabOneD

namespace Slab_s94_93

end Slab_s94_93

end SlabOneD
end ThomsonN7

end Asm_s94_93_1d

section Asm_s94_93_spec
namespace ThomsonN7
namespace Final

end Final
end ThomsonN7

end Asm_s94_93_spec

section Asm_s93_90_tc
namespace ThomsonN7
open Kron Kron.Ex
namespace Cert
open ThreePoint

end Cert
end ThomsonN7

end Asm_s93_90_tc

section Asm_s93_90_1d
namespace ThomsonN7
namespace SlabOneD

namespace Slab_s93_90

end Slab_s93_90

end SlabOneD
end ThomsonN7

end Asm_s93_90_1d

section Asm_s93_90_spec
namespace ThomsonN7
namespace Final

end Final
end ThomsonN7

end Asm_s93_90_spec

section Asm_Final
namespace ThomsonN7
namespace Final

end Final
end ThomsonN7

end Asm_Final

namespace ThomsonN7

end ThomsonN7


theorem solution : ThomsonN7.Glue.CapSpec (-99 / 100 : ℝ) := ThomsonN7.Final.capspec_cap
