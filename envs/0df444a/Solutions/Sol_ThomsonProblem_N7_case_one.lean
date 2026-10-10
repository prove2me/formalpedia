-- Prove2me | solution 1 for ThomsonProblem.N7.case_one
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-10-10T01:34:20.486581+00:00
-- url     : https://prove2.me/submissions/c08ea538-4d1c-4514-a926-550e6281a13f

import Mathlib
import Definitions.Def_ThomsonProblem_defs
import Definitions.Def_ThomsonN7_core
import Definitions.Def_ThomsonN7_case_one_data_2
import Definitions.Def_ThomsonN7_case_one_stats_1
import Definitions.Def_ThomsonN7_case_one_stats_2
import Definitions.Def_ThomsonN7_case_one_stats_3

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

lemma norm_sub_sq_of_unit {x y : R3} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ‖x - y‖ ^ 2 = 2 - 2 * inner ℝ x y := by
  rw [norm_sub_sq_real, hx, hy]; ring

lemma norm_sub_inv_eq_phi {x y : R3} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ‖x - y‖⁻¹ = phi (inner ℝ x y) := by
  unfold phi
  rw [← norm_sub_sq_of_unit hx hy, Real.sqrt_sq (norm_nonneg _)]

lemma inner_lt_one_of_ne {x y : R3} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hne : x ≠ y) :
    inner ℝ x y < 1 := by
  have h := norm_sub_sq_of_unit hx hy
  have : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  nlinarith

/-- For unit vectors the energy is a sum of `phi` of the pairwise inner products. -/
lemma coulombEnergy_eq_sum_phi {n : ℕ} {x : Fin n → R3} (hx : ∀ i, ‖x i‖ = 1) :
    coulombEnergy x = ∑ i, ∑ j ∈ Finset.Ioi i, phi (inner ℝ (x i) (x j)) := by
  unfold coulombEnergy
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    norm_sub_inv_eq_phi (hx i) (hx j)

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

theorem S3_swap12 (m k : ℕ) (u v t : ℝ) : S3 m k u v t = S3 m k v u t := by
  ext i j
  simp only [S3, Y3, Matrix.smul_apply, Matrix.add_apply, Matrix.of_apply, smul_eq_mul]
  ring

theorem S3_swap23 (m k : ℕ) (u v t : ℝ) : S3 m k u v t = S3 m k u t v := by
  ext i j
  simp only [S3, Y3, Matrix.smul_apply, Matrix.add_apply, Matrix.of_apply, smul_eq_mul]
  ring

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

/-- Relabelling lemmas for triple sums. -/
theorem tsum_swap12 {ι : Type*} [Fintype ι] (g : ι → ι → ι → ℝ) :
    ∑ i, ∑ j, ∑ l, g i j l = ∑ i, ∑ j, ∑ l, g j i l := by
  rw [Finset.sum_comm]

theorem tsum_swap23 {ι : Type*} [Fintype ι] (g : ι → ι → ι → ℝ) :
    ∑ i, ∑ j, ∑ l, g i j l = ∑ i, ∑ j, ∑ l, g i l j := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

/-- The symmetrised triple sum equals the unsymmetrised one. -/
theorem sum_S3_eq_sum_Y3 (m k : ℕ) {n : ℕ} (t : Fin n → Fin n → ℝ) (hsym : ∀ i j, t j i = t i j)
    (w : Fin m → ℝ) :
    ∑ i, ∑ j, ∑ l, w ⬝ᵥ (S3 m k (t i j) (t i l) (t j l)).mulVec w
      = ∑ i, ∑ j, ∑ l, w ⬝ᵥ (Y3 m k (t i j) (t i l) (t j l)).mulVec w := by
  set Φ : Fin n → Fin n → Fin n → ℝ :=
    fun i j l => w ⬝ᵥ (Y3 m k (t i j) (t i l) (t j l)).mulVec w with hΦ
  have expand : ∀ i j l, w ⬝ᵥ (S3 m k (t i j) (t i l) (t j l)).mulVec w
      = (1 / 6 : ℝ) * (Φ i j l + Φ j i l + Φ i l j + Φ l i j + Φ j l i + Φ l j i) := by
    intro i j l
    simp only [S3, Matrix.smul_mulVec, Matrix.add_mulVec, dotProduct_smul, dotProduct_add,
      smul_eq_mul, hΦ, hsym]
  have e1 : ∑ i, ∑ j, ∑ l, Φ j i l = ∑ i, ∑ j, ∑ l, Φ i j l := (tsum_swap12 Φ).symm
  have e2 : ∑ i, ∑ j, ∑ l, Φ i l j = ∑ i, ∑ j, ∑ l, Φ i j l := (tsum_swap23 Φ).symm
  have e3 : ∑ i, ∑ j, ∑ l, Φ l i j = ∑ i, ∑ j, ∑ l, Φ i j l := by
    rw [tsum_swap23 (fun i j l => Φ l i j)]; exact (tsum_swap12 Φ).symm
  have e4 : ∑ i, ∑ j, ∑ l, Φ j l i = ∑ i, ∑ j, ∑ l, Φ i j l := by
    rw [tsum_swap12 (fun i j l => Φ j l i)]; exact (tsum_swap23 Φ).symm
  have e5 : ∑ i, ∑ j, ∑ l, Φ l j i = ∑ i, ∑ j, ∑ l, Φ i j l := by
    rw [tsum_swap12 (fun i j l => Φ l j i), tsum_swap23 (fun i j l => Φ l i j)]
    exact (tsum_swap12 Φ).symm
  simp only [expand, ← Finset.mul_sum, Finset.sum_add_distrib, e1, e2, e3, e4, e5]
  ring

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

/-- **Bachoc–Vallentin positivity for `S²`.** For unit vectors `x i`, the moment matrix
`Σ_{i,j,l} S_k(⟨xᵢ,xⱼ⟩, ⟨xᵢ,x_l⟩, ⟨xⱼ,x_l⟩)` is positive semidefinite (as a quadratic form). -/
theorem bv_positivity (m k : ℕ) {n : ℕ} (x : Fin n → R3) (hx : ∀ i, ‖x i‖ = 1) (w : Fin m → ℝ) :
    0 ≤ ∑ i, ∑ j, ∑ l, w ⬝ᵥ (S3 m k ⟪x i, x j⟫ ⟪x i, x l⟫ ⟪x j, x l⟫).mulVec w := by
  have hsym : ∀ i j, ⟪x j, x i⟫ = ⟪x i, x j⟫ := fun i j => real_inner_comm _ _
  have e := sum_S3_eq_sum_Y3 m k (fun i j => ⟪x i, x j⟫) hsym w
  beta_reduce at e
  rw [e]
  refine Finset.sum_nonneg fun i _ => ?_
  obtain ⟨e₁, e₂, hfr⟩ := exists_tangent_frame (x i) (hx i)
  exact quad_Y3_nonneg m k (fun j => ⟪x i, x j⟫)
    (fun j l => ⟪x j, x l⟫) (fun j => ⟪e₁, x j⟫) (fun j => ⟪e₂, x j⟫)
    (fun j => (hfr (x j) (x j) (hx j) (hx j)).1)
    (fun j l => (hfr (x j) (x l) (hx j) (hx l)).2) w

/-- Pairing of a PSD matrix with the moment matrix is nonnegative. -/
theorem matDot_moment_nonneg (m k : ℕ) {n : ℕ} (x : Fin n → R3) (hx : ∀ i, ‖x i‖ = 1)
    (F : Matrix (Fin m) (Fin m) ℝ) (hF : F.PosSemidef) :
    0 ≤ ∑ i, ∑ j, ∑ l, matDot F (S3 m k ⟪x i, x j⟫ ⟪x i, x l⟫ ⟪x j, x l⟫) := by
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
    simp only [matDot, Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.star_apply, star_trivial,
      dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
    rw [key3 (fun a b s => v s a * v s b * M a b)]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun b _ => ?_
    ring
  have hswap : ∀ f : Fin n → Fin n → Fin n → Fin r → ℝ,
      ∑ i, ∑ j, ∑ l, ∑ s, f i j l s = ∑ s, ∑ i, ∑ j, ∑ l, f i j l s := by
    intro f
    calc ∑ i, ∑ j, ∑ l, ∑ s, f i j l s
        = ∑ i, ∑ j, ∑ s, ∑ l, f i j l s :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _ = ∑ i, ∑ s, ∑ j, ∑ l, f i j l s := Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ s, ∑ i, ∑ j, ∑ l, f i j l s := Finset.sum_comm
  simp only [hdot]
  rw [hswap]
  exact Finset.sum_nonneg fun s _ => bv_positivity m k x hx (v s)

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

theorem dsum_mul_left (c : ℝ) (f : Fin n → Fin n → Fin n → ℝ) :
    dsum (fun i j l => c * f i j l) = c * dsum f := by
  unfold dsum
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun l _ => ?_
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

theorem card_third (hn : 2 ≤ n) (i j : Fin n) (hij : i ≠ j) :
    (Finset.univ.filter fun l : Fin n => i ≠ j ∧ i ≠ l ∧ j ≠ l).card = n - 2 := by
  have h : (Finset.univ.filter fun l : Fin n => i ≠ j ∧ i ≠ l ∧ j ≠ l)
      = (Finset.univ.erase i).erase j := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq]
    constructor
    · rintro ⟨_, h2, h3⟩
      exact ⟨fun h => h3 h.symm, fun h => h2 h.symm, trivial⟩
    · rintro ⟨h3, h2, _⟩
      exact ⟨hij, fun h => h2 h.symm, fun h => h3 h.symm⟩
  rw [h, Finset.card_erase_of_mem (by simp [hij.symm]), Finset.card_erase_of_mem (Finset.mem_univ i)]
  simp only [Finset.card_univ, Fintype.card_fin]
  omega

theorem dsum_pair12 (hn : 2 ≤ n) (g : Fin n → Fin n → ℝ) :
    dsum (fun i j _ => g i j)
      = ((n : ℝ) - 2) * ∑ i, ∑ j, (if i ≠ j then g i j else 0) := by
  unfold dsum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hij : i = j
  · simp [hij]
  · rw [if_pos hij, ← Finset.sum_filter, Finset.sum_const, card_third hn i j hij, nsmul_eq_mul]
    push_cast [Nat.cast_sub hn]
    ring

theorem dsum_pair13 (hn : 2 ≤ n) (g : Fin n → Fin n → ℝ) :
    dsum (fun i _ l => g i l)
      = ((n : ℝ) - 2) * ∑ i, ∑ j, (if i ≠ j then g i j else 0) :=
  (dsum_swap23 (fun i j _ => g i j)).trans (dsum_pair12 hn g)

theorem dsum_pair23 (hn : 2 ≤ n) (g : Fin n → Fin n → ℝ) :
    dsum (fun _ j l => g j l)
      = ((n : ℝ) - 2) * ∑ i, ∑ j, (if i ≠ j then g i j else 0) :=
  (dsum_cyc (fun i j _ => g i j)).trans (dsum_pair12 hn g)

theorem dsum_const (hn : 2 ≤ n) (c : ℝ) :
    dsum (n := n) (fun _ _ _ => c) = c * ((n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2)) := by
  rw [dsum_pair12 hn (fun _ _ => c)]
  have h1 : ∀ i : Fin n, ∑ j : Fin n, (if i ≠ j then c else 0) = c * ((n : ℝ) - 1) := by
    intro i
    rw [← Finset.sum_filter, Finset.sum_const, Finset.filter_ne,
      Finset.card_erase_of_mem (Finset.mem_univ i), nsmul_eq_mul]
    simp only [Finset.card_univ, Fintype.card_fin]
    push_cast [Nat.cast_sub (show 1 ≤ n by omega)]
    ring
  simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

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

theorem dsum_Rs (hn : 3 ≤ n) (s : ℝ → ℝ → ℝ → ℝ)
    (hs12 : ∀ u v t, s u v t = s v u t) (hs23 : ∀ u v t, s u v t = s u t v)
    (τ : Fin n → Fin n → ℝ) (hsymm : ∀ i j, τ i j = τ j i) (hdiag : ∀ i, τ i i = 1) :
    dsum (fun i j l => Rs s n (τ i j) (τ i l) (τ j l))
      = ((n : ℝ) - 2) * ∑ i, ∑ j, ∑ l, s (τ i j) (τ i l) (τ j l) := by
  have hn2 : 2 ≤ n := by omega
  have hn1 : ((n : ℝ) - 1) ≠ 0 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    intro h
    linarith
  obtain ⟨g, hg⟩ : ∃ g : Fin n → Fin n → ℝ, ∀ i j, g i j = s (τ i j) (τ i j) 1 :=
    ⟨fun i j => s (τ i j) (τ i j) 1, fun _ _ => rfl⟩
  have hgd : ∀ i, g i i = s 1 1 1 := by intro i; rw [hg, hdiag]
  have hQ : ∑ i, ∑ j, (if i ≠ j then g i j else 0)
      = ∑ i, ∑ j, g i j - (n : ℝ) * s 1 1 1 := by
    simp only [sum_ne_eq_sub, hgd, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  have hall := sum_all_eq (n := n) (fun i j l => s (τ i j) (τ i l) (τ j l))
  have e1 : ∑ i, ∑ l, s (τ i i) (τ i l) (τ i l) = ∑ i, ∑ j, g i j := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    rw [hdiag i, hs12 1 (τ i l) (τ i l), hs23 (τ i l) 1 (τ i l), hg]
  have e2 : ∑ i, ∑ j, s (τ i j) (τ i i) (τ j i) = ∑ i, ∑ j, g i j := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hdiag i, hsymm j i, hs23 (τ i j) 1 (τ i j), hg]
  have e3 : ∑ i, ∑ j, s (τ i j) (τ i j) (τ j j) = ∑ i, ∑ j, g i j := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hdiag j, hg]
  have e4 : ∑ i, s (τ i i) (τ i i) (τ i i) = (n : ℝ) * s 1 1 1 := by
    simp only [hdiag, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hR : dsum (fun i j l => Rs s n (τ i j) (τ i l) (τ j l))
      = ((n : ℝ) - 2) * dsum (fun i j l => s (τ i j) (τ i l) (τ j l))
        + (dsum (fun i j _ => g i j) + dsum (fun i _ l => g i l) + dsum (fun _ j l => g j l))
        + dsum (n := n) (fun _ _ _ => s 1 1 1 / ((n : ℝ) - 1)) := by
    have hfun : (fun i j l => Rs s n (τ i j) (τ i l) (τ j l))
        = fun i j l => (((n : ℝ) - 2) * s (τ i j) (τ i l) (τ j l) + (g i j + g i l + g j l))
            + s 1 1 1 / ((n : ℝ) - 1) := by
      funext i j l
      simp only [Rs, hg]
    rw [hfun, dsum_add, dsum_add, dsum_mul_left, dsum_add, dsum_add]
  rw [hR, dsum_pair12 hn2, dsum_pair13 hn2, dsum_pair23 hn2, dsum_const hn2, hQ, hall, e1, e2, e3,
    e4]
  field_simp
  ring

theorem dsum_H (hn : 3 ≤ n) (H : ℝ → ℝ) (c : ℝ) (τ : Fin n → Fin n → ℝ)
    (hsymm : ∀ i j, τ i j = τ j i) :
    dsum (fun i j l => (H (τ i j) + H (τ i l) + H (τ j l)) / 3 - c)
      = 2 * ((n : ℝ) - 2) * ∑ i, ∑ j ∈ Finset.Ioi i, H (τ i j)
        - c * ((n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2)) := by
  have hn2 : 2 ≤ n := by omega
  have hfun : (fun i j l => (H (τ i j) + H (τ i l) + H (τ j l)) / 3 - c)
      = fun i j l => (1 / 3 : ℝ) * (H (τ i j) + H (τ i l) + H (τ j l)) - c := by
    funext i j l; ring
  rw [hfun, dsum_sub, dsum_mul_left, dsum_add, dsum_add,
    dsum_pair12 hn2 (fun i j => H (τ i j)), dsum_pair13 hn2 (fun i j => H (τ i j)),
    dsum_pair23 hn2 (fun i j => H (τ i j)), dsum_const hn2,
    sum_ne_eq_two_sum_Ioi (fun i j => H (τ i j)) (fun i j => by rw [hsymm])]
  ring

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

theorem matDot_add {m : ℕ} (F A B : Matrix (Fin m) (Fin m) ℝ) :
    matDot F (A + B) = matDot F A + matDot F B := by
  simp only [matDot, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem matDot_smul {m : ℕ} (F A : Matrix (Fin m) (Fin m) ℝ) (c : ℝ) :
    matDot F (c • A) = c * matDot F A := by
  simp only [matDot, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem matDot_Rk {m : ℕ} (F : Matrix (Fin m) (Fin m) ℝ) (n k : ℕ) (u v t : ℝ) :
    matDot F (Rk n m k u v t) = Rs (fun u v t => matDot F (S3 m k u v t)) n u v t := by
  simp only [Rk, Rs, matDot_add, matDot_smul]
  ring

theorem sum_matDot_Rk (K n : ℕ) (m : ℕ → ℕ)
    (F : (k : ℕ) → Matrix (Fin (m k)) (Fin (m k)) ℝ) (u v t : ℝ) :
    ∑ k ∈ Finset.range K, matDot (F k) (Rk n (m k) k u v t)
      = Rs (fun u v t => ∑ k ∈ Finset.range K, matDot (F k) (S3 (m k) k u v t)) n u v t := by
  simp only [matDot_Rk, Rs, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_div]

theorem sum4_swap {ι κ : Type*} [Fintype ι] (s : Finset κ) (f : ι → ι → ι → κ → ℝ) :
    ∑ i, ∑ j, ∑ l, ∑ k ∈ s, f i j l k = ∑ k ∈ s, ∑ i, ∑ j, ∑ l, f i j l k := by
  calc ∑ i, ∑ j, ∑ l, ∑ k ∈ s, f i j l k
      = ∑ i, ∑ j, ∑ k ∈ s, ∑ l, f i j l k :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ i, ∑ k ∈ s, ∑ j, ∑ l, f i j l k := Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ k ∈ s, ∑ i, ∑ j, ∑ l, f i j l k := Finset.sum_comm

/-- The exact three-point identity. -/
theorem three_point_identity (hn : 3 ≤ n) (s : ℝ → ℝ → ℝ → ℝ)
    (hs12 : ∀ u v t, s u v t = s v u t) (hs23 : ∀ u v t, s u v t = s u t v)
    (H : ℝ → ℝ) (e : ℝ) (x : Fin n → R3) (hx : ∀ i, ‖x i‖ = 1) :
    dsum (fun i j l => ((H ⟪x i, x j⟫ + H ⟪x i, x l⟫ + H ⟪x j, x l⟫) / 3
        - e / (n.choose 2 : ℝ)) - Rs s n ⟪x i, x j⟫ ⟪x i, x l⟫ ⟪x j, x l⟫)
      + ((n : ℝ) - 2) * ∑ i, ∑ j, ∑ l, s ⟪x i, x j⟫ ⟪x i, x l⟫ ⟪x j, x l⟫
    = 2 * ((n : ℝ) - 2) * (∑ i, ∑ j ∈ Finset.Ioi i, H ⟪x i, x j⟫ - e) := by
  have hsymm : ∀ i j, ⟪x i, x j⟫ = ⟪x j, x i⟫ := fun i j => (real_inner_comm _ _).symm
  have hdiag : ∀ i, ⟪x i, x i⟫ = 1 := fun i => by
    rw [real_inner_self_eq_norm_sq, hx i]; norm_num
  rw [dsum_sub, dsum_Rs hn s hs12 hs23 (fun i j => ⟪x i, x j⟫) hsymm hdiag,
    dsum_H hn H (e / (n.choose 2 : ℝ)) (fun i j => ⟪x i, x j⟫) hsymm]
  have hc : (n.choose 2 : ℝ) = n * (n - 1) / 2 := Nat.cast_choose_two ℝ n
  have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : ((n : ℝ) - 1) ≠ 0 := by intro h; linarith
  have hn0 : (n : ℝ) ≠ 0 := by intro h; linarith
  rw [hc]
  field_simp
  ring

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

lemma matDot_S3 {m : ℕ} (F : Matrix (Fin m) (Fin m) ℝ) (k : ℕ) (x y z : ℝ) :
    matDot F (S3 m k x y z) = (1 / 6) * six (fun a b c => matDot F (Y3 m k a b c)) x y z := by
  simp only [S3, matDot_smul, matDot_add, six]

lemma ev_sixE (i j k : ℕ) (e : Ex) (u v t : ℝ) :
    (sixE i j k e).ev u v t
      = six (fun a b c => e.ev a b c) (varVal u v t i) (varVal u v t j) (varVal u v t k) := by
  simp only [sixE, ev_add, ev_sbst, six]

lemma ev_ftotE (n K : ℕ) (fs : ℕ → Ex) (u v t : ℝ) :
    (ftotE n K fs).ev u v t
      = ∑ k ∈ Finset.range K, ftotTerm n (fun a b c => (fs k).ev a b c) u v t := by
  simp only [ftotE, ev_sumRange, ev_add, ev_smul, ev_sixE, ftotTerm, varVal]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  ring

lemma key_F {r Lam : ℕ} (b : Blk) (k n : ℕ) (hL : (Lam : ℝ) ≠ 0) (hn : (n : ℝ) - 1 ≠ 0)
    (u v t : ℝ) :
    6 * ((n : ℝ) - 1) * Lam * matDot (fmat r Lam b) (Rk n r k u v t)
      = ftotTerm n (fun a b' c => (fkE r b k).ev a b' c) u v t := by
  rw [matDot_Rk]
  simp only [Rs, matDot_S3, matDot_fmat_Y3, six, ftotTerm]
  field_simp

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

lemma gE_nonneg (an : ℤ) (ad : ℕ) (g : List ℕ) {u v t : ℝ} (h : GramCut an ad u v t) :
    0 ≤ (gE an ad g).ev u v t := by
  induction g with
  | nil => simp [gE]
  | cons code g ih =>
    simp only [gE, List.foldr_cons, ev_mul] at ih ⊢
    exact mul_nonneg (codeE_nonneg an ad code h) ih

lemma gramOK_swap12 {u v t : ℝ} (h : GramOK u v t) : GramOK v u t := by
  obtain ⟨hu, hv, ht, hd⟩ := h
  exact ⟨hv, hu, ht, by linarith⟩

lemma gramOK_swap23 {u v t : ℝ} (h : GramOK u v t) : GramOK u t v := by
  obtain ⟨hu, hv, ht, hd⟩ := h
  exact ⟨hu, ht, hv, by linarith⟩

lemma gramCut_swap12 {an : ℤ} {ad : ℕ} {u v t : ℝ} (h : GramCut an ad u v t) :
    GramCut an ad v u t :=
  ⟨gramOK_swap12 h.1, h.2.2.1, h.2.1, h.2.2.2⟩

lemma gramCut_swap23 {an : ℤ} {ad : ℕ} {u v t : ℝ} (h : GramCut an ad u v t) :
    GramCut an ad u t v :=
  ⟨gramOK_swap23 h.1, h.2.1, h.2.2.2, h.2.2.1⟩

lemma gramCut_perm3 (an : ℤ) (ad : ℕ) (s : ℕ) {u v t : ℝ} (h : GramCut an ad u v t) :
    GramCut an ad (varVal u v t (perm3 s).1) (varVal u v t (perm3 s).2.1)
      (varVal u v t (perm3 s).2.2) := by
  match s with
  | 0 => simpa [perm3, varVal] using h
  | 1 => simpa [perm3, varVal] using gramCut_swap23 h
  | 2 => simpa [perm3, varVal] using gramCut_swap12 h
  | 3 => simpa [perm3, varVal] using gramCut_swap23 (gramCut_swap12 h)
  | 4 => simpa [perm3, varVal] using gramCut_swap12 (gramCut_swap23 h)
  | s + 5 => simpa [perm3, varVal] using gramCut_swap12 (gramCut_swap23 (gramCut_swap12 h))

lemma sblkE_nonneg (an : ℤ) (ad : ℕ) {s : SBlk} (h : s.B.ok s.z.length = true) {u v t : ℝ}
    (hg : GramCut an ad u v t) : 0 ≤ (sblkE an ad s).ev u v t := by
  rw [sblkE, ev_sbst, ev_mul]
  exact mul_nonneg (gE_nonneg an ad s.g (gramCut_perm3 an ad s.σ hg)) (sqfE_nonneg h _ _ _)

/-! ## The certificate and its soundness -/

open scoped RealInnerProductSpace

lemma ev_hE (h : List ℤ) (u v t : ℝ) :
    (hE h).ev u v t
      = ∑ j ∈ Finset.range h.length, (h.getD j 0 : ℝ) * (u ^ j + v ^ j + t ^ j) := by
  simp only [hE, ev_sumRange, ev_smulNZ, ev_add, ev_mon, pow_zero, mul_one, one_mul]

namespace Cert3

end Cert3

lemma chk_sound {e : Ex} (h : chk e = true) (u v t : ℝ) : e.ev u v t = 0 := by
  have hk := of_decide_eq_true h
  refine Ex.ev_eq_zero_of_kev e (Nat.log2 e.l1 + 1) (max e.dx (max e.dy e.dz) + 1)
    ?_ ?_ ?_ ?_ hk u v t
  · omega
  · omega
  · omega
  · exact Nat.lt_log2_self

namespace Cert3

lemma check_parts {cf : Cert3} (h : cf.check = true) :
    3 ≤ cf.n ∧ 0 < cf.Lam ∧ 0 < cf.ad ∧ (∀ k < cf.K, (cf.blk k).ok (cf.m k) = true) ∧
    (cf.S.all (fun s => s.B.ok s.z.length) = true) ∧ chk cf.idE = true := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h2'⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, h2', fun k hk => ?_, h4, h5⟩
  exact (List.all_eq_true.mp h3) k (List.mem_range.mpr hk)

end Cert3

lemma sos_sum_nonneg (an : ℤ) (ad : ℕ) (S : List SBlk)
    (hS : S.all (fun s => s.B.ok s.z.length) = true) {u v t : ℝ} (hg : GramCut an ad u v t) :
    0 ≤ ((S.map (sblkE an ad)).map fun e => e.ev u v t).sum := by
  refine List.sum_nonneg fun x hx => ?_
  simp only [List.mem_map] at hx
  obtain ⟨e, ⟨s, hs, rfl⟩, rfl⟩ := hx
  exact sblkE_nonneg an ad (List.all_eq_true.mp hS s hs) hg

/-- The real-number algebra at the end of the soundness proof. -/
lemma final_ineq {n' C Λ Hs eps A Ssum : ℝ} (hn : 3 ≤ n') (hC : 0 < C) (hΛ : 0 < Λ)
    (hS : 0 ≤ Ssum)
    (hev : 2 * (n' - 1) * C * Hs - 6 * (n' - 1) * eps - C * (6 * (n' - 1) * Λ * A)
      - 6 * (n' - 1) * C * Ssum = 0) :
    A ≤ (Hs / Λ) / 3 - (eps / Λ) / C := by
  have h2 : 2 * (n' - 1) ≠ 0 := by
    have : 0 < 2 * (n' - 1) := by linarith
    exact this.ne'
  have hz : Hs * C - 3 * eps - 3 * Λ * C * A - 3 * C * Ssum = 0 := by
    refine mul_left_cancel₀ h2 ?_
    linear_combination hev
  have e : (Hs / Λ) / 3 - (eps / Λ) / C - A - Ssum / Λ
      = (Hs * C - 3 * eps - 3 * Λ * C * A - 3 * C * Ssum) / (3 * Λ * C) := by
    have hΛ' : Λ ≠ 0 := hΛ.ne'
    have hC' : C ≠ 0 := hC.ne'
    field_simp
  rw [hz, zero_div] at e
  have : 0 ≤ Ssum / Λ := div_nonneg hS hΛ.le
  linarith

namespace Cert3

lemma Hf_sum (cf : Cert3) (u v t : ℝ) :
    cf.Hf u + cf.Hf v + cf.Hf t
      = (∑ j ∈ Finset.range cf.h.length, (cf.h.getD j 0 : ℝ) * (u ^ j + v ^ j + t ^ j))
        / cf.Lam := by
  unfold Hf
  rw [← add_div, ← add_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The pointwise inequality on Gram triples of the cut. -/
lemma hpt_gramCut (cf : Cert3) (hc : cf.check = true) {u v t : ℝ} (hg : GramCut cf.an cf.ad u v t) :
    ∑ k ∈ Finset.range cf.K, matDot (cf.Fm k) (Rk cf.n (cf.m k) k u v t)
      ≤ (cf.Hf u + cf.Hf v + cf.Hf t) / 3 - ((cf.eps : ℝ) / cf.Lam) / (cf.n.choose 2 : ℕ) := by
  obtain ⟨hn, hL, hA, hF, hS, hz⟩ := check_parts hc
  have hev := chk_sound hz u v t
  simp only [idE, ev_sub, ev_smul, ev_c, ev_hE, ev_ftotE, ev_sumE] at hev
  have hnr : (3 : ℝ) ≤ cf.n := by exact_mod_cast hn
  have hn1 : (cf.n : ℝ) - 1 ≠ 0 := by
    have : (0 : ℝ) < (cf.n : ℝ) - 1 := by linarith
    exact this.ne'
  have hLpos : (0 : ℝ) < cf.Lam := by exact_mod_cast hL
  have hC : (0 : ℝ) < (cf.n.choose 2 : ℕ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hFp : ∑ k ∈ Finset.range cf.K,
        ftotTerm cf.n (fun a b c => (fkE (cf.m k) (cf.blk k) k).ev a b c) u v t
      = 6 * ((cf.n : ℝ) - 1) * cf.Lam
        * ∑ k ∈ Finset.range cf.K, matDot (cf.Fm k) (Rk cf.n (cf.m k) k u v t) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => (key_F (cf.blk k) k cf.n hLpos.ne' hn1 u v t).symm
  rw [hFp] at hev
  push_cast at hev
  rw [Hf_sum]
  exact final_ineq hnr hC hLpos (sos_sum_nonneg cf.an cf.ad cf.S hS hg) hev

lemma gramCut_of_le {cf : Cert3} (hA : 0 < cf.ad) {u v t : ℝ} (hg : GramOK u v t)
    (hu : (cf.an : ℝ) / cf.ad ≤ u) (hv : (cf.an : ℝ) / cf.ad ≤ v)
    (ht : (cf.an : ℝ) / cf.ad ≤ t) : GramCut cf.an cf.ad u v t := by
  have hp : (0 : ℝ) < cf.ad := by exact_mod_cast hA
  refine ⟨hg, ?_, ?_, ?_⟩
  · rw [div_le_iff₀ hp] at hu; linarith
  · rw [div_le_iff₀ hp] at hv; linarith
  · rw [div_le_iff₀ hp] at ht; linarith

/-- The pointwise inequality required by `three_point_bound_cut` (cut `a = an / ad`). -/
lemma hpt_cut (cf : Cert3) (hc : cf.check = true) {u v t : ℝ} (hg : GramOK u v t)
    (hu : (cf.an : ℝ) / cf.ad ≤ u) (hv : (cf.an : ℝ) / cf.ad ≤ v)
    (ht : (cf.an : ℝ) / cf.ad ≤ t) :
    ∑ k ∈ Finset.range cf.K, matDot (cf.Fm k) (Rk cf.n (cf.m k) k u v t)
      ≤ (cf.Hf u + cf.Hf v + cf.Hf t) / 3 - ((cf.eps : ℝ) / cf.Lam) / (cf.n.choose 2 : ℕ) :=
  hpt_gramCut cf hc (gramCut_of_le (check_parts hc).2.2.1 hg hu hv ht)

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

/-- **Three-point bound on a cut.**  As `three_point_bound`, but the pointwise inequality is only
required on Gram triples all of whose entries are `≥ a`, and the conclusion is only claimed for
configurations all of whose off-diagonal inner products are `≥ a`. -/
theorem three_point_bound_cut (hn : 3 ≤ n) (a : ℝ) (K : ℕ) (m : ℕ → ℕ)
    (F : (k : ℕ) → Matrix (Fin (m k)) (Fin (m k)) ℝ) (hF : ∀ k, k < K → (F k).PosSemidef)
    (H : ℝ → ℝ) (e : ℝ)
    (hpt : ∀ u v t : ℝ, GramOK u v t → a ≤ u → a ≤ v → a ≤ t →
      ∑ k ∈ Finset.range K, matDot (F k) (Rk n (m k) k u v t)
        ≤ (H u + H v + H t) / 3 - e / (n.choose 2 : ℝ))
    (x : Fin n → R3) (hx : ∀ i, ‖x i‖ = 1) (hxa : ∀ i j, i ≠ j → a ≤ ⟪x i, x j⟫) :
    e ≤ ∑ i, ∑ j ∈ Finset.Ioi i, H ⟪x i, x j⟫ := by
  set s : ℝ → ℝ → ℝ → ℝ := fun u v t => ∑ k ∈ Finset.range K, matDot (F k) (S3 (m k) k u v t)
    with hs
  have hs12 : ∀ u v t, s u v t = s v u t := fun u v t => by
    simp only [hs, S3_swap12 _ _ u v t]
  have hs23 : ∀ u v t, s u v t = s u t v := fun u v t => by
    simp only [hs, S3_swap23 _ _ u v t]
  have hid := three_point_identity hn s hs12 hs23 H e x hx
  have hBV : 0 ≤ ∑ i, ∑ j, ∑ l, s ⟪x i, x j⟫ ⟪x i, x l⟫ ⟪x j, x l⟫ := by
    simp only [hs]
    rw [sum4_swap]
    exact Finset.sum_nonneg fun k hk =>
      matDot_moment_nonneg (m k) k x hx (F k) (hF k (Finset.mem_range.mp hk))
  have hslack : 0 ≤ dsum (fun i j l => ((H ⟪x i, x j⟫ + H ⟪x i, x l⟫ + H ⟪x j, x l⟫) / 3
        - e / (n.choose 2 : ℝ)) - Rs s n ⟪x i, x j⟫ ⟪x i, x l⟫ ⟪x j, x l⟫) := by
    refine dsum_nonneg fun i j l hij hil hjl => ?_
    have := hpt _ _ _ (gramOK_inner (x i) (x j) (x l) (hx i) (hx j) (hx l))
      (hxa i j hij) (hxa i l hil) (hxa j l hjl)
    rw [sum_matDot_Rk] at this
    linarith
  have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < 2 * ((n : ℝ) - 2) := by linarith
  have hprod : 0 ≤ 2 * ((n : ℝ) - 2) * (∑ i, ∑ j ∈ Finset.Ioi i, H ⟪x i, x j⟫ - e) := by
    rw [← hid]
    have : 0 ≤ ((n : ℝ) - 2) * ∑ i, ∑ j, ∑ l, s ⟪x i, x j⟫ ⟪x i, x l⟫ ⟪x j, x l⟫ :=
      mul_nonneg (by linarith) hBV
    linarith
  have := nonneg_of_mul_nonneg_right hprod hpos
  linarith

end FinalCut

end ThreePoint

namespace TwoRegime

open scoped InnerProductSpace
open Base

/-- **Margin on the cut (Case 1).**  A cut three-point certificate and a one-dimensional
minorant `H ≤ φ` on `[a, 1)` give `E(y) ≥ E(P) + η` for every configuration all of whose
off-diagonal inner products are `≥ a`. -/
theorem margin_of_threePoint_cut {H : ℝ → ℝ} {a η : ℝ} (K : ℕ) (m : ℕ → ℕ)
    (F : (k : ℕ) → Matrix (Fin (m k)) (Fin (m k)) ℝ) (hF : ∀ k, k < K → (F k).PosSemidef)
    (hpt : ∀ u v t : ℝ, ThreePoint.GramOK u v t → a ≤ u → a ≤ v → a ≤ t →
      ∑ k ∈ Finset.range K, ThreePoint.matDot (F k) (ThreePoint.Rk 7 (m k) k u v t)
        ≤ (H u + H v + H t) / 3 - (coulombEnergy pentBipyramid + η) / ((Nat.choose 7 2 : ℕ) : ℝ))
    (hH : ∀ t : ℝ, a ≤ t → t < 1 → H t ≤ phi t) :
    ∀ y ∈ SphereConfig 7, (∀ i j, i ≠ j → a ≤ ⟪y i, y j⟫_ℝ) →
      coulombEnergy pentBipyramid + η ≤ coulombEnergy y := by
  intro y hy hya
  have h1 : coulombEnergy y = ∑ i, ∑ j ∈ Finset.Ioi i, phi ⟪y i, y j⟫_ℝ :=
    coulombEnergy_eq_sum_phi hy.1
  have h2 : ∑ i, ∑ j ∈ Finset.Ioi i, H ⟪y i, y j⟫_ℝ ≤ ∑ i, ∑ j ∈ Finset.Ioi i, phi ⟪y i, y j⟫_ℝ := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj => ?_
    have hij : i ≠ j := (Finset.mem_Ioi.1 hj).ne
    exact hH _ (hya i j hij) (inner_lt_one_of_ne (hy.1 i) (hy.1 j) (fun h => hij (hy.2 h)))
  have h4 := ThreePoint.three_point_bound_cut (by norm_num) a K m F hF H
    (coulombEnergy pentBipyramid + η) hpt y hy.1 hya
  linarith

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

/-- Rational enclosure of `sin (π/5)` and `√5`, `√2`. -/
lemma sqrt2_bounds : 1414213562 / 1000000000 ≤ √2 ∧ √2 ≤ 1414213563 / 1000000000 := by
  constructor
  · exact (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
  · exact Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩

lemma sqrt5_bounds : 2236067977 / 1000000000 ≤ √5 ∧ √5 ≤ 2236067978 / 1000000000 := by
  constructor
  · exact (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
  · exact Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩

lemma sin_pi_div_five_sq : sin (π / 5) ^ 2 = (5 - √5) / 8 := by
  have h := sin_sq_add_cos_sq (π / 5)
  rw [cos_pi_div_five] at h
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith

lemma sin_pi_div_five_bounds :
    587785252 / 1000000000 ≤ sin (π / 5) ∧ sin (π / 5) ≤ 587785253 / 1000000000 := by
  have hpos : 0 < sin (π / 5) := sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [pi_pos])
  have hsq := sin_pi_div_five_sq
  obtain ⟨h5l, h5u⟩ := sqrt5_bounds
  constructor
  · by_contra hlt
    push Not at hlt
    nlinarith
  · by_contra hlt
    push Not at hlt
    nlinarith

lemma sin_two_pi_div_five : sin (2 * π / 5) = sin (π / 5) * ((1 + √5) / 2) := by
  have : 2 * π / 5 = 2 * (π / 5) := by ring
  rw [this, sin_two_mul, cos_pi_div_five]
  ring

lemma pent_formula_bounds :
    14452977 / 1000000 ≤ 1 / 2 + 5 * √2 + 5 / (2 * sin (π / 5)) + 5 / (2 * sin (2 * π / 5)) ∧
    1 / 2 + 5 * √2 + 5 / (2 * sin (π / 5)) + 5 / (2 * sin (2 * π / 5)) ≤ 14452978 / 1000000 := by
  obtain ⟨h2l, h2u⟩ := sqrt2_bounds
  obtain ⟨h5l, h5u⟩ := sqrt5_bounds
  obtain ⟨hal, hau⟩ := sin_pi_div_five_bounds
  have hpos : 0 < sin (π / 5) := by linarith
  rw [sin_two_pi_div_five]
  have h1 : 5 / (2 * sin (π / 5)) ≤ 5 / (2 * (587785252 / 1000000000)) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have h1' : 5 / (2 * (587785253 / 1000000000)) ≤ 5 / (2 * sin (π / 5)) :=
    div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  have hb : 0 < sin (π / 5) * ((1 + √5) / 2) := by
    have : 0 < √5 := Real.sqrt_pos.2 (by norm_num)
    positivity
  have hbl : (587785252 / 1000000000) * ((1 + 2236067977 / 1000000000) / 2)
      ≤ sin (π / 5) * ((1 + √5) / 2) := by
    apply mul_le_mul hal (by linarith) (by norm_num) (by linarith)
  have hbu : sin (π / 5) * ((1 + √5) / 2)
      ≤ (587785253 / 1000000000) * ((1 + 2236067978 / 1000000000) / 2) := by
    apply mul_le_mul hau (by linarith) (by linarith) (by norm_num)
  have h2 : 5 / (2 * (sin (π / 5) * ((1 + √5) / 2))) ≤
      5 / (2 * ((587785252 / 1000000000) * ((1 + 2236067977 / 1000000000) / 2))) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  have h2' : 5 / (2 * ((587785253 / 1000000000) * ((1 + 2236067978 / 1000000000) / 2))) ≤
      5 / (2 * (sin (π / 5) * ((1 + √5) / 2))) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  constructor
  · norm_num at h1' h2' ⊢; linarith
  · norm_num at h1 h2 ⊢; linarith

/-- **Rational enclosure of the minimum energy**: `14.452977 ≤ E(P) ≤ 14.452978`. -/
lemma coulombEnergy_pent_bounds :
    14452977 / 1000000 ≤ coulombEnergy pentBipyramid ∧
    coulombEnergy pentBipyramid ≤ 14452978 / 1000000 := by
  rw [pentBipyramid_energy]
  exact pent_formula_bounds

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

theorem peval_sqSum (L : List (ℕ × List ℤ)) (y : ℝ) : peval (sqSum L) y = sqEval L y := by
  induction L with
  | nil => simp [sqSum, peval, sqEval]
  | cons x rs ih =>
    obtain ⟨d, r⟩ := x
    simp only [sqSum, peval_padd, peval_pscale, peval_pmul, ih, sqEval, List.map_cons, List.sum_cons]
    push_cast; ring

theorem sqEval_nonneg (L : List (ℕ × List ℤ)) (y : ℝ) : 0 ≤ sqEval L y := by
  unfold sqEval
  refine List.sum_nonneg ?_
  intro z hz
  obtain ⟨x, _, rfl⟩ := List.mem_map.1 hz
  positivity

theorem peval_eq_zero_of_all (p : List ℤ) (h : p.all (· == 0) = true) (y : ℝ) : peval p y = 0 := by
  induction p with
  | nil => simp [peval]
  | cons a as ih =>
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    simp only [peval, h.1, ih h.2]; simp

theorem Cert.nonneg (mu nu : ℤ) (c : Cert) (hc : c.check mu nu = true) (y : ℝ) (h0 : 0 ≤ y)
    (h1 : (nu : ℝ) * y ^ 2 ≤ mu) :
    0 ≤ (c.Lam : ℝ) - 2 * y * peval c.Q (1 - 2 * y ^ 2) := by
  simp only [Cert.check, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨-, hz⟩ := hc
  have h := peval_eq_zero_of_all _ hz y
  simp only [Cert.diff, peval_padd, peval_pneg, peval_pmul, peval_compQ,
    peval_sqSum, peval] at h
  have hA0 := sqEval_nonneg c.A0 y
  have hA1 := mul_nonneg h0 (sqEval_nonneg c.A1 y)
  have hA2 := mul_nonneg (sub_nonneg.2 h1) (sqEval_nonneg c.A2 y)
  have hA3 := mul_nonneg (mul_nonneg h0 (sub_nonneg.2 h1)) (sqEval_nonneg c.A3 y)
  push_cast at h
  nlinarith [hA0, hA1, hA2, hA3]

/-- **Soundness**: a passing certificate gives `Q(t) / Lam ≤ (√(2 - 2t))⁻¹` for `t < 1` with
`ν (1 - t) ≤ 2 μ`. -/
theorem Cert.sound (mu nu : ℤ) (c : Cert) (hc : c.check mu nu = true) {t : ℝ}
    (h1 : (nu : ℝ) * (1 - t) ≤ 2 * mu) (h2 : t < 1) :
    peval c.Q t / c.Lam ≤ (Real.sqrt (2 - 2 * t))⁻¹ := by
  have hD : (0 : ℝ) < c.Lam := by
    simp only [Cert.check, Bool.and_eq_true, decide_eq_true_eq] at hc
    exact_mod_cast hc.1
  have hpos : 0 < 2 - 2 * t := by linarith
  set s := Real.sqrt (2 - 2 * t) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hpos
  have hss : s ^ 2 = 2 - 2 * t := Real.sq_sqrt hpos.le
  have hy2 : (s / 2) ^ 2 = (1 - t) / 2 := by rw [div_pow, hss]; ring
  have hy : (nu : ℝ) * (s / 2) ^ 2 ≤ mu := by rw [hy2]; linarith
  have h0 := c.nonneg mu nu hc (s / 2) (by positivity) hy
  have e1 : 1 - 2 * (s / 2) ^ 2 = t := by nlinarith
  rw [e1] at h0
  rw [div_le_iff₀ hD, ← one_div, div_mul_eq_mul_div, le_div_iff₀ hs0]
  nlinarith

/-- `peval` as a finite sum. -/
theorem peval_eq_sum (Q : List ℤ) (x : ℝ) :
    peval Q x = ∑ j ∈ Finset.range Q.length, (Q.getD j 0 : ℝ) * x ^ j := by
  induction Q with
  | nil => simp [peval]
  | cons a as ih =>
    rw [List.length_cons, Finset.sum_range_succ', peval, ih, Finset.mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

/-- The certificate passes the exact check. -/
theorem cutCert_ok : cutCert.check 19 20 = true := by decide +kernel

/-- **`H ≤ φ` on the cut.**  The degree-10 minorant `H(t) = Q(t) / Lam` satisfies `H(t) ≤ φ(t)` for
`-9/10 ≤ t < 1`. -/
theorem cutH_le_phi {t : ℝ} (h1 : (-9 / 10 : ℝ) ≤ t) (h2 : t < 1) :
    peval cutCert.Q t / cutCert.Lam ≤ (Real.sqrt (2 - 2 * t))⁻¹ :=
  Cert.sound 19 20 cutCert cutCert_ok (by push_cast; linarith) h2

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

/-- `c1Stat` computes the four statistics `l1`, `dx`, `dy`, `dz` and the Kronecker value `kev`. -/
lemma c1Stat_eq (w D : ℕ) (e : Kron.Ex) :
    c1Stat w D e = (e.l1, e.dx, e.dy, e.dz, e.kev w D) := by
  induction e with
  | c n => rfl
  | mon a b d => rfl
  | add p q ihp ihq => simp only [c1Stat, ihp, ihq, c1Add, Kron.Ex.l1, Kron.Ex.dx, Kron.Ex.dy,
      Kron.Ex.dz, Kron.Ex.kev]
  | mul p q ihp ihq => simp only [c1Stat, ihp, ihq, c1Mul, Kron.Ex.l1, Kron.Ex.dx, Kron.Ex.dy,
      Kron.Ex.dz, Kron.Ex.kev]

lemma c1Stat_sub (w D : ℕ) (a b : Kron.Ex) :
    c1Stat w D (Kron.Ex.sub a b) = c1Sub (c1Stat w D a) (c1Stat w D b) := rfl

lemma c1Stat_smul (w D : ℕ) (a : ℤ) (e : Kron.Ex) :
    c1Stat w D (Kron.Ex.smul a e) = c1Smul a (c1Stat w D e) := rfl

lemma c1Stat_c (w D : ℕ) (a : ℤ) : c1Stat w D (Kron.Ex.c a) = c1C a := rfl

lemma c1Stat_sumE (w D : ℕ) : ∀ l : List Kron.Ex,
    c1Stat w D (Kron.Ex.sumE l) = c1Sum (l.map (c1Stat w D))
  | [] => rfl
  | x :: l => by
    have ih := c1Stat_sumE w D l
    show c1Add (c1Stat w D x) (c1Stat w D (Kron.Ex.sumE l)) = _
    rw [ih]
    rfl

lemma c1Stat_sumRange (w D r : ℕ) (f : ℕ → Kron.Ex) :
    c1Stat w D (Kron.Ex.sumRange r f)
      = c1Sum ((List.range r).map fun k => c1Stat w D (f k)) := by
  rw [Kron.Ex.sumRange, c1Stat_sumE, List.map_map]
  rfl

lemma c1_ftotE_eq (n K : ℕ) (fs : ℕ → Kron.Ex) :
    ftotE n K fs = Kron.Ex.sumRange K fun k => c1FtotK n (fs k) := rfl

/-- The statistics of the identity expression, in terms of the statistics of its pieces. -/
lemma c1Stat_idE (cf : Cert3) (w D : ℕ) :
    c1Stat w D cf.idE =
      c1Sub (c1Sub (c1Sub
        (c1Smul (2 * ((cf.n : ℤ) - 1) * (cf.n.choose 2 : ℕ)) (c1Stat w D (hE cf.h)))
        (c1C (6 * ((cf.n : ℤ) - 1) * cf.eps)))
        (c1Smul (cf.n.choose 2 : ℕ) (c1Sum ((List.range cf.K).map fun k =>
          c1Stat w D (c1FtotK cf.n (fkE (cf.m k) (cf.blk k) k))))))
        (c1Smul (6 * ((cf.n : ℤ) - 1) * (cf.n.choose 2 : ℕ))
          (c1Sum (cf.S.map fun s => c1Stat w D (sblkE cf.an cf.ad s)))) := by
  simp only [Cert3.idE, c1Stat_sub, c1Stat_smul, c1Stat_c, c1_ftotE_eq, c1Stat_sumRange,
    c1Stat_sumE, List.map_map]
  rfl

/-! The 13 pieces, each evaluated in its own declaration (`w = 179`, `D = 11`). -/
theorem c1_stat_H :
    c1Stat 179 11 (hE Case1Data.cf.h) = ThomsonN7.Case1Stats.val_H := by
  decide +kernel
theorem c1_stat_F0 :
    c1Stat 179 11 (c1FtotK Case1Data.cf.n (fkE (Case1Data.cf.m 0) (Case1Data.cf.blk 0) 0)) = ThomsonN7.Case1Stats.val_F0 := by
  decide +kernel
theorem c1_stat_F1 :
    c1Stat 179 11 (c1FtotK Case1Data.cf.n (fkE (Case1Data.cf.m 1) (Case1Data.cf.blk 1) 1)) = ThomsonN7.Case1Stats.val_F1 := by
  decide +kernel
theorem c1_stat_F2 :
    c1Stat 179 11 (c1FtotK Case1Data.cf.n (fkE (Case1Data.cf.m 2) (Case1Data.cf.blk 2) 2)) = ThomsonN7.Case1Stats.val_F2 := by
  decide +kernel
theorem c1_stat_F3 :
    c1Stat 179 11 (c1FtotK Case1Data.cf.n (fkE (Case1Data.cf.m 3) (Case1Data.cf.blk 3) 3)) = ThomsonN7.Case1Stats.val_F3 := by
  decide +kernel
theorem c1_stat_S0 :
    c1Stat 179 11 (sblkE Case1Data.cf.an Case1Data.cf.ad Case1Data.S0) = ThomsonN7.Case1Stats.val_S0 := by
  decide +kernel
theorem c1_stat_S1 :
    c1Stat 179 11 (sblkE Case1Data.cf.an Case1Data.cf.ad Case1Data.S1) = ThomsonN7.Case1Stats.val_S1 := by
  decide +kernel
theorem c1_stat_S2 :
    c1Stat 179 11 (sblkE Case1Data.cf.an Case1Data.cf.ad Case1Data.S2) = ThomsonN7.Case1Stats.val_S2 := by
  decide +kernel
theorem c1_stat_S3 :
    c1Stat 179 11 (sblkE Case1Data.cf.an Case1Data.cf.ad Case1Data.S3) = ThomsonN7.Case1Stats.val_S3 := by
  decide +kernel
theorem c1_stat_S4 :
    c1Stat 179 11 (sblkE Case1Data.cf.an Case1Data.cf.ad Case1Data.S4) = ThomsonN7.Case1Stats.val_S4 := by
  decide +kernel
theorem c1_stat_S5 :
    c1Stat 179 11 (sblkE Case1Data.cf.an Case1Data.cf.ad Case1Data.S5) = ThomsonN7.Case1Stats.val_S5 := by
  decide +kernel
theorem c1_stat_S6 :
    c1Stat 179 11 (sblkE Case1Data.cf.an Case1Data.cf.ad Case1Data.S6) = ThomsonN7.Case1Stats.val_S6 := by
  decide +kernel
theorem c1_stat_S7 :
    c1Stat 179 11 (sblkE Case1Data.cf.an Case1Data.cf.ad Case1Data.S7) = ThomsonN7.Case1Stats.val_S7 := by
  decide +kernel

theorem c1_K : Case1Data.cf.K = 4 := rfl

theorem c1_S : Case1Data.cf.S = [Case1Data.S0, Case1Data.S1, Case1Data.S2, Case1Data.S3,
    Case1Data.S4, Case1Data.S5, Case1Data.S6, Case1Data.S7] := rfl

theorem c1_range4 : List.range 4 = [0, 1, 2, 3] := rfl

/-- The statistics of the whole identity expression: `ℓ¹`-norm below `2 ^ 179`, all three degrees
`10`, Kronecker value `0`. -/
theorem c1_idE_stat : c1Stat 179 11 Case1Data.cf.idE = (436332295499381438821328134325189273208925017963848688, 10, 10, 10, (0 : Int)) := by
  rw [c1Stat_idE, c1_K, c1_S, c1_range4]
  simp only [List.map_cons, List.map_nil]
  rw [c1_stat_H, c1_stat_F0, c1_stat_F1, c1_stat_F2, c1_stat_F3, c1_stat_S0, c1_stat_S1,
    c1_stat_S2, c1_stat_S3, c1_stat_S4, c1_stat_S5, c1_stat_S6, c1_stat_S7]
  decide +kernel

/-- The Kronecker check of the identity expression. -/
theorem cf_chk : chk Case1Data.cf.idE = true := by
  have h := c1Stat_eq 179 11 Case1Data.cf.idE
  rw [c1_idE_stat] at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨hl, hx, hy, hz, hk⟩ := h
  unfold chk
  rw [← hl, ← hx, ← hy, ← hz]
  have hW : Nat.log2 436332295499381438821328134325189273208925017963848688 + 1 = 179 := by decide +kernel
  have hD : max 10 (max 10 10) + 1 = 11 := by decide +kernel
  rw [hW, hD]
  exact decide_eq_true hk.symm

/-- The positive-semidefiniteness certificates of the `F`-blocks. -/
theorem cf_blocks :
    (List.range Case1Data.cf.K).all (fun k => (Case1Data.cf.blk k).ok (Case1Data.cf.m k)) = true := by
  decide +kernel

/-- The positive-semidefiniteness certificates of the `S`-blocks. -/
theorem cf_sos : Case1Data.cf.S.all (fun s => s.B.ok s.z.length) = true := by
  decide +kernel

/-- The packed cut certificate passes the exact Kronecker check (checked in 17 separate kernel
calls, see the comment above). -/
theorem cf_ok : Case1Data.cf.check = true := by
  unfold Cert3.check
  rw [cf_chk, cf_blocks, cf_sos]
  decide +kernel

/-- The polynomial of the packed three-point certificate is the polynomial of the
one-dimensional minorant certificate. -/
theorem h_eq : Case1Data.cf.h = CutOneD.cutCert.Q := by decide +kernel

/-- The denominators agree. -/
theorem lam_eq : Case1Data.cf.Lam = CutOneD.cutCert.Lam := by decide +kernel

/-- `Hf` is the polynomial `Q / Lam` of the one-dimensional certificate. -/
theorem Hf_eq (t : ℝ) :
    Case1Data.cf.Hf t = CutOneD.peval CutOneD.cutCert.Q t / (CutOneD.cutCert.Lam : ℝ) := by
  unfold Cert3.Hf
  rw [CutOneD.peval_eq_sum, h_eq, lam_eq]

/-- The certified bound `eps / Lam ≥ 14.453278`. -/
theorem eps_ge : (14453278 : ℝ) / 1000000 ≤ (Case1Data.cf.eps : ℝ) / (Case1Data.cf.Lam : ℝ) := by
  have hL : (0 : ℝ) < (Case1Data.cf.Lam : ℝ) := by
    have : 0 < Case1Data.cf.Lam := by decide +kernel
    exact_mod_cast this
  have hI : (14453278 : ℤ) * (Case1Data.cf.Lam : ℤ) ≤ 1000000 * Case1Data.cf.eps := by
    decide +kernel
  have hR : (14453278 : ℝ) * (Case1Data.cf.Lam : ℝ) ≤ 1000000 * (Case1Data.cf.eps : ℝ) := by
    exact_mod_cast hI
  rw [div_le_div_iff₀ (by norm_num) hL]
  linarith

/-- **Case 1 margin (exact certificate).**  Every configuration on the unit sphere all of whose
pairwise inner products are `≥ -9/10` has energy at least `E(P) + 3/10000`. -/
theorem case1_margin : ∀ y ∈ SphereConfig 7, (∀ i j, i ≠ j → (-9 / 10 : ℝ) ≤ ⟪y i, y j⟫_ℝ) →
    coulombEnergy pentBipyramid + 3 / 10000 ≤ coulombEnergy y := by
  have hP := (EPBounds.coulombEnergy_pent_bounds).2
  have han : ((Case1Data.cf.an : ℤ) : ℝ) / (Case1Data.cf.ad : ℝ) = -9 / 10 := by
    show (((-9 : ℤ) : ℝ)) / (((10 : ℕ) : ℝ)) = -9 / 10
    norm_num
  have hC : (0 : ℝ) < ((Nat.choose 7 2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by norm_num)
  refine TwoRegime.margin_of_threePoint_cut (H := Case1Data.cf.Hf) (a := -9 / 10) (η := 3 / 10000)
    Case1Data.cf.K Case1Data.cf.m Case1Data.cf.Fm
    (fun k hk => fmat_psd Case1Data.cf.Lam ((check_parts cf_ok).2.2.2.1 k hk)) ?_ ?_
  · intro u v t hg hu hv ht
    have h := Cert3.hpt_cut Case1Data.cf cf_ok hg (by rw [han]; exact hu)
      (by rw [han]; exact hv) (by rw [han]; exact ht)
    have hdiv : (coulombEnergy pentBipyramid + 3 / 10000) / ((Nat.choose 7 2 : ℕ) : ℝ)
        ≤ ((Case1Data.cf.eps : ℝ) / (Case1Data.cf.Lam : ℝ)) / ((Nat.choose 7 2 : ℕ) : ℝ) := by
      apply div_le_div_of_nonneg_right _ hC.le
      linarith [eps_ge, hP]
    have hn : Case1Data.cf.n = 7 := rfl
    rw [hn] at h
    linarith
  · intro t h1 h2
    rw [Hf_eq]
    exact CutOneD.cutH_le_phi h1 h2

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

end TypedRoot

section TypedComb

variable {n : ℕ}

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

end Sym

/-! # The `n = 7` typed instance: two poles (indices `0, 1`) and five ring points (`2..6`) -/

section Typed7

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

/-! ## B. The substitution `y = √(2 - 2t) / 2` -/

/-! ## C. Plain certificates: `H ≤ phi` on a `y`-interval -/

/-! ## D. Contact certificates with coercivity -/

/-! ## E. Shapes of the hypotheses `hA hB hC` of `cap_of_typed_tube7` and closeness of the nodes -/

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

/-! ## B. Two nodes -/

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

/-! ## The positivity check, by list traversal -/

end Cert
end ThomsonN7

end Asm_CertF

section Asm_CertT
namespace ThomsonN7

open Kron Kron.Ex
namespace Cert

open ThreePoint

/-! ## Multiplier atoms of the typed certificates -/

/-! ## Kronecker values of the quadratic form of a block -/

/-! ## Size bounds of packed blocks -/

/-! ### Degrees -/

/-! ## Analytic bounds of typed blocks -/

/-! ## Sums of expressions -/

/-! ## The hybrid check -/

end Cert
end ThomsonN7

namespace ThomsonN7

open Kron Kron.Ex
namespace Cert

/-! # Flat (Nat-only inner loops) evaluation of the quadratic form of a packed block -/

end Cert
end ThomsonN7

namespace ThomsonN7

open Kron Kron.Ex
namespace Cert

open ThreePoint
open scoped RealInnerProductSpace

/-! ## One-variable polynomials, marginals, kernel sums -/

/-! ## The three type slacks, scaled to integer polynomials -/

section RealSide

variable (K : ℕ) (m : ℕ → ℕ) (Lam : ℕ) (blP blR : ℕ → Blk)

end RealSide

/-! ## The certificate -/

namespace TCert

variable (cf : TCert)

/-! ### The real data of a certificate -/

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

end Bridge3

end Glue
end ThomsonN7

end Asm_Bridge3

section Asm_cap_tc
namespace ThomsonN7
open Kron Kron.Ex
namespace Cert
open ThreePoint

end Cert
end ThomsonN7

end Asm_cap_tc

section Asm_cap_ct
namespace ThomsonN7
namespace Final

end Final
end ThomsonN7

end Asm_cap_ct

section Asm_cap_capspec
namespace ThomsonN7
namespace Final

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


namespace ThomsonN7.PlatformBridge

lemma two_mul_energy {N : ℕ} (x : Fin N → R3) :
    2 * coulombEnergy x = ∑ i, ∑ j, ‖x i - x j‖⁻¹ := by
  unfold coulombEnergy
  have key : ∀ i, ∑ j, ‖x i - x j‖⁻¹
      = ∑ j ∈ Finset.Ioi i, ‖x i - x j‖⁻¹ + ∑ j ∈ Finset.Iio i, ‖x i - x j‖⁻¹ := by
    intro i
    have h1 : (Finset.univ : Finset (Fin N)) = Finset.Ioi i ∪ ({i} ∪ Finset.Iio i) := by
      ext j; simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_Ioi, Finset.mem_singleton,
        Finset.mem_Iio, true_iff]; omega
    rw [h1, Finset.sum_union, Finset.sum_union]
    · simp
    · simp
    · rw [Finset.disjoint_left]; intro a ha; simp at ha ⊢; omega
  simp_rw [key, Finset.sum_add_distrib]
  have hswap : ∑ i, ∑ j ∈ Finset.Iio i, ‖x i - x j‖⁻¹
      = ∑ i, ∑ j ∈ Finset.Ioi i, ‖x i - x j‖⁻¹ := by
    rw [Finset.sum_sigma', Finset.sum_sigma']
    refine Finset.sum_bij' (fun p _ => ⟨p.2, p.1⟩) (fun p _ => ⟨p.2, p.1⟩) ?_ ?_ ?_ ?_ ?_
    · intro p hp; simp at hp ⊢; exact hp
    · intro p hp; simp at hp ⊢; exact hp
    · intro p _; rfl
    · intro p _; rfl
    · intro p _; simp [norm_sub_rev]
  rw [hswap]; ring

lemma energy_comp_perm {N : ℕ} (x : Fin N → R3) (σ : Equiv.Perm (Fin N)) :
    coulombEnergy (x ∘ σ) = coulombEnergy x := by
  have h1 := two_mul_energy (x ∘ σ)
  have h2 := two_mul_energy x
  have h3 : ∑ i, ∑ j, ‖(x ∘ σ) i - (x ∘ σ) j‖⁻¹ = ∑ i, ∑ j, ‖x i - x j‖⁻¹ := by
    simp only [Function.comp]
    rw [Equiv.sum_comp σ (fun i => ∑ j, ‖x i - x (σ j)‖⁻¹)]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Equiv.sum_comp σ (fun j => ‖x i - x j‖⁻¹)
  linarith

/-- The two Coulomb energies agree. -/
lemma energy_eq {N : ℕ} (y : Fin N → R3) :
    ThomsonProblem.coulombEnergy y = coulombEnergy y := by
  unfold ThomsonProblem.coulombEnergy coulombEnergy
  simp [dist_eq_norm]

lemma admissible_iff {N : ℕ} (y : Fin N → R3) :
    ThomsonProblem.IsAdmissible y ↔ y ∈ SphereConfig N := Iff.rfl

/-- Relabelling of the repository's bipyramid into the platform's ordering. -/
def relabel : Equiv.Perm (Fin 7) where
  toFun := ![5, 6, 0, 1, 2, 3, 4]
  invFun := ![2, 3, 4, 5, 6, 0, 1]
  left_inv := by decide
  right_inv := by decide

lemma pent_eq : ThomsonProblem.pentagonalBipyramid = pentBipyramid ∘ relabel := by
  funext i
  fin_cases i <;>
    simp [ThomsonProblem.pentagonalBipyramid, ThomsonProblem.pentagonVertex, pentBipyramid,
      relabel, cyl]

lemma pent_energy_eq :
    ThomsonProblem.coulombEnergy ThomsonProblem.pentagonalBipyramid
      = coulombEnergy pentBipyramid := by
  rw [energy_eq, pent_eq, energy_comp_perm]

end ThomsonN7.PlatformBridge

open ThomsonProblem in
theorem solution : ∀ y : Fin 7 → Space, IsAdmissible y →
    (∀ i j, i ≠ j → (-9 / 10 : ℝ) ≤ inner ℝ (y i) (y j)) →
    coulombEnergy pentagonalBipyramid + 3 / 10000 ≤ coulombEnergy y := by
  intro y hy h
  rw [ThomsonN7.PlatformBridge.pent_energy_eq, ThomsonN7.PlatformBridge.energy_eq]
  exact ThomsonN7.Case1.case1_margin y hy h
