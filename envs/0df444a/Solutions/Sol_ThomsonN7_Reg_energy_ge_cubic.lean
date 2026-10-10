-- Prove2me | solution 1 for ThomsonN7.Reg.energy_ge_cubic
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-10-10T02:08:49.658981+00:00
-- url     : https://prove2.me/submissions/d99674bd-b4f3-4b89-b800-e4b63600e190

import Mathlib
import Definitions.Def_ThomsonN7_core

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

lemma norm_sq_cyl (ρ θ h : ℝ) : ‖cyl ρ θ h‖ ^ 2 = ρ ^ 2 + h ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [cyl, Fin.sum_univ_three, mul_pow]
  nlinarith [sin_sq_add_cos_sq θ]

lemma int_eq_zero_of_cos_eq_one (m : ℕ) (hm : 0 < m) (d : ℤ) (hd : |d| < m)
    (h : cos (2 * π * d / m) = 1) : d = 0 := by
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).1 h
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 : (n : ℝ) * m = d := by
    field_simp at hn
    nlinarith [Real.pi_pos]
  have h2 : n * (m : ℤ) = d := by exact_mod_cast h1
  have hm2 : (0 : ℤ) < m := by exact_mod_cast hm
  rw [abs_lt] at hd
  rcases lt_trichotomy n 0 with hn0 | hn0 | hn0
  · nlinarith
  · subst hn0; simpa using h2.symm
  · nlinarith

lemma cos_sub_eq_one_of_cyl_eq {ρ θ θ' h : ℝ} (hρ : 0 < ρ)
    (H : cyl ρ θ h = cyl ρ θ' h) : cos (θ - θ') = 1 := by
  have := norm_sq_cyl_sub ρ θ h ρ θ' h
  rw [H, sub_self, norm_zero] at this
  have hρ2 : 0 < ρ ^ 2 := by positivity
  nlinarith

lemma pent_angle_inj {i j : ℕ} (hi : i < 5) (hj : j < 5)
    (H : cos (2 * π * (i : ℕ) / 5 - 2 * π * (j : ℕ) / 5) = 1) : i = j := by
  have := int_eq_zero_of_cos_eq_one 5 (by norm_num) ((i : ℤ) - j) (by rw [abs_lt]; constructor <;> omega)
    (by convert H using 2; push_cast; ring)
  omega

lemma pent_of_lt {i : Fin 7} (hi : (i : ℕ) < 5) :
    pentBipyramid i = cyl 1 (2 * π * (i : ℕ) / 5) 0 := by
  simp [pentBipyramid, hi]

lemma pent_five : pentBipyramid 5 = cyl 0 0 1 := by simp [pentBipyramid]
lemma pent_six : pentBipyramid 6 = cyl 0 0 (-1) := by simp [pentBipyramid]

lemma pent_cases (i : Fin 7) : (i : ℕ) < 5 ∨ i = 5 ∨ i = 6 := by
  fin_cases i <;> simp

theorem pentBipyramid_injective : Function.Injective pentBipyramid := by
  intro i j hij
  have h2 := congrArg (fun v : R3 => v 2) hij
  rcases pent_cases i with hi | rfl | rfl <;> rcases pent_cases j with hj | rfl | rfl
  · rw [pent_of_lt hi, pent_of_lt hj] at hij
    exact Fin.ext (pent_angle_inj hi hj (cos_sub_eq_one_of_cyl_eq one_pos hij))
  · simp [pent_of_lt hi, pent_five, cyl] at h2
  · simp [pent_of_lt hi, pent_six, cyl] at h2
  · simp [pent_of_lt hj, pent_five, cyl] at h2
  · rfl
  · simp [pent_five, pent_six, cyl] at h2; norm_num at h2
  · simp [pent_of_lt hj, pent_six, cyl] at h2
  · simp [pent_five, pent_six, cyl] at h2; norm_num at h2
  · rfl

/-- The pentagonal bipyramid is an admissible configuration. -/
theorem pentBipyramid_mem : pentBipyramid ∈ SphereConfig 7 := by
  refine ⟨fun i => ?_, pentBipyramid_injective⟩
  have : ‖pentBipyramid i‖ ^ 2 = 1 := by
    rcases pent_cases i with hi | rfl | rfl
    · rw [pent_of_lt hi, norm_sq_cyl]; norm_num
    · rw [pent_five, norm_sq_cyl]; norm_num
    · rw [pent_six, norm_sq_cyl]; norm_num
  nlinarith [norm_nonneg (pentBipyramid i)]

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

lemma two_mul_sum_Ioi {n : ℕ} (F : Fin n → Fin n → ℝ) (hF : ∀ i j, F i j = F j i) :
    2 * ∑ i, ∑ j ∈ Finset.Ioi i, F i j = ∑ i, ∑ j, if i = j then 0 else F i j := by
  have h1 : ∀ i : Fin n, ∑ j ∈ Finset.Ioi i, F i j = ∑ j, if i < j then F i j else 0 := by
    intro i
    rw [← Finset.sum_filter]
    congr 1
    ext j; simp
  have h2 : ∀ i j : Fin n, (if i = j then 0 else F i j) =
      (if i < j then F i j else 0) + (if j < i then F j i else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.ne, not_lt_of_gt h]
    · simp [h]
    · simp [h, h.ne', not_lt_of_gt h, hF i j]
  simp only [h1, h2, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => if j < i then F j i else 0)]
  ring

/-! ### Gram values of the pentagonal bipyramid -/

lemma inner_cyl (ρ θ h ρ' θ' h' : ℝ) :
    inner ℝ (cyl ρ θ h) (cyl ρ' θ' h') = ρ * ρ' * cos (θ - θ') + h * h' := by
  simp only [cyl, PiLp.inner_apply, Fin.sum_univ_three, cos_sub]
  simp
  ring

lemma cos_2pi5 : cos (2 * π / 5) = c1 := by
  have hs : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h : cos (2 * π / 5) = 2 * cos (π / 5) ^ 2 - 1 := by
    rw [← cos_two_mul]; congr 1; ring
  rw [h, cos_pi_div_five]; unfold c1
  linear_combination (1 / 8) * hs

lemma cos_4pi5 : cos (4 * π / 5) = c2 := by
  have h : cos (4 * π / 5) = - cos (π / 5) := by
    rw [← cos_pi_sub]; congr 1; ring
  rw [h, cos_pi_div_five]; unfold c2; ring

lemma cos_6pi5 : cos (6 * π / 5) = c2 := by
  have h : cos (6 * π / 5) = - cos (π / 5) := by
    rw [← cos_add_pi]; congr 1; ring
  rw [h, cos_pi_div_five]; unfold c2; ring

lemma cos_8pi5 : cos (8 * π / 5) = c1 := by
  have h : cos (8 * π / 5) = cos (2 * π / 5) := by
    rw [← cos_neg (2 * π / 5), ← cos_add_two_pi (-(2 * π / 5))]; congr 1; ring
  rw [h, cos_2pi5]

lemma pent_inner_north {i : Fin 7} (hi : (i : ℕ) < 5) :
    inner ℝ (pentBipyramid i) (pentBipyramid 5) = 0 := by
  rw [pent_of_lt hi, pent_five, inner_cyl]; simp

lemma pent_inner_south {i : Fin 7} (hi : (i : ℕ) < 5) :
    inner ℝ (pentBipyramid i) (pentBipyramid 6) = 0 := by
  rw [pent_of_lt hi, pent_six, inner_cyl]; simp

lemma pent_inner_poles : inner ℝ (pentBipyramid 5) (pentBipyramid 6) = -1 := by
  rw [pent_five, pent_six, inner_cyl]; simp

lemma pent_norm (i : Fin 7) : ‖pentBipyramid i‖ = 1 := pentBipyramid_mem.1 i

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

/-! ### Combinatorics of ordered triple sums -/

section Comb

variable {n : ℕ}

end Comb

section Comb2

variable {n : ℕ}

end Comb2

section Comb3

variable {n : ℕ}

end Comb3

section Comb4

variable {n : ℕ}

end Comb4

section Final

variable {n : ℕ}

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

namespace Ex

end Ex

open Ex

end Kron

/-! ## Builders for `Ex` with evaluation lemmas -/

namespace Kron
namespace Ex

variable (u v t : ℝ)

/-! ### Substitution of variables by variables or `1` -/

end Ex
end Kron

/- BEGIN CERT1 -/
section Cert1Block

open Kron Kron.Ex

namespace Cert

open ThreePoint

/-! ## `Q_k` as a polynomial expression -/

/-! ## Quadratic forms: `L D Lᵀ` plus a diagonally dominant remainder -/

/-! ## Integer data of a positive semidefinite block -/

namespace Blk

end Blk

end Cert

end Cert1Block

/- BEGIN CERT3FILE -/
section Cert3Block

open Kron Kron.Ex

namespace Cert

open ThreePoint

/-! ## Helpers: zero-skipping scaling, monomial-preserving substitution -/

/-! ## The `F`-blocks: `Λ · Fp(u,v)` -/

/-! ## Block matrices and their quadratic forms -/

/-! ## Symmetrisation and the `F`-part of the identity -/

/-! ## SOS blocks with multipliers -/

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

lemma phi_pos {t : ℝ} (h : t < 1) : 0 < phi t := by
  unfold phi
  have : 0 < 2 - 2 * t := by linarith
  positivity

lemma phi_sq_mul {t : ℝ} (h : t < 1) : phi t ^ 2 * (2 - 2 * t) = 1 := by
  unfold phi
  have h2 : 0 < 2 - 2 * t := by linarith
  rw [inv_pow, Real.sq_sqrt h2.le]
  exact inv_mul_cancel₀ h2.ne'

/-- With `a = phi t0`, `b = phi t` the increment `τ = t - t0` is `(b² - a²) / (2 a² b²)`. -/
lemma phi_tau_eq {t0 t : ℝ} (h0 : t0 < 1) (h : t < 1) :
    t - t0 = (phi t ^ 2 - phi t0 ^ 2) / (2 * phi t0 ^ 2 * phi t ^ 2) := by
  have ha := phi_pos h0
  have hb := phi_pos h
  have ha2 := phi_sq_mul h0
  have hb2 := phi_sq_mul h
  generalize phi t0 = a at *
  generalize phi t = b at *
  rw [eq_div_iff (by positivity)]
  linear_combination b ^ 2 * ha2 - a ^ 2 * hb2

/-- **Bregman cubic bound** for the Coulomb pair potential `phi t = (2 - 2t)^(-1/2)`:
the remainder of the *first-order* Taylor expansion at `t0` dominates the *second and third
order* Taylor terms.  With `phi' = phi^3`, `phi'' = 3 phi^5`, `phi''' = 15 phi^7`, this reads
`phi t ≥ phi t0 + phi' τ + phi'' τ²/2 + phi''' τ³/6`, `τ = t - t0` (any sign of `τ`).
The gap is `(a-b)^4 (5a^3 + 20a^2 b + 29 a b^2 + 16 b^3) / (16 b^6)`, `a = phi t0`, `b = phi t`. -/
lemma phi_bregman_cubic {t0 t : ℝ} (h0 : t0 < 1) (h : t < 1) :
    phi t0 + phi t0 ^ 3 * (t - t0) + 3 / 2 * phi t0 ^ 5 * (t - t0) ^ 2
      + 5 / 2 * phi t0 ^ 7 * (t - t0) ^ 3 ≤ phi t := by
  have ha := phi_pos h0
  have hb := phi_pos h
  have hτ := phi_tau_eq h0 h
  generalize phi t0 = a at *
  generalize phi t = b at *
  have key : b - (a + a ^ 3 * (t - t0) + 3 / 2 * a ^ 5 * (t - t0) ^ 2
      + 5 / 2 * a ^ 7 * (t - t0) ^ 3)
      = (a - b) ^ 4 * (5 * a ^ 3 + 20 * a ^ 2 * b + 29 * a * b ^ 2 + 16 * b ^ 3) / (16 * b ^ 6) := by
    rw [hτ]
    field_simp
    ring
  have : 0 ≤ (a - b) ^ 4 * (5 * a ^ 3 + 20 * a ^ 2 * b + 29 * a * b ^ 2 + 16 * b ^ 3)
      / (16 * b ^ 6) := by
    positivity
  linarith

end Base

/- END P3ext -/

/- BEGIN P1 -/

/-! ## P1: the bipyramid is a critical point of the Coulomb energy on the constraint set (agent7) -/

namespace Reg

open Base

lemma s2_eq : s2 = 2 * s1 * c1 := by
  unfold s1 s2
  rw [← cos_2pi5, show 4 * π / 5 = 2 * (2 * π / 5) by ring, sin_two_mul]

lemma s1_sq : s1 ^ 2 = 1 - c1 ^ 2 := by
  rw [← cos_2pi5]; unfold s1
  nlinarith [sin_sq_add_cos_sq (2 * π / 5)]

lemma sin_6pi5 : sin (6 * π / 5) = -s2 := by
  unfold s2
  rw [show 6 * π / 5 = 2 * π - 4 * π / 5 by ring, Real.sin_two_pi_sub]

lemma sin_8pi5 : sin (8 * π / 5) = -s1 := by
  unfold s1
  rw [show 8 * π / 5 = 2 * π - 2 * π / 5 by ring, Real.sin_two_pi_sub]

/-- Relations between the trigonometric constants used by the coordinate computations. -/
lemma hF1 : c2 + c1 + 1 / 2 = 0 := by unfold c1 c2; ring
lemma hF2 : s2 - 2 * s1 * c1 = 0 := by rw [s2_eq]; ring
lemma hF3 : s1 ^ 2 - 1 + c1 ^ 2 = 0 := by rw [s1_sq]; ring
lemma hF4 : c1 ^ 2 + c1 / 2 - 1 / 4 = 0 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  unfold c1
  linear_combination (1 / 16) * h

lemma pent_0 : pentBipyramid 0 = !₂[1, 0, 0] := by
  rw [pent_of_lt (by decide)]; simp [cyl]

lemma pent_1 : pentBipyramid 1 = !₂[c1, s1, 0] := by
  rw [pent_of_lt (by decide)]; simp [cyl, cos_2pi5, s1]

lemma pent_2 : pentBipyramid 2 = !₂[c2, s2, 0] := by
  rw [pent_of_lt (by decide)]
  have h1 : (2 * π * (((2 : Fin 7) : ℕ) : ℝ) / 5) = 4 * π / 5 := by
    norm_num; ring
  rw [h1]
  ext m; fin_cases m <;> simp [cyl, cos_4pi5, s2]

lemma pent_3 : pentBipyramid 3 = !₂[c2, -s2, 0] := by
  rw [pent_of_lt (by decide)]
  have h1 : (2 * π * (((3 : Fin 7) : ℕ) : ℝ) / 5) = 6 * π / 5 := by
    norm_num; ring
  rw [h1]
  ext m; fin_cases m <;> simp [cyl, cos_6pi5, sin_6pi5]

lemma pent_4 : pentBipyramid 4 = !₂[c1, -s1, 0] := by
  rw [pent_of_lt (by decide)]
  have h1 : (2 * π * (((4 : Fin 7) : ℕ) : ℝ) / 5) = 8 * π / 5 := by
    norm_num; ring
  rw [h1]
  ext m; fin_cases m <;> simp [cyl, cos_8pi5, sin_8pi5]

lemma pent_5' : pentBipyramid 5 = !₂[0, 0, 1] := by
  rw [pent_five]; simp [cyl]

lemma pent_6' : pentBipyramid 6 = !₂[0, 0, -1] := by
  rw [pent_six]; simp [cyl]

lemma inner_vec3 (a b c d e f : ℝ) :
    inner ℝ (!₂[a, b, c] : R3) !₂[d, e, f] = a * d + b * e + c * f := by
  simp [PiLp.inner_apply, Fin.sum_univ_three] <;> ring

lemma W_diag (i : Fin 7) : W i i = 0 := by simp [W]

lemma W_ne {i j : Fin 7} (h : i ≠ j) :
    W i j = phi (inner ℝ (pentBipyramid i) (pentBipyramid j)) ^ 3 := by simp [W, h]

lemma g_0_1 : inner ℝ (pentBipyramid 0) (pentBipyramid 1) = c1 := by
  rw [pent_0, pent_1, inner_vec3]
  ring

lemma g_0_2 : inner ℝ (pentBipyramid 0) (pentBipyramid 2) = c2 := by
  rw [pent_0, pent_2, inner_vec3]
  ring

lemma g_0_3 : inner ℝ (pentBipyramid 0) (pentBipyramid 3) = c2 := by
  rw [pent_0, pent_3, inner_vec3]
  ring

lemma g_0_4 : inner ℝ (pentBipyramid 0) (pentBipyramid 4) = c1 := by
  rw [pent_0, pent_4, inner_vec3]
  ring

lemma g_0_5 : inner ℝ (pentBipyramid 0) (pentBipyramid 5) = 0 :=
  pent_inner_north (by decide)

lemma g_0_6 : inner ℝ (pentBipyramid 0) (pentBipyramid 6) = 0 :=
  pent_inner_south (by decide)

lemma g_1_0 : inner ℝ (pentBipyramid 1) (pentBipyramid 0) = c1 := by
  rw [real_inner_comm]; exact g_0_1

lemma g_1_2 : inner ℝ (pentBipyramid 1) (pentBipyramid 2) = c1 := by
  rw [pent_1, pent_2, inner_vec3]
  linear_combination (c1) * hF1 + (s1) * hF2 + (2*c1) * hF3 + (-2*c1) * hF4

lemma g_1_3 : inner ℝ (pentBipyramid 1) (pentBipyramid 3) = c2 := by
  rw [pent_1, pent_3, inner_vec3]
  linear_combination (c1 - 1) * hF1 + (-s1) * hF2 + (-2*c1) * hF3 + (2*c1 - 2) * hF4

lemma g_1_4 : inner ℝ (pentBipyramid 1) (pentBipyramid 4) = c2 := by
  rw [pent_1, pent_4, inner_vec3]
  linear_combination (-1) * hF1 + (-1) * hF3 + (2) * hF4

lemma g_1_5 : inner ℝ (pentBipyramid 1) (pentBipyramid 5) = 0 :=
  pent_inner_north (by decide)

lemma g_1_6 : inner ℝ (pentBipyramid 1) (pentBipyramid 6) = 0 :=
  pent_inner_south (by decide)

lemma g_2_0 : inner ℝ (pentBipyramid 2) (pentBipyramid 0) = c2 := by
  rw [real_inner_comm]; exact g_0_2

lemma g_2_1 : inner ℝ (pentBipyramid 2) (pentBipyramid 1) = c1 := by
  rw [real_inner_comm]; exact g_1_2

lemma g_2_3 : inner ℝ (pentBipyramid 2) (pentBipyramid 3) = c1 := by
  rw [pent_2, pent_3, inner_vec3]
  linear_combination (-c1 + c2 - 1/2) * hF1 + (-2*c1*s1 - s2) * hF2 + (-4*c1^2) * hF3 + (4*c1^2 - 2*c1 - 1) * hF4

lemma g_2_4 : inner ℝ (pentBipyramid 2) (pentBipyramid 4) = c2 := by
  rw [pent_2, pent_4, inner_vec3]
  linear_combination (c1 - 1) * hF1 + (-s1) * hF2 + (-2*c1) * hF3 + (2*c1 - 2) * hF4

lemma g_2_5 : inner ℝ (pentBipyramid 2) (pentBipyramid 5) = 0 :=
  pent_inner_north (by decide)

lemma g_2_6 : inner ℝ (pentBipyramid 2) (pentBipyramid 6) = 0 :=
  pent_inner_south (by decide)

lemma g_3_0 : inner ℝ (pentBipyramid 3) (pentBipyramid 0) = c2 := by
  rw [real_inner_comm]; exact g_0_3

lemma g_3_1 : inner ℝ (pentBipyramid 3) (pentBipyramid 1) = c2 := by
  rw [real_inner_comm]; exact g_1_3

lemma g_3_2 : inner ℝ (pentBipyramid 3) (pentBipyramid 2) = c1 := by
  rw [real_inner_comm]; exact g_2_3

lemma g_3_4 : inner ℝ (pentBipyramid 3) (pentBipyramid 4) = c1 := by
  rw [pent_3, pent_4, inner_vec3]
  linear_combination (c1) * hF1 + (s1) * hF2 + (2*c1) * hF3 + (-2*c1) * hF4

lemma g_3_5 : inner ℝ (pentBipyramid 3) (pentBipyramid 5) = 0 :=
  pent_inner_north (by decide)

lemma g_3_6 : inner ℝ (pentBipyramid 3) (pentBipyramid 6) = 0 :=
  pent_inner_south (by decide)

lemma g_4_0 : inner ℝ (pentBipyramid 4) (pentBipyramid 0) = c1 := by
  rw [real_inner_comm]; exact g_0_4

lemma g_4_1 : inner ℝ (pentBipyramid 4) (pentBipyramid 1) = c2 := by
  rw [real_inner_comm]; exact g_1_4

lemma g_4_2 : inner ℝ (pentBipyramid 4) (pentBipyramid 2) = c2 := by
  rw [real_inner_comm]; exact g_2_4

lemma g_4_3 : inner ℝ (pentBipyramid 4) (pentBipyramid 3) = c1 := by
  rw [real_inner_comm]; exact g_3_4

lemma g_4_5 : inner ℝ (pentBipyramid 4) (pentBipyramid 5) = 0 :=
  pent_inner_north (by decide)

lemma g_4_6 : inner ℝ (pentBipyramid 4) (pentBipyramid 6) = 0 :=
  pent_inner_south (by decide)

lemma g_5_0 : inner ℝ (pentBipyramid 5) (pentBipyramid 0) = 0 := by
  rw [real_inner_comm]; exact g_0_5

lemma g_5_1 : inner ℝ (pentBipyramid 5) (pentBipyramid 1) = 0 := by
  rw [real_inner_comm]; exact g_1_5

lemma g_5_2 : inner ℝ (pentBipyramid 5) (pentBipyramid 2) = 0 := by
  rw [real_inner_comm]; exact g_2_5

lemma g_5_3 : inner ℝ (pentBipyramid 5) (pentBipyramid 3) = 0 := by
  rw [real_inner_comm]; exact g_3_5

lemma g_5_4 : inner ℝ (pentBipyramid 5) (pentBipyramid 4) = 0 := by
  rw [real_inner_comm]; exact g_4_5

lemma g_5_6 : inner ℝ (pentBipyramid 5) (pentBipyramid 6) = -1 := pent_inner_poles

lemma g_6_0 : inner ℝ (pentBipyramid 6) (pentBipyramid 0) = 0 := by
  rw [real_inner_comm]; exact g_0_6

lemma g_6_1 : inner ℝ (pentBipyramid 6) (pentBipyramid 1) = 0 := by
  rw [real_inner_comm]; exact g_1_6

lemma g_6_2 : inner ℝ (pentBipyramid 6) (pentBipyramid 2) = 0 := by
  rw [real_inner_comm]; exact g_2_6

lemma g_6_3 : inner ℝ (pentBipyramid 6) (pentBipyramid 3) = 0 := by
  rw [real_inner_comm]; exact g_3_6

lemma g_6_4 : inner ℝ (pentBipyramid 6) (pentBipyramid 4) = 0 := by
  rw [real_inner_comm]; exact g_4_6

lemma g_6_5 : inner ℝ (pentBipyramid 6) (pentBipyramid 5) = -1 := by
  rw [real_inner_comm]; exact g_5_6

lemma W_0_0 : W 0 0 = 0 := W_diag _

lemma W_0_1 : W 0 1 = phi c1 ^ 3 := by
  rw [W_ne (show (0 : Fin 7) ≠ 1 by decide), g_0_1]

lemma W_0_2 : W 0 2 = phi c2 ^ 3 := by
  rw [W_ne (show (0 : Fin 7) ≠ 2 by decide), g_0_2]

lemma W_0_3 : W 0 3 = phi c2 ^ 3 := by
  rw [W_ne (show (0 : Fin 7) ≠ 3 by decide), g_0_3]

lemma W_0_4 : W 0 4 = phi c1 ^ 3 := by
  rw [W_ne (show (0 : Fin 7) ≠ 4 by decide), g_0_4]

lemma W_0_5 : W 0 5 = phi 0 ^ 3 := by
  rw [W_ne (show (0 : Fin 7) ≠ 5 by decide), g_0_5]

lemma W_0_6 : W 0 6 = phi 0 ^ 3 := by
  rw [W_ne (show (0 : Fin 7) ≠ 6 by decide), g_0_6]

lemma W_1_0 : W 1 0 = phi c1 ^ 3 := by
  rw [W_ne (show (1 : Fin 7) ≠ 0 by decide), g_1_0]

lemma W_1_1 : W 1 1 = 0 := W_diag _

lemma W_1_2 : W 1 2 = phi c1 ^ 3 := by
  rw [W_ne (show (1 : Fin 7) ≠ 2 by decide), g_1_2]

lemma W_1_3 : W 1 3 = phi c2 ^ 3 := by
  rw [W_ne (show (1 : Fin 7) ≠ 3 by decide), g_1_3]

lemma W_1_4 : W 1 4 = phi c2 ^ 3 := by
  rw [W_ne (show (1 : Fin 7) ≠ 4 by decide), g_1_4]

lemma W_1_5 : W 1 5 = phi 0 ^ 3 := by
  rw [W_ne (show (1 : Fin 7) ≠ 5 by decide), g_1_5]

lemma W_1_6 : W 1 6 = phi 0 ^ 3 := by
  rw [W_ne (show (1 : Fin 7) ≠ 6 by decide), g_1_6]

lemma W_2_0 : W 2 0 = phi c2 ^ 3 := by
  rw [W_ne (show (2 : Fin 7) ≠ 0 by decide), g_2_0]

lemma W_2_1 : W 2 1 = phi c1 ^ 3 := by
  rw [W_ne (show (2 : Fin 7) ≠ 1 by decide), g_2_1]

lemma W_2_2 : W 2 2 = 0 := W_diag _

lemma W_2_3 : W 2 3 = phi c1 ^ 3 := by
  rw [W_ne (show (2 : Fin 7) ≠ 3 by decide), g_2_3]

lemma W_2_4 : W 2 4 = phi c2 ^ 3 := by
  rw [W_ne (show (2 : Fin 7) ≠ 4 by decide), g_2_4]

lemma W_2_5 : W 2 5 = phi 0 ^ 3 := by
  rw [W_ne (show (2 : Fin 7) ≠ 5 by decide), g_2_5]

lemma W_2_6 : W 2 6 = phi 0 ^ 3 := by
  rw [W_ne (show (2 : Fin 7) ≠ 6 by decide), g_2_6]

lemma W_3_0 : W 3 0 = phi c2 ^ 3 := by
  rw [W_ne (show (3 : Fin 7) ≠ 0 by decide), g_3_0]

lemma W_3_1 : W 3 1 = phi c2 ^ 3 := by
  rw [W_ne (show (3 : Fin 7) ≠ 1 by decide), g_3_1]

lemma W_3_2 : W 3 2 = phi c1 ^ 3 := by
  rw [W_ne (show (3 : Fin 7) ≠ 2 by decide), g_3_2]

lemma W_3_3 : W 3 3 = 0 := W_diag _

lemma W_3_4 : W 3 4 = phi c1 ^ 3 := by
  rw [W_ne (show (3 : Fin 7) ≠ 4 by decide), g_3_4]

lemma W_3_5 : W 3 5 = phi 0 ^ 3 := by
  rw [W_ne (show (3 : Fin 7) ≠ 5 by decide), g_3_5]

lemma W_3_6 : W 3 6 = phi 0 ^ 3 := by
  rw [W_ne (show (3 : Fin 7) ≠ 6 by decide), g_3_6]

lemma W_4_0 : W 4 0 = phi c1 ^ 3 := by
  rw [W_ne (show (4 : Fin 7) ≠ 0 by decide), g_4_0]

lemma W_4_1 : W 4 1 = phi c2 ^ 3 := by
  rw [W_ne (show (4 : Fin 7) ≠ 1 by decide), g_4_1]

lemma W_4_2 : W 4 2 = phi c2 ^ 3 := by
  rw [W_ne (show (4 : Fin 7) ≠ 2 by decide), g_4_2]

lemma W_4_3 : W 4 3 = phi c1 ^ 3 := by
  rw [W_ne (show (4 : Fin 7) ≠ 3 by decide), g_4_3]

lemma W_4_4 : W 4 4 = 0 := W_diag _

lemma W_4_5 : W 4 5 = phi 0 ^ 3 := by
  rw [W_ne (show (4 : Fin 7) ≠ 5 by decide), g_4_5]

lemma W_4_6 : W 4 6 = phi 0 ^ 3 := by
  rw [W_ne (show (4 : Fin 7) ≠ 6 by decide), g_4_6]

lemma W_5_0 : W 5 0 = phi 0 ^ 3 := by
  rw [W_ne (show (5 : Fin 7) ≠ 0 by decide), g_5_0]

lemma W_5_1 : W 5 1 = phi 0 ^ 3 := by
  rw [W_ne (show (5 : Fin 7) ≠ 1 by decide), g_5_1]

lemma W_5_2 : W 5 2 = phi 0 ^ 3 := by
  rw [W_ne (show (5 : Fin 7) ≠ 2 by decide), g_5_2]

lemma W_5_3 : W 5 3 = phi 0 ^ 3 := by
  rw [W_ne (show (5 : Fin 7) ≠ 3 by decide), g_5_3]

lemma W_5_4 : W 5 4 = phi 0 ^ 3 := by
  rw [W_ne (show (5 : Fin 7) ≠ 4 by decide), g_5_4]

lemma W_5_5 : W 5 5 = 0 := W_diag _

lemma W_5_6 : W 5 6 = phi (-1) ^ 3 := by
  rw [W_ne (show (5 : Fin 7) ≠ 6 by decide), g_5_6]

lemma W_6_0 : W 6 0 = phi 0 ^ 3 := by
  rw [W_ne (show (6 : Fin 7) ≠ 0 by decide), g_6_0]

lemma W_6_1 : W 6 1 = phi 0 ^ 3 := by
  rw [W_ne (show (6 : Fin 7) ≠ 1 by decide), g_6_1]

lemma W_6_2 : W 6 2 = phi 0 ^ 3 := by
  rw [W_ne (show (6 : Fin 7) ≠ 2 by decide), g_6_2]

lemma W_6_3 : W 6 3 = phi 0 ^ 3 := by
  rw [W_ne (show (6 : Fin 7) ≠ 3 by decide), g_6_3]

lemma W_6_4 : W 6 4 = phi 0 ^ 3 := by
  rw [W_ne (show (6 : Fin 7) ≠ 4 by decide), g_6_4]

lemma W_6_5 : W 6 5 = phi (-1) ^ 3 := by
  rw [W_ne (show (6 : Fin 7) ≠ 5 by decide), g_6_5]

lemma W_6_6 : W 6 6 = 0 := W_diag _

lemma crit_1_x (w1 w2 : ℝ) :
    c1*w2 + c2*w1 + c2*w2 + w1 = c1*(2*c1*w1 + 2*c2*w2) := by
  linear_combination (-2*c1*w2 + w1 + w2) * hF1 + (-2*w1 + 2*w2) * hF4

lemma crit_1_y (w1 w2 : ℝ) :
    -s1*w2 + s2*w1 - s2*w2 = s1*(2*c1*w1 + 2*c2*w2) := by
  linear_combination (-2*s1*w2) * hF1 + (w1 - w2) * hF2

lemma crit_2_x (w1 w2 : ℝ) :
    c1*w1 + c1*w2 + c2*w1 + w2 = c2*(2*c1*w1 + 2*c2*w2) := by
  linear_combination (-2*c1*w1 + 2*c1*w2 - 2*c2*w2 + w1 + w2) * hF1 + (2*w1 - 2*w2) * hF4

lemma crit_2_y (w1 w2 : ℝ) :
    s1*w1 - s1*w2 - s2*w1 = s2*(2*c1*w1 + 2*c2*w2) := by
  linear_combination (-2*s2*w2) * hF1 + (-2*c1*w1 + 2*c1*w2 - w1 + w2) * hF2 + (-4*s1*w1 + 4*s1*w2) * hF4

lemma crit_3_x (w1 w2 : ℝ) :
    c1*w1 + c1*w2 + c2*w1 + w2 = c2*(2*c1*w1 + 2*c2*w2) := by
  linear_combination (-2*c1*w1 + 2*c1*w2 - 2*c2*w2 + w1 + w2) * hF1 + (2*w1 - 2*w2) * hF4

lemma crit_3_y (w1 w2 : ℝ) :
    -s1*w1 + s1*w2 + s2*w1 = -s2*(2*c1*w1 + 2*c2*w2) := by
  linear_combination (2*s2*w2) * hF1 + (2*c1*w1 - 2*c1*w2 + w1 - w2) * hF2 + (4*s1*w1 - 4*s1*w2) * hF4

lemma crit_4_x (w1 w2 : ℝ) :
    c1*w2 + c2*w1 + c2*w2 + w1 = c1*(2*c1*w1 + 2*c2*w2) := by
  linear_combination (-2*c1*w2 + w1 + w2) * hF1 + (-2*w1 + 2*w2) * hF4

lemma crit_4_y (w1 w2 : ℝ) :
    s1*w2 - s2*w1 + s2*w2 = -s1*(2*c1*w1 + 2*c2*w2) := by
  linear_combination (2*s1*w2) * hF1 + (-w1 + w2) * hF2

lemma crit_5_x (w0 : ℝ) :
    2*c1*w0 + 2*c2*w0 + w0 = 0 := by
  linear_combination (2*w0) * hF1

lemma crit_6_x (w0 : ℝ) :
    2*c1*w0 + 2*c2*w0 + w0 = 0 := by
  linear_combination (2*w0) * hF1

lemma muP_0 : muP 0 = 2 * c1 * phi c1 ^ 3 + 2 * c2 * phi c2 ^ 3 := by
  simp only [muP, Fin.sum_univ_seven, W_0_0, W_0_1, W_0_2, W_0_3, W_0_4, W_0_5, W_0_6, g_0_1, g_0_2, g_0_3, g_0_4, g_0_5, g_0_6, zero_mul]
  ring

lemma muP_1 : muP 1 = 2 * c1 * phi c1 ^ 3 + 2 * c2 * phi c2 ^ 3 := by
  simp only [muP, Fin.sum_univ_seven, W_1_0, W_1_1, W_1_2, W_1_3, W_1_4, W_1_5, W_1_6, g_1_0, g_1_2, g_1_3, g_1_4, g_1_5, g_1_6, zero_mul]
  ring

lemma muP_2 : muP 2 = 2 * c1 * phi c1 ^ 3 + 2 * c2 * phi c2 ^ 3 := by
  simp only [muP, Fin.sum_univ_seven, W_2_0, W_2_1, W_2_2, W_2_3, W_2_4, W_2_5, W_2_6, g_2_0, g_2_1, g_2_3, g_2_4, g_2_5, g_2_6, zero_mul]
  ring

lemma muP_3 : muP 3 = 2 * c1 * phi c1 ^ 3 + 2 * c2 * phi c2 ^ 3 := by
  simp only [muP, Fin.sum_univ_seven, W_3_0, W_3_1, W_3_2, W_3_3, W_3_4, W_3_5, W_3_6, g_3_0, g_3_1, g_3_2, g_3_4, g_3_5, g_3_6, zero_mul]
  ring

lemma muP_4 : muP 4 = 2 * c1 * phi c1 ^ 3 + 2 * c2 * phi c2 ^ 3 := by
  simp only [muP, Fin.sum_univ_seven, W_4_0, W_4_1, W_4_2, W_4_3, W_4_4, W_4_5, W_4_6, g_4_0, g_4_1, g_4_2, g_4_3, g_4_5, g_4_6, zero_mul]
  ring

lemma muP_5 : muP 5 = -(phi (-1) ^ 3) := by
  simp only [muP, Fin.sum_univ_seven, W_5_0, W_5_1, W_5_2, W_5_3, W_5_4, W_5_5, W_5_6, g_5_0, g_5_1, g_5_2, g_5_3, g_5_4, g_5_6, zero_mul]
  ring

lemma muP_6 : muP 6 = -(phi (-1) ^ 3) := by
  simp only [muP, Fin.sum_univ_seven, W_6_0, W_6_1, W_6_2, W_6_3, W_6_4, W_6_5, W_6_6, g_6_0, g_6_1, g_6_2, g_6_3, g_6_4, g_6_5, zero_mul]
  ring

lemma pent_critical_0 : ∑ j, W 0 j • pentBipyramid j = muP 0 • pentBipyramid 0 := by
  rw [muP_0]
  ext m
  fin_cases m
  · simp [Fin.sum_univ_seven, W_0_0, W_0_1, W_0_2, W_0_3, W_0_4, W_0_5, W_0_6, pent_0, pent_1, pent_2, pent_3, pent_4, pent_5', pent_6'] <;> ring
  · simp [Fin.sum_univ_seven, W_0_0, W_0_1, W_0_2, W_0_3, W_0_4, W_0_5, W_0_6, pent_0, pent_1, pent_2, pent_3, pent_4, pent_5', pent_6'] <;> ring
  · simp [Fin.sum_univ_seven, W_0_0, W_0_1, W_0_2, W_0_3, W_0_4, W_0_5, W_0_6, pent_0, pent_1, pent_2, pent_3, pent_4, pent_5', pent_6'] <;> ring

lemma pent_critical_1 : ∑ j, W 1 j • pentBipyramid j = muP 1 • pentBipyramid 1 := by
  rw [muP_1]
  ext m
  fin_cases m
  · simp [Fin.sum_univ_seven, W_1_0, W_1_1, W_1_2, W_1_3, W_1_4, W_1_5, W_1_6, pent_0, pent_1, pent_2, pent_3, pent_4, pent_5', pent_6'] <;> linear_combination crit_1_x (phi c1 ^ 3) (phi c2 ^ 3)
  · simp [Fin.sum_univ_seven, W_1_0, W_1_1, W_1_2, W_1_3, W_1_4, W_1_5, W_1_6, pent_0, pent_1, pent_2, pent_3, pent_4, pent_5', pent_6'] <;> linear_combination crit_1_y (phi c1 ^ 3) (phi c2 ^ 3)
  · simp [Fin.sum_univ_seven, W_1_0, W_1_1, W_1_2, W_1_3, W_1_4, W_1_5, W_1_6, pent_0, pent_1, pent_2, pent_3, pent_4, pent_5', pent_6'] <;> ring

lemma pent_critical_2 : ∑ j, W 2 j • pentBipyramid j = muP 2 • pentBipyramid 2 := by
  rw [muP_2]
  ext m
  fin_cases m
  · simp [Fin.sum_univ_seven, W_2_0, W_2_1, W_2_2, W_2_3, W_2_4, W_2_5, W_2_6, pent_0, pent_1, pent_2, pent_3, pent_4, pent_5', pent_6'] <;> linear_combination crit_2_x (phi c1 ^ 3) (phi c2 ^ 3)
  · simp [Fin.sum_univ_seven, W_2_0, W_2_1, W_2_2, W_2_3, W_2_4, W_2_5, W_2_6, pent_0, pent_1, pent_2, pent_3, pent_4, pent_5', pent_6'] <;> linear_combination crit_2_y (phi c1 ^ 3) (phi c2 ^ 3)
  · simp [Fin.sum_univ_seven, W_2_0, W_2_1, W_2_2, W_2_3, W_2_4, W_2_5, W_2_6, pent_0, pent_1, pent_2, pent_3, pent_4, pent_5', pent_6'] <;> ring

lemma pent_critical_3 : ∑ j, W 3 j • pentBipyramid j = muP 3 • pentBipyramid 3 := by
  rw [muP_3]
  ext m
  fin_cases m
  · simp [Fin.sum_univ_seven, W_3_0, W_3_1, W_3_2, W_3_3, W_3_4, W_3_5, W_3_6, pent_0, pent_1, pent_2, pent_3, pent_4, pent_5', pent_6'] <;> linear_combination crit_3_x (phi c1 ^ 3) (phi c2 ^ 3)
  · simp [Fin.sum_univ_seven, W_3_0, W_3_1, W_3_2, W_3_3, W_3_4, W_3_5, W_3_6, pent_0, pent_1, pent_2, pent_3, pent_4, pent_5', pent_6'] <;> linear_combination crit_3_y (phi c1 ^ 3) (phi c2 ^ 3)
  · simp [Fin.sum_univ_seven, W_3_0, W_3_1, W_3_2, W_3_3, W_3_4, W_3_5, W_3_6, pent_0, pent_1, pent_2, pent_3, pent_4, pent_5', pent_6'] <;> ring

lemma pent_critical_4 : ∑ j, W 4 j • pentBipyramid j = muP 4 • pentBipyramid 4 := by
  rw [muP_4]
  ext m
  fin_cases m
  · simp [Fin.sum_univ_seven, W_4_0, W_4_1, W_4_2, W_4_3, W_4_4, W_4_5, W_4_6, pent_0, pent_1, pent_2, pent_3, pent_4, pent_5', pent_6'] <;> linear_combination crit_4_x (phi c1 ^ 3) (phi c2 ^ 3)
  · simp [Fin.sum_univ_seven, W_4_0, W_4_1, W_4_2, W_4_3, W_4_4, W_4_5, W_4_6, pent_0, pent_1, pent_2, pent_3, pent_4, pent_5', pent_6'] <;> linear_combination crit_4_y (phi c1 ^ 3) (phi c2 ^ 3)
  · simp [Fin.sum_univ_seven, W_4_0, W_4_1, W_4_2, W_4_3, W_4_4, W_4_5, W_4_6, pent_0, pent_1, pent_2, pent_3, pent_4, pent_5', pent_6'] <;> ring

lemma pent_critical_5 : ∑ j, W 5 j • pentBipyramid j = muP 5 • pentBipyramid 5 := by
  rw [muP_5]
  ext m
  fin_cases m
  · simp [Fin.sum_univ_seven, W_5_0, W_5_1, W_5_2, W_5_3, W_5_4, W_5_5, W_5_6, pent_0, pent_1, pent_2, pent_3, pent_4, pent_5', pent_6'] <;> linear_combination crit_5_x (phi 0 ^ 3)
  · simp [Fin.sum_univ_seven, W_5_0, W_5_1, W_5_2, W_5_3, W_5_4, W_5_5, W_5_6, pent_0, pent_1, pent_2, pent_3, pent_4, pent_5', pent_6'] <;> ring
  · simp [Fin.sum_univ_seven, W_5_0, W_5_1, W_5_2, W_5_3, W_5_4, W_5_5, W_5_6, pent_0, pent_1, pent_2, pent_3, pent_4, pent_5', pent_6'] <;> ring

lemma pent_critical_6 : ∑ j, W 6 j • pentBipyramid j = muP 6 • pentBipyramid 6 := by
  rw [muP_6]
  ext m
  fin_cases m
  · simp [Fin.sum_univ_seven, W_6_0, W_6_1, W_6_2, W_6_3, W_6_4, W_6_5, W_6_6, pent_0, pent_1, pent_2, pent_3, pent_4, pent_5', pent_6'] <;> linear_combination crit_6_x (phi 0 ^ 3)
  · simp [Fin.sum_univ_seven, W_6_0, W_6_1, W_6_2, W_6_3, W_6_4, W_6_5, W_6_6, pent_0, pent_1, pent_2, pent_3, pent_4, pent_5', pent_6'] <;> ring
  · simp [Fin.sum_univ_seven, W_6_0, W_6_1, W_6_2, W_6_3, W_6_4, W_6_5, W_6_6, pent_0, pent_1, pent_2, pent_3, pent_4, pent_5', pent_6'] <;> ring

/-- **Criticality (Lagrange condition)**: the bipyramid satisfies `∑_j φ'(t_ij) P_j = μ_i P_i`. -/
theorem pent_critical (i : Fin 7) :
    ∑ j, W i j • pentBipyramid j = muP i • pentBipyramid i := by
  fin_cases i
  · exact pent_critical_0
  · exact pent_critical_1
  · exact pent_critical_2
  · exact pent_critical_3
  · exact pent_critical_4
  · exact pent_critical_5
  · exact pent_critical_6

lemma W_symm (i j : Fin 7) : W i j = W j i := by
  by_cases h : i = j
  · subst h; rfl
  · rw [W_ne h, W_ne (Ne.symm h), real_inner_comm]

lemma sum_Ioi_add_swap {n : ℕ} (F : Fin n → Fin n → ℝ) (hd : ∀ i, F i i = 0) :
    ∑ i, ∑ j ∈ Finset.Ioi i, (F i j + F j i) = ∑ i, ∑ j, F i j := by
  have h2 := two_mul_sum_Ioi (fun i j => F i j + F j i) (fun i j => by ring)
  have h3 : ∀ i j, (if i = j then (0 : ℝ) else F i j + F j i) = F i j + F j i := by
    intro i j
    by_cases h : i = j
    · subst h; simp [hd]
    · simp [h]
  have hc : ∑ i, ∑ j, F j i = ∑ i, ∑ j, F i j := Finset.sum_comm
  have h4 : ∑ i, ∑ j, (F i j + F j i) = 2 * ∑ i, ∑ j, F i j := by
    simp only [Finset.sum_add_distrib, hc]; ring
  simp only [h3, h4] at h2
  linarith

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

lemma gP_lt_one {i j : Fin 7} (hij : i ≠ j) : gP i j < 1 :=
  inner_lt_one_of_ne (pent_norm i) (pent_norm j) (pentBipyramid_injective.ne hij)

/-- For a unit vector `y i = P i + h i` the normal component of `h i` is `-‖h i‖²/2`. -/
lemma inner_P_h {y : Fin 7 → R3} (hy : ∀ i, ‖y i‖ = 1) (i : Fin 7) :
    inner ℝ (pentBipyramid i) (y i - pentBipyramid i) = -(1 / 2) * ‖y i - pentBipyramid i‖ ^ 2 := by
  have h1 := hy i
  have h2 := pent_norm i
  have h3 : ‖y i‖ ^ 2 = ‖pentBipyramid i + (y i - pentBipyramid i)‖ ^ 2 := by simp
  rw [norm_add_sq_real, h1, h2] at h3
  linarith

lemma sum_W_inner_left (v : Fin 7 → R3) :
    ∑ i, ∑ j, W i j * inner ℝ (pentBipyramid i) (v j)
      = ∑ j, muP j * inner ℝ (pentBipyramid j) (v j) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := pent_critical j
  have h2 : inner ℝ (∑ i, W j i • pentBipyramid i) (v j)
      = inner ℝ (muP j • pentBipyramid j) (v j) := by rw [h]
  simp only [sum_inner, real_inner_smul_left] at h2
  simp only [W_symm j] at h2
  exact h2

lemma sum_W_inner_right (v : Fin 7 → R3) :
    ∑ i, ∑ j, W i j * inner ℝ (v i) (pentBipyramid j)
      = ∑ i, muP i * inner ℝ (v i) (pentBipyramid i) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  have h2 : inner ℝ (v i) (∑ j, W i j • pentBipyramid j)
      = inner ℝ (v i) (muP i • pentBipyramid i) := by rw [pent_critical i]
  simpa only [inner_sum, real_inner_smul_right] using h2

lemma tau_symm (y : Fin 7 → R3) (i j : Fin 7) : tau y i j = tau y j i := by
  unfold tau gP
  rw [real_inner_comm (y i), real_inner_comm (pentBipyramid i)]

lemma tau_expand (y : Fin 7 → R3) (i j : Fin 7) :
    tau y i j = inner ℝ (pentBipyramid i) (y j - pentBipyramid j)
      + inner ℝ (y i - pentBipyramid i) (pentBipyramid j)
      + inner ℝ (y i - pentBipyramid i) (y j - pentBipyramid j) := by
  unfold tau gP
  simp only [inner_sub_left, inner_sub_right]
  ring

/-- **(H)** For unit `y = P + h`, the first-order term `∑_{i<j} W_ij τ_ij` is the quadratic form
`½ ∑_{ij} (W_ij - δ_ij μ_i) ⟪h_i, h_j⟫` (from the criticality of `P`). -/
lemma sum_W_tau {y : Fin 7 → R3} (hy : ∀ i, ‖y i‖ = 1) :
    ∑ i, ∑ j ∈ Finset.Ioi i, W i j * tau y i j
      = 1 / 2 * ∑ i, ∑ j, W i j * inner ℝ (y i - pentBipyramid i) (y j - pentBipyramid j)
        - 1 / 2 * ∑ i, muP i * ‖y i - pentBipyramid i‖ ^ 2 := by
  have hF : ∑ i, ∑ j ∈ Finset.Ioi i, (W i j * tau y i j + W j i * tau y j i)
      = ∑ i, ∑ j, W i j * tau y i j :=
    sum_Ioi_add_swap (fun i j => W i j * tau y i j) (fun i => by simp [W_diag])
  have hF2 : ∀ i j, W j i * tau y j i = W i j * tau y i j := by
    intro i j; rw [W_symm j i, tau_symm y j i]
  have hF3 : ∑ i, ∑ j ∈ Finset.Ioi i, (W i j * tau y i j + W j i * tau y j i)
      = 2 * ∑ i, ∑ j ∈ Finset.Ioi i, W i j * tau y i j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hF2]; ring
  have hT : ∑ i, ∑ j, W i j * tau y i j
      = ∑ i, ∑ j, W i j * inner ℝ (pentBipyramid i) (y j - pentBipyramid j)
        + ∑ i, ∑ j, W i j * inner ℝ (y i - pentBipyramid i) (pentBipyramid j)
        + ∑ i, ∑ j, W i j * inner ℝ (y i - pentBipyramid i) (y j - pentBipyramid j) := by
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [tau_expand]; ring
  rw [sum_W_inner_left (fun j => y j - pentBipyramid j),
    sum_W_inner_right (fun j => y j - pentBipyramid j)] at hT
  have hN : ∀ i, inner ℝ (pentBipyramid i) (y i - pentBipyramid i)
      = -(1 / 2) * ‖y i - pentBipyramid i‖ ^ 2 := inner_P_h hy
  have hN' : ∀ i, inner ℝ (y i - pentBipyramid i) (pentBipyramid i)
      = -(1 / 2) * ‖y i - pentBipyramid i‖ ^ 2 := fun i => by rw [real_inner_comm]; exact hN i
  simp only [hN, hN'] at hT
  have hM : ∑ j, muP j * (-(1 / 2) * ‖y j - pentBipyramid j‖ ^ 2)
      = -(1 / 2) * ∑ j, muP j * ‖y j - pentBipyramid j‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hM] at hT
  linarith

/-- **(B3)**: the cubic Bregman lower bound for the energy difference of a unit configuration
`y` (injective) from the bipyramid, in terms of `h = y - P`. -/
theorem energy_ge_cubic {y : Fin 7 → R3} (hy : ∀ i, ‖y i‖ = 1) (hinj : Function.Injective y) :
    1 / 2 * ∑ i, ∑ j, W i j * inner ℝ (y i - pentBipyramid i) (y j - pentBipyramid j)
      - 1 / 2 * ∑ i, muP i * ‖y i - pentBipyramid i‖ ^ 2
      + ∑ i, ∑ j ∈ Finset.Ioi i, (3 / 2 * phi (gP i j) ^ 5 * tau y i j ^ 2
          + 5 / 2 * phi (gP i j) ^ 7 * tau y i j ^ 3)
      ≤ coulombEnergy y - coulombEnergy pentBipyramid := by
  rw [coulombEnergy_eq_sum_phi hy, coulombEnergy_eq_sum_phi pent_norm, ← sum_W_tau hy,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun j hj => ?_
  have hij : i ≠ j := (Finset.mem_Ioi.1 hj).ne
  have h0 : gP i j < 1 := gP_lt_one hij
  have h1 : inner ℝ (y i) (y j) < 1 := inner_lt_one_of_ne (hy i) (hy j) (hinj.ne hij)
  have hb := phi_bregman_cubic h0 h1
  have hW : W i j = phi (gP i j) ^ 3 := W_ne hij
  have hτ : inner ℝ (y i) (y j) - gP i j = tau y i j := rfl
  rw [hτ] at hb
  rw [hW]
  have hg : gP i j = inner ℝ (pentBipyramid i) (pentBipyramid j) := rfl
  rw [hg] at hb ⊢
  linarith

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

open ThomsonN7 in
theorem solution {y : Fin 7 → R3} (hy : ∀ i, ‖y i‖ = 1) (hinj : Function.Injective y) :
    1 / 2 * ∑ i, ∑ j, Reg.W i j * inner ℝ (y i - pentBipyramid i) (y j - pentBipyramid j)
      - 1 / 2 * ∑ i, Reg.muP i * ‖y i - pentBipyramid i‖ ^ 2
      + ∑ i, ∑ j ∈ Finset.Ioi i, (3 / 2 * Base.phi (Reg.gP i j) ^ 5 * Reg.tau y i j ^ 2
          + 5 / 2 * Base.phi (Reg.gP i j) ^ 7 * Reg.tau y i j ^ 3)
      ≤ coulombEnergy y - coulombEnergy pentBipyramid :=
  ThomsonN7.Reg.energy_ge_cubic hy hinj
