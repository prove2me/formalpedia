-- Prove2me | solution 1 for ThomsonN7.Reg.hessian_lower
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-10-10T02:09:19.714679+00:00
-- url     : https://prove2.me/submissions/41a06698-b7b9-493a-a52c-27dddbeb0697

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

lemma pent_of_lt {i : Fin 7} (hi : (i : ℕ) < 5) :
    pentBipyramid i = cyl 1 (2 * π * (i : ℕ) / 5) 0 := by
  simp [pentBipyramid, hi]

lemma pent_five : pentBipyramid 5 = cyl 0 0 1 := by simp [pentBipyramid]
lemma pent_six : pentBipyramid 6 = cyl 0 0 (-1) := by simp [pentBipyramid]

/- BEGIN M0 -/
namespace Base

open Finset

/-! ### Invariance -/

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

end Reg

/- END LOC1 -/

end ThomsonN7

/- BEGIN QCORE1 -/
namespace ThomsonN7
namespace Reg

lemma cross_of_enc {C lo hi T θ u v : ℝ} (h1 : lo ≤ C) (h2 : C ≤ hi)
    (h3 : T - θ ≤ lo) (h4 : hi ≤ T + θ) :
    0 ≤ (C - T) * (u * v) + θ / 2 * (u ^ 2 + v ^ 2) := by
  have e1 : 0 ≤ θ + (C - T) := by linarith
  have e2 : 0 ≤ θ - (C - T) := by linarith
  nlinarith [mul_nonneg e1 (sq_nonneg (u + v)), mul_nonneg e2 (sq_nonneg (u - v))]

lemma diag_of_enc {C lo hi T θ u : ℝ} (h1 : lo ≤ C) (h2 : C ≤ hi)
    (h3 : T - θ ≤ lo) (h4 : hi ≤ T + θ) :
    0 ≤ (C - T) * u ^ 2 + θ * u ^ 2 := by
  have e1 : 0 ≤ θ + (C - T) := by linarith
  nlinarith [mul_nonneg e1 (sq_nonneg u)]

lemma mon_lo (c s p q r : ℝ) (hb : InBox c s p q r) (i j k l m : ℕ) (t : ℝ)
    (ht : t ≤ (30901699 / 100000000 : ℝ) ^ i * (95105651 / 100000000 : ℝ) ^ j * (2126627 / 2500000 : ℝ) ^ k * (52573111 / 100000000 : ℝ) ^ l * (35355339 / 50000000 : ℝ) ^ m) :
    t ≤ c ^ i * s ^ j * p ^ k * q ^ l * r ^ m := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hb
  refine ht.trans ?_
  gcongr

lemma mon_hi (c s p q r : ℝ) (hb : InBox c s p q r) (i j k l m : ℕ) (t : ℝ)
    (ht : (309017 / 1000000 : ℝ) ^ i * (23776413 / 25000000 : ℝ) ^ j * (85065081 / 100000000 : ℝ) ^ k * (6571639 / 12500000 : ℝ) ^ l * (70710679 / 100000000 : ℝ) ^ m ≤ t) :
    c ^ i * s ^ j * p ^ k * q ^ l * r ^ m ≤ t := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hb
  refine le_trans ?_ ht
  gcongr

lemma mlo_0 (c s p q r : ℝ) (hb : InBox c s p q r) : (55242717 / 156250000 : ℝ) ≤ c ^ 0 * s ^ 0 * p ^ 0 * q ^ 0 * r ^ 3 :=
  mon_lo c s p q r hb 0 0 0 0 3 _ (by norm_num)
lemma mhi_0 (c s p q r : ℝ) (hb : InBox c s p q r) : c ^ 0 * s ^ 0 * p ^ 0 * q ^ 0 * r ^ 3 ≤ (3535534039 / 10000000000 : ℝ) :=
  mon_hi c s p q r hb 0 0 0 0 3 _ (by norm_num)
lemma mlo_1 (c s p q r : ℝ) (hb : InBox c s p q r) : (883883469 / 5000000000 : ℝ) ≤ c ^ 0 * s ^ 0 * p ^ 0 * q ^ 0 * r ^ 5 :=
  mon_lo c s p q r hb 0 0 0 0 5 _ (by norm_num)
lemma mhi_1 (c s p q r : ℝ) (hb : InBox c s p q r) : c ^ 0 * s ^ 0 * p ^ 0 * q ^ 0 * r ^ 5 ≤ (220970883 / 1250000000 : ℝ) :=
  mon_hi c s p q r hb 0 0 0 0 5 _ (by norm_num)
lemma mlo_2 (c s p q r : ℝ) (hb : InBox c s p q r) : (726542519 / 5000000000 : ℝ) ≤ c ^ 0 * s ^ 0 * p ^ 0 * q ^ 3 * r ^ 0 :=
  mon_lo c s p q r hb 0 0 0 3 0 _ (by norm_num)
lemma mhi_2 (c s p q r : ℝ) (hb : InBox c s p q r) : c ^ 0 * s ^ 0 * p ^ 0 * q ^ 3 * r ^ 0 ≤ (726542561 / 5000000000 : ℝ) :=
  mon_hi c s p q r hb 0 0 0 3 0 _ (by norm_num)
lemma mlo_3 (c s p q r : ℝ) (hb : InBox c s p q r) : (401622823 / 10000000000 : ℝ) ≤ c ^ 0 * s ^ 0 * p ^ 0 * q ^ 5 * r ^ 0 :=
  mon_lo c s p q r hb 0 0 0 5 0 _ (by norm_num)
lemma mhi_3 (c s p q r : ℝ) (hb : InBox c s p q r) : c ^ 0 * s ^ 0 * p ^ 0 * q ^ 5 * r ^ 0 ≤ (200811431 / 5000000000 : ℝ) :=
  mon_hi c s p q r hb 0 0 0 5 0 _ (by norm_num)
lemma mlo_4 (c s p q r : ℝ) (hb : InBox c s p q r) : (6155366893 / 10000000000 : ℝ) ≤ c ^ 0 * s ^ 0 * p ^ 3 * q ^ 0 * r ^ 0 :=
  mon_lo c s p q r hb 0 0 3 0 0 _ (by norm_num)
lemma mhi_4 (c s p q r : ℝ) (hb : InBox c s p q r) : c ^ 0 * s ^ 0 * p ^ 3 * q ^ 0 * r ^ 0 ≤ (6155367111 / 10000000000 : ℝ) :=
  mon_hi c s p q r hb 0 0 3 0 0 _ (by norm_num)
lemma mlo_5 (c s p q r : ℝ) (hb : InBox c s p q r) : (2227032619 / 5000000000 : ℝ) ≤ c ^ 0 * s ^ 0 * p ^ 5 * q ^ 0 * r ^ 0 :=
  mon_lo c s p q r hb 0 0 5 0 0 _ (by norm_num)
lemma mhi_5 (c s p q r : ℝ) (hb : InBox c s p q r) : c ^ 0 * s ^ 0 * p ^ 5 * q ^ 0 * r ^ 0 ≤ (4454065501 / 10000000000 : ℝ) :=
  mon_hi c s p q r hb 0 0 5 0 0 _ (by norm_num)
lemma mlo_6 (c s p q r : ℝ) (hb : InBox c s p q r) : (95105651 / 100000000 : ℝ) ≤ c ^ 0 * s ^ 1 * p ^ 0 * q ^ 0 * r ^ 0 :=
  mon_lo c s p q r hb 0 1 0 0 0 _ (by norm_num)
lemma mhi_6 (c s p q r : ℝ) (hb : InBox c s p q r) : c ^ 0 * s ^ 1 * p ^ 0 * q ^ 0 * r ^ 0 ≤ (23776413 / 25000000 : ℝ) :=
  mon_hi c s p q r hb 0 1 0 0 0 _ (by norm_num)
lemma mlo_7 (c s p q r : ℝ) (hb : InBox c s p q r) : (840623127 / 5000000000 : ℝ) ≤ c ^ 0 * s ^ 1 * p ^ 0 * q ^ 0 * r ^ 5 :=
  mon_lo c s p q r hb 0 1 0 0 5 _ (by norm_num)
lemma mhi_7 (c s p q r : ℝ) (hb : InBox c s p q r) : c ^ 0 * s ^ 1 * p ^ 0 * q ^ 0 * r ^ 5 ≤ (210155799 / 1250000000 : ℝ) :=
  mon_hi c s p q r hb 0 1 0 0 5 _ (by norm_num)
lemma mlo_8 (c s p q r : ℝ) (hb : InBox c s p q r) : (381966001 / 10000000000 : ℝ) ≤ c ^ 0 * s ^ 1 * p ^ 0 * q ^ 5 * r ^ 0 :=
  mon_lo c s p q r hb 0 1 0 5 0 _ (by norm_num)
lemma mhi_8 (c s p q r : ℝ) (hb : InBox c s p q r) : c ^ 0 * s ^ 1 * p ^ 0 * q ^ 5 * r ^ 0 ≤ (190983021 / 5000000000 : ℝ) :=
  mon_hi c s p q r hb 0 1 0 5 0 _ (by norm_num)
lemma mlo_9 (c s p q r : ℝ) (hb : InBox c s p q r) : (4236067741 / 10000000000 : ℝ) ≤ c ^ 0 * s ^ 1 * p ^ 5 * q ^ 0 * r ^ 0 :=
  mon_lo c s p q r hb 0 1 5 0 0 _ (by norm_num)
lemma mhi_9 (c s p q r : ℝ) (hb : InBox c s p q r) : c ^ 0 * s ^ 1 * p ^ 5 * q ^ 0 * r ^ 0 ≤ (1059017009 / 2500000000 : ℝ) :=
  mon_hi c s p q r hb 0 1 5 0 0 _ (by norm_num)
lemma mlo_10 (c s p q r : ℝ) (hb : InBox c s p q r) : (2261271213 / 2500000000 : ℝ) ≤ c ^ 0 * s ^ 2 * p ^ 0 * q ^ 0 * r ^ 0 :=
  mon_lo c s p q r hb 0 2 0 0 0 _ (by norm_num)
lemma mhi_10 (c s p q r : ℝ) (hb : InBox c s p q r) : c ^ 0 * s ^ 2 * p ^ 0 * q ^ 0 * r ^ 0 ≤ (9045085043 / 10000000000 : ℝ) :=
  mon_hi c s p q r hb 0 2 0 0 0 _ (by norm_num)
lemma mlo_11 (c s p q r : ℝ) (hb : InBox c s p q r) : (319792039 / 2000000000 : ℝ) ≤ c ^ 0 * s ^ 2 * p ^ 0 * q ^ 0 * r ^ 5 :=
  mon_lo c s p q r hb 0 2 0 0 5 _ (by norm_num)
lemma mhi_11 (c s p q r : ℝ) (hb : InBox c s p q r) : c ^ 0 * s ^ 2 * p ^ 0 * q ^ 0 * r ^ 5 ≤ (1598960343 / 10000000000 : ℝ) :=
  mon_hi c s p q r hb 0 2 0 0 5 _ (by norm_num)
lemma mlo_12 (c s p q r : ℝ) (hb : InBox c s p q r) : (363271251 / 10000000000 : ℝ) ≤ c ^ 0 * s ^ 2 * p ^ 0 * q ^ 5 * r ^ 0 :=
  mon_lo c s p q r hb 0 2 0 5 0 _ (by norm_num)
lemma mhi_12 (c s p q r : ℝ) (hb : InBox c s p q r) : c ^ 0 * s ^ 2 * p ^ 0 * q ^ 5 * r ^ 0 ≤ (72654259 / 2000000000 : ℝ) :=
  mon_hi c s p q r hb 0 2 0 5 0 _ (by norm_num)
lemma mlo_13 (c s p q r : ℝ) (hb : InBox c s p q r) : (2014369901 / 5000000000 : ℝ) ≤ c ^ 0 * s ^ 2 * p ^ 5 * q ^ 0 * r ^ 0 :=
  mon_lo c s p q r hb 0 2 5 0 0 _ (by norm_num)
lemma mhi_13 (c s p q r : ℝ) (hb : InBox c s p q r) : c ^ 0 * s ^ 2 * p ^ 5 * q ^ 0 * r ^ 0 ≤ (1007185031 / 2500000000 : ℝ) :=
  mon_hi c s p q r hb 0 2 5 0 0 _ (by norm_num)
lemma mlo_14 (c s p q r : ℝ) (hb : InBox c s p q r) : (30901699 / 100000000 : ℝ) ≤ c ^ 1 * s ^ 0 * p ^ 0 * q ^ 0 * r ^ 0 :=
  mon_lo c s p q r hb 1 0 0 0 0 _ (by norm_num)
lemma mhi_14 (c s p q r : ℝ) (hb : InBox c s p q r) : c ^ 1 * s ^ 0 * p ^ 0 * q ^ 0 * r ^ 0 ≤ (309017 / 1000000 : ℝ) :=
  mon_hi c s p q r hb 1 0 0 0 0 _ (by norm_num)
lemma mlo_15 (c s p q r : ℝ) (hb : InBox c s p q r) : (273135009 / 5000000000 : ℝ) ≤ c ^ 1 * s ^ 0 * p ^ 0 * q ^ 0 * r ^ 5 :=
  mon_lo c s p q r hb 1 0 0 0 5 _ (by norm_num)
lemma mhi_15 (c s p q r : ℝ) (hb : InBox c s p q r) : c ^ 1 * s ^ 0 * p ^ 0 * q ^ 0 * r ^ 5 ≤ (21850803 / 400000000 : ℝ) :=
  mon_hi c s p q r hb 1 0 0 0 5 _ (by norm_num)
lemma mlo_16 (c s p q r : ℝ) (hb : InBox c s p q r) : (112256991 / 2500000000 : ℝ) ≤ c ^ 1 * s ^ 0 * p ^ 0 * q ^ 3 * r ^ 0 :=
  mon_lo c s p q r hb 1 0 0 3 0 _ (by norm_num)
lemma mhi_16 (c s p q r : ℝ) (hb : InBox c s p q r) : c ^ 1 * s ^ 0 * p ^ 0 * q ^ 3 * r ^ 0 ≤ (89805601 / 2000000000 : ℝ) :=
  mon_hi c s p q r hb 1 0 0 3 0 _ (by norm_num)
lemma mlo_17 (c s p q r : ℝ) (hb : InBox c s p q r) : (31027069 / 2500000000 : ℝ) ≤ c ^ 1 * s ^ 0 * p ^ 0 * q ^ 5 * r ^ 0 :=
  mon_lo c s p q r hb 1 0 0 5 0 _ (by norm_num)
lemma mhi_17 (c s p q r : ℝ) (hb : InBox c s p q r) : c ^ 1 * s ^ 0 * p ^ 0 * q ^ 5 * r ^ 0 ≤ (31027073 / 2500000000 : ℝ) :=
  mon_hi c s p q r hb 1 0 0 5 0 _ (by norm_num)
lemma mlo_18 (c s p q r : ℝ) (hb : InBox c s p q r) : (1902112949 / 10000000000 : ℝ) ≤ c ^ 1 * s ^ 0 * p ^ 3 * q ^ 0 * r ^ 0 :=
  mon_lo c s p q r hb 1 0 3 0 0 _ (by norm_num)
lemma mhi_18 (c s p q r : ℝ) (hb : InBox c s p q r) : c ^ 1 * s ^ 0 * p ^ 3 * q ^ 0 * r ^ 0 ≤ (1902113079 / 10000000000 : ℝ) :=
  mon_hi c s p q r hb 1 0 3 0 0 _ (by norm_num)
lemma mlo_19 (c s p q r : ℝ) (hb : InBox c s p q r) : (1376381833 / 10000000000 : ℝ) ≤ c ^ 1 * s ^ 0 * p ^ 5 * q ^ 0 * r ^ 0 :=
  mon_lo c s p q r hb 1 0 5 0 0 _ (by norm_num)
lemma mhi_19 (c s p q r : ℝ) (hb : InBox c s p q r) : c ^ 1 * s ^ 0 * p ^ 5 * q ^ 0 * r ^ 0 ≤ (1376381959 / 10000000000 : ℝ) :=
  mon_hi c s p q r hb 1 0 5 0 0 _ (by norm_num)
lemma mlo_20 (c s p q r : ℝ) (hb : InBox c s p q r) : (14694631 / 50000000 : ℝ) ≤ c ^ 1 * s ^ 1 * p ^ 0 * q ^ 0 * r ^ 0 :=
  mon_lo c s p q r hb 1 1 0 0 0 _ (by norm_num)
lemma mhi_20 (c s p q r : ℝ) (hb : InBox c s p q r) : c ^ 1 * s ^ 1 * p ^ 0 * q ^ 0 * r ^ 0 ≤ (2938926327 / 10000000000 : ℝ) :=
  mon_hi c s p q r hb 1 1 0 0 0 _ (by norm_num)
lemma mlo_21 (c s p q r : ℝ) (hb : InBox c s p q r) : (519533657 / 10000000000 : ℝ) ≤ c ^ 1 * s ^ 1 * p ^ 0 * q ^ 0 * r ^ 5 :=
  mon_lo c s p q r hb 1 1 0 0 5 _ (by norm_num)
lemma mhi_21 (c s p q r : ℝ) (hb : InBox c s p q r) : c ^ 1 * s ^ 1 * p ^ 0 * q ^ 0 * r ^ 5 ≤ (519533717 / 10000000000 : ℝ) :=
  mon_hi c s p q r hb 1 1 0 0 5 _ (by norm_num)
lemma mlo_22 (c s p q r : ℝ) (hb : InBox c s p q r) : (118033983 / 10000000000 : ℝ) ≤ c ^ 1 * s ^ 1 * p ^ 0 * q ^ 5 * r ^ 0 :=
  mon_lo c s p q r hb 1 1 0 5 0 _ (by norm_num)
lemma mhi_22 (c s p q r : ℝ) (hb : InBox c s p q r) : c ^ 1 * s ^ 1 * p ^ 0 * q ^ 5 * r ^ 0 ≤ (118034001 / 10000000000 : ℝ) :=
  mon_hi c s p q r hb 1 1 0 5 0 _ (by norm_num)
lemma mlo_23 (c s p q r : ℝ) (hb : InBox c s p q r) : (654508451 / 5000000000 : ℝ) ≤ c ^ 1 * s ^ 1 * p ^ 5 * q ^ 0 * r ^ 0 :=
  mon_lo c s p q r hb 1 1 5 0 0 _ (by norm_num)
lemma mhi_23 (c s p q r : ℝ) (hb : InBox c s p q r) : c ^ 1 * s ^ 1 * p ^ 5 * q ^ 0 * r ^ 0 ≤ (327254259 / 2500000000 : ℝ) :=
  mon_hi c s p q r hb 1 1 5 0 0 _ (by norm_num)
lemma mlo_24 (c s p q r : ℝ) (hb : InBox c s p q r) : (559016979 / 2000000000 : ℝ) ≤ c ^ 1 * s ^ 2 * p ^ 0 * q ^ 0 * r ^ 0 :=
  mon_lo c s p q r hb 1 2 0 0 0 _ (by norm_num)
lemma mhi_24 (c s p q r : ℝ) (hb : InBox c s p q r) : c ^ 1 * s ^ 2 * p ^ 0 * q ^ 0 * r ^ 0 ≤ (559017009 / 2000000000 : ℝ) :=
  mon_hi c s p q r hb 1 2 0 0 0 _ (by norm_num)
lemma mlo_25 (c s p q r : ℝ) (hb : InBox c s p q r) : (28064247 / 2500000000 : ℝ) ≤ c ^ 1 * s ^ 2 * p ^ 0 * q ^ 5 * r ^ 0 :=
  mon_lo c s p q r hb 1 2 0 5 0 _ (by norm_num)
lemma mhi_25 (c s p q r : ℝ) (hb : InBox c s p q r) : c ^ 1 * s ^ 2 * p ^ 0 * q ^ 5 * r ^ 0 ≤ (56128503 / 5000000000 : ℝ) :=
  mon_hi c s p q r hb 1 2 0 5 0 _ (by norm_num)
lemma mlo_26 (c s p q r : ℝ) (hb : InBox c s p q r) : (1244949047 / 10000000000 : ℝ) ≤ c ^ 1 * s ^ 2 * p ^ 5 * q ^ 0 * r ^ 0 :=
  mon_lo c s p q r hb 1 2 5 0 0 _ (by norm_num)
lemma mhi_26 (c s p q r : ℝ) (hb : InBox c s p q r) : c ^ 1 * s ^ 2 * p ^ 5 * q ^ 0 * r ^ 0 ≤ (1244949187 / 10000000000 : ℝ) :=
  mon_hi c s p q r hb 1 2 5 0 0 _ (by norm_num)
lemma mlo_27 (c s p q r : ℝ) (hb : InBox c s p q r) : (954915001 / 10000000000 : ℝ) ≤ c ^ 2 * s ^ 0 * p ^ 0 * q ^ 0 * r ^ 0 :=
  mon_lo c s p q r hb 2 0 0 0 0 _ (by norm_num)
lemma mhi_27 (c s p q r : ℝ) (hb : InBox c s p q r) : c ^ 2 * s ^ 0 * p ^ 0 * q ^ 0 * r ^ 0 ≤ (954915063 / 10000000000 : ℝ) :=
  mon_hi c s p q r hb 2 0 0 0 0 _ (by norm_num)
lemma mlo_28 (c s p q r : ℝ) (hb : InBox c s p q r) : (42201679 / 2500000000 : ℝ) ≤ c ^ 2 * s ^ 0 * p ^ 0 * q ^ 0 * r ^ 5 :=
  mon_lo c s p q r hb 2 0 0 0 5 _ (by norm_num)
lemma mhi_28 (c s p q r : ℝ) (hb : InBox c s p q r) : c ^ 2 * s ^ 0 * p ^ 0 * q ^ 0 * r ^ 5 ≤ (8440337 / 500000000 : ℝ) :=
  mon_hi c s p q r hb 2 0 0 0 5 _ (by norm_num)
lemma mlo_29 (c s p q r : ℝ) (hb : InBox c s p q r) : (7670313 / 2000000000 : ℝ) ≤ c ^ 2 * s ^ 0 * p ^ 0 * q ^ 5 * r ^ 0 :=
  mon_lo c s p q r hb 2 0 0 5 0 _ (by norm_num)
lemma mhi_29 (c s p q r : ℝ) (hb : InBox c s p q r) : c ^ 2 * s ^ 0 * p ^ 0 * q ^ 5 * r ^ 0 ≤ (38351573 / 10000000000 : ℝ) :=
  mon_hi c s p q r hb 2 0 0 5 0 _ (by norm_num)
lemma mlo_30 (c s p q r : ℝ) (hb : InBox c s p q r) : (425325371 / 10000000000 : ℝ) ≤ c ^ 2 * s ^ 0 * p ^ 5 * q ^ 0 * r ^ 0 :=
  mon_lo c s p q r hb 2 0 5 0 0 _ (by norm_num)
lemma mhi_30 (c s p q r : ℝ) (hb : InBox c s p q r) : c ^ 2 * s ^ 0 * p ^ 5 * q ^ 0 * r ^ 0 ≤ (26582839 / 625000000 : ℝ) :=
  mon_hi c s p q r hb 2 0 5 0 0 _ (by norm_num)
lemma mlo_31 (c s p q r : ℝ) (hb : InBox c s p q r) : (56761133 / 625000000 : ℝ) ≤ c ^ 2 * s ^ 1 * p ^ 0 * q ^ 0 * r ^ 0 :=
  mon_lo c s p q r hb 2 1 0 0 0 _ (by norm_num)
lemma mhi_31 (c s p q r : ℝ) (hb : InBox c s p q r) : c ^ 2 * s ^ 1 * p ^ 0 * q ^ 0 * r ^ 0 ≤ (908178197 / 10000000000 : ℝ) :=
  mon_hi c s p q r hb 2 1 0 0 0 _ (by norm_num)
lemma mlo_32 (c s p q r : ℝ) (hb : InBox c s p q r) : (18237253 / 5000000000 : ℝ) ≤ c ^ 2 * s ^ 1 * p ^ 0 * q ^ 5 * r ^ 0 :=
  mon_lo c s p q r hb 2 1 0 5 0 _ (by norm_num)
lemma mhi_32 (c s p q r : ℝ) (hb : InBox c s p q r) : c ^ 2 * s ^ 1 * p ^ 0 * q ^ 5 * r ^ 0 ≤ (36474513 / 10000000000 : ℝ) :=
  mon_hi c s p q r hb 2 1 0 5 0 _ (by norm_num)
lemma mlo_33 (c s p q r : ℝ) (hb : InBox c s p q r) : (404508463 / 10000000000 : ℝ) ≤ c ^ 2 * s ^ 1 * p ^ 5 * q ^ 0 * r ^ 0 :=
  mon_lo c s p q r hb 2 1 5 0 0 _ (by norm_num)
lemma mhi_33 (c s p q r : ℝ) (hb : InBox c s p q r) : c ^ 2 * s ^ 1 * p ^ 5 * q ^ 0 * r ^ 0 ≤ (202254259 / 5000000000 : ℝ) :=
  mon_hi c s p q r hb 2 1 5 0 0 _ (by norm_num)
lemma mlo_34 (c s p q r : ℝ) (hb : InBox c s p q r) : (863728721 / 10000000000 : ℝ) ≤ c ^ 2 * s ^ 2 * p ^ 0 * q ^ 0 * r ^ 0 :=
  mon_lo c s p q r hb 2 2 0 0 0 _ (by norm_num)
lemma mhi_34 (c s p q r : ℝ) (hb : InBox c s p q r) : c ^ 2 * s ^ 2 * p ^ 0 * q ^ 0 * r ^ 0 ≤ (215932199 / 2500000000 : ℝ) :=
  mon_hi c s p q r hb 2 2 0 0 0 _ (by norm_num)
lemma mlo_35 (c s p q r : ℝ) (hb : InBox c s p q r) : (152687107 / 10000000000 : ℝ) ≤ c ^ 2 * s ^ 2 * p ^ 0 * q ^ 0 * r ^ 5 :=
  mon_lo c s p q r hb 2 2 0 0 5 _ (by norm_num)
lemma mhi_35 (c s p q r : ℝ) (hb : InBox c s p q r) : c ^ 2 * s ^ 2 * p ^ 0 * q ^ 0 * r ^ 5 ≤ (38171783 / 2500000000 : ℝ) :=
  mon_hi c s p q r hb 2 2 0 0 5 _ (by norm_num)
lemma mlo_36 (c s p q r : ℝ) (hb : InBox c s p q r) : (8672329 / 2500000000 : ℝ) ≤ c ^ 2 * s ^ 2 * p ^ 0 * q ^ 5 * r ^ 0 :=
  mon_lo c s p q r hb 2 2 0 5 0 _ (by norm_num)
lemma mhi_36 (c s p q r : ℝ) (hb : InBox c s p q r) : c ^ 2 * s ^ 2 * p ^ 0 * q ^ 5 * r ^ 0 ≤ (8672331 / 2500000000 : ℝ) :=
  mon_hi c s p q r hb 2 2 0 5 0 _ (by norm_num)
lemma mlo_37 (c s p q r : ℝ) (hb : InBox c s p q r) : (384710407 / 10000000000 : ℝ) ≤ c ^ 2 * s ^ 2 * p ^ 5 * q ^ 0 * r ^ 0 :=
  mon_lo c s p q r hb 2 2 5 0 0 _ (by norm_num)
lemma mhi_37 (c s p q r : ℝ) (hb : InBox c s p q r) : c ^ 2 * s ^ 2 * p ^ 5 * q ^ 0 * r ^ 0 ≤ (384710463 / 10000000000 : ℝ) :=
  mon_hi c s p q r hb 2 2 5 0 0 _ (by norm_num)
lemma enc_0 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (21338030157 / 10000000000 : ℝ) ≤ CP_0 c s p q r ∧ CP_0 c s p q r ≤ (21338030631 / 10000000000 : ℝ) := by
  have a2 := mlo_2 c s p q r hb
  have b2 := mhi_2 c s p q r hb
  have a3 := mlo_3 c s p q r hb
  have b3 := mhi_3 c s p q r hb
  have a16 := mlo_16 c s p q r hb
  have b16 := mhi_16 c s p q r hb
  have a17 := mlo_17 c s p q r hb
  have b17 := mhi_17 c s p q r hb
  have a18 := mlo_18 c s p q r hb
  have b18 := mhi_18 c s p q r hb
  have a29 := mlo_29 c s p q r hb
  have b29 := mhi_29 c s p q r hb
  have a30 := mlo_30 c s p q r hb
  have b30 := mhi_30 c s p q r hb
  unfold CP_0
  constructor <;> linarith
lemma enc_1 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (1285564049 / 1250000000 : ℝ) ≤ CP_1 c s p q r ∧ CP_1 c s p q r ≤ (2571128247 / 2500000000 : ℝ) := by
  have a4 := mlo_4 c s p q r hb
  have b4 := mhi_4 c s p q r hb
  have a19 := mlo_19 c s p q r hb
  have b19 := mhi_19 c s p q r hb
  unfold CP_1
  constructor <;> linarith
lemma enc_2 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (478325869 / 10000000000 : ℝ) ≤ CP_2 c s p q r ∧ CP_2 c s p q r ≤ (23916303 / 500000000 : ℝ) := by
  have a2 := mlo_2 c s p q r hb
  have b2 := mhi_2 c s p q r hb
  have a3 := mlo_3 c s p q r hb
  have b3 := mhi_3 c s p q r hb
  have a17 := mlo_17 c s p q r hb
  have b17 := mhi_17 c s p q r hb
  unfold CP_2
  constructor <;> linarith
lemma enc_3 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (55242717 / 156250000 : ℝ) ≤ CP_3 c s p q r ∧ CP_3 c s p q r ≤ (3535534039 / 10000000000 : ℝ) := by
  have a0 := mlo_0 c s p q r hb
  have b0 := mhi_0 c s p q r hb
  unfold CP_3
  constructor <;> linarith
lemma enc_4 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (15887974301 / 5000000000 : ℝ) ≤ CP_4 c s p q r ∧ CP_4 c s p q r ≤ (31775949877 / 10000000000 : ℝ) := by
  have a2 := mlo_2 c s p q r hb
  have b2 := mhi_2 c s p q r hb
  have a13 := mlo_13 c s p q r hb
  have b13 := mhi_13 c s p q r hb
  have a16 := mlo_16 c s p q r hb
  have b16 := mhi_16 c s p q r hb
  have a18 := mlo_18 c s p q r hb
  have b18 := mhi_18 c s p q r hb
  have a36 := mlo_36 c s p q r hb
  have b36 := mhi_36 c s p q r hb
  unfold CP_4
  constructor <;> linarith
lemma enc_5 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (-25334057577 / 10000000000 : ℝ) ≤ CP_5 c s p q r ∧ CP_5 c s p q r ≤ (-6333514073 / 2500000000 : ℝ) := by
  have a6 := mlo_6 c s p q r hb
  have b6 := mhi_6 c s p q r hb
  have a9 := mlo_9 c s p q r hb
  have b9 := mhi_9 c s p q r hb
  unfold CP_5
  constructor <;> linarith
lemma enc_6 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (18516046493 / 10000000000 : ℝ) ≤ CP_6 c s p q r ∧ CP_6 c s p q r ≤ (18516047111 / 10000000000 : ℝ) := by
  have a4 := mlo_4 c s p q r hb
  have b4 := mhi_4 c s p q r hb
  have a14 := mlo_14 c s p q r hb
  have b14 := mhi_14 c s p q r hb
  unfold CP_6
  constructor <;> linarith
lemma enc_7 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (-11401603359 / 5000000000 : ℝ) ≤ CP_7 c s p q r ∧ CP_7 c s p q r ≤ (-11401602797 / 5000000000 : ℝ) := by
  have a20 := mlo_20 c s p q r hb
  have b20 := mhi_20 c s p q r hb
  have a22 := mlo_22 c s p q r hb
  have b22 := mhi_22 c s p q r hb
  unfold CP_7
  constructor <;> linarith
lemma enc_8 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (-15453797481 / 5000000000 : ℝ) ≤ CP_8 c s p q r ∧ CP_8 c s p q r ≤ (-15453797239 / 5000000000 : ℝ) := by
  have a2 := mlo_2 c s p q r hb
  have b2 := mhi_2 c s p q r hb
  have a14 := mlo_14 c s p q r hb
  have b14 := mhi_14 c s p q r hb
  unfold CP_8
  constructor <;> linarith
lemma enc_9 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (11401602797 / 5000000000 : ℝ) ≤ CP_9 c s p q r ∧ CP_9 c s p q r ≤ (11401603359 / 5000000000 : ℝ) := by
  have a20 := mlo_20 c s p q r hb
  have b20 := mhi_20 c s p q r hb
  have a22 := mlo_22 c s p q r hb
  have b22 := mhi_22 c s p q r hb
  unfold CP_9
  constructor <;> linarith
lemma enc_10 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (6333514073 / 2500000000 : ℝ) ≤ CP_10 c s p q r ∧ CP_10 c s p q r ≤ (25334057577 / 10000000000 : ℝ) := by
  have a6 := mlo_6 c s p q r hb
  have b6 := mhi_6 c s p q r hb
  have a9 := mlo_9 c s p q r hb
  have b9 := mhi_9 c s p q r hb
  unfold CP_10
  constructor <;> linarith
lemma enc_11 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (12288379109 / 5000000000 : ℝ) ≤ CP_11 c s p q r ∧ CP_11 c s p q r ≤ (24576758809 / 10000000000 : ℝ) := by
  have a1 := mlo_1 c s p q r hb
  have b1 := mhi_1 c s p q r hb
  have a2 := mlo_2 c s p q r hb
  have b2 := mhi_2 c s p q r hb
  have a16 := mlo_16 c s p q r hb
  have b16 := mhi_16 c s p q r hb
  have a18 := mlo_18 c s p q r hb
  have b18 := mhi_18 c s p q r hb
  unfold CP_11
  constructor <;> linarith
lemma enc_12 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (-17348349593 / 5000000000 : ℝ) ≤ CP_12 c s p q r ∧ CP_12 c s p q r ≤ (-4337087351 / 1250000000 : ℝ) := by
  have a1 := mlo_1 c s p q r hb
  have b1 := mhi_1 c s p q r hb
  unfold CP_12
  constructor <;> linarith
lemma enc_13 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (4337087351 / 1250000000 : ℝ) ≤ CP_13 c s p q r ∧ CP_13 c s p q r ≤ (17348349593 / 5000000000 : ℝ) := by
  have a1 := mlo_1 c s p q r hb
  have b1 := mhi_1 c s p q r hb
  unfold CP_13
  constructor <;> linarith
lemma enc_14 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (961850497 / 312500000 : ℝ) ≤ CP_14 c s p q r ∧ CP_14 c s p q r ≤ (30779217449 / 10000000000 : ℝ) := by
  have a2 := mlo_2 c s p q r hb
  have b2 := mhi_2 c s p q r hb
  have a3 := mlo_3 c s p q r hb
  have b3 := mhi_3 c s p q r hb
  have a5 := mlo_5 c s p q r hb
  have b5 := mhi_5 c s p q r hb
  have a10 := mlo_10 c s p q r hb
  have b10 := mhi_10 c s p q r hb
  have a16 := mlo_16 c s p q r hb
  have b16 := mhi_16 c s p q r hb
  have a17 := mlo_17 c s p q r hb
  have b17 := mhi_17 c s p q r hb
  have a18 := mlo_18 c s p q r hb
  have b18 := mhi_18 c s p q r hb
  have a19 := mlo_19 c s p q r hb
  have b19 := mhi_19 c s p q r hb
  have a27 := mlo_27 c s p q r hb
  have b27 := mhi_27 c s p q r hb
  have a29 := mlo_29 c s p q r hb
  have b29 := mhi_29 c s p q r hb
  have a30 := mlo_30 c s p q r hb
  have b30 := mhi_30 c s p q r hb
  unfold CP_14
  constructor <;> linarith
lemma enc_15 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (-306762759 / 500000000 : ℝ) ≤ CP_15 c s p q r ∧ CP_15 c s p q r ≤ (-3067627203 / 5000000000 : ℝ) := by
  have a23 := mlo_23 c s p q r hb
  have b23 := mhi_23 c s p q r hb
  have a32 := mlo_32 c s p q r hb
  have b32 := mhi_32 c s p q r hb
  have a33 := mlo_33 c s p q r hb
  have b33 := mhi_33 c s p q r hb
  unfold CP_15
  constructor <;> linarith
lemma enc_16 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (12587748421 / 5000000000 : ℝ) ≤ CP_16 c s p q r ∧ CP_16 c s p q r ≤ (25175498609 / 10000000000 : ℝ) := by
  have a4 := mlo_4 c s p q r hb
  have b4 := mhi_4 c s p q r hb
  have a19 := mlo_19 c s p q r hb
  have b19 := mhi_19 c s p q r hb
  have a24 := mlo_24 c s p q r hb
  have b24 := mhi_24 c s p q r hb
  have a30 := mlo_30 c s p q r hb
  have b30 := mhi_30 c s p q r hb
  unfold CP_16
  constructor <;> linarith
lemma enc_17 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (10247840919 / 5000000000 : ℝ) ≤ CP_17 c s p q r ∧ CP_17 c s p q r ≤ (20495683391 / 10000000000 : ℝ) := by
  have a6 := mlo_6 c s p q r hb
  have b6 := mhi_6 c s p q r hb
  have a9 := mlo_9 c s p q r hb
  have b9 := mhi_9 c s p q r hb
  have a20 := mlo_20 c s p q r hb
  have b20 := mhi_20 c s p q r hb
  have a23 := mlo_23 c s p q r hb
  have b23 := mhi_23 c s p q r hb
  unfold CP_17
  constructor <;> linarith
lemma enc_18 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (-21208812479 / 10000000000 : ℝ) ≤ CP_18 c s p q r ∧ CP_18 c s p q r ≤ (-21208811147 / 10000000000 : ℝ) := by
  have a2 := mlo_2 c s p q r hb
  have b2 := mhi_2 c s p q r hb
  have a17 := mlo_17 c s p q r hb
  have b17 := mhi_17 c s p q r hb
  have a24 := mlo_24 c s p q r hb
  have b24 := mhi_24 c s p q r hb
  have a29 := mlo_29 c s p q r hb
  have b29 := mhi_29 c s p q r hb
  unfold CP_18
  constructor <;> linarith
lemma enc_19 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (14924891967 / 5000000000 : ℝ) ≤ CP_19 c s p q r ∧ CP_19 c s p q r ≤ (14924892379 / 5000000000 : ℝ) := by
  have a6 := mlo_6 c s p q r hb
  have b6 := mhi_6 c s p q r hb
  have a8 := mlo_8 c s p q r hb
  have b8 := mhi_8 c s p q r hb
  have a20 := mlo_20 c s p q r hb
  have b20 := mhi_20 c s p q r hb
  have a22 := mlo_22 c s p q r hb
  have b22 := mhi_22 c s p q r hb
  unfold CP_19
  constructor <;> linarith
lemma enc_20 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (-34612200439 / 10000000000 : ℝ) ≤ CP_20 c s p q r ∧ CP_20 c s p q r ≤ (-34612199567 / 10000000000 : ℝ) := by
  have a2 := mlo_2 c s p q r hb
  have b2 := mhi_2 c s p q r hb
  have a10 := mlo_10 c s p q r hb
  have b10 := mhi_10 c s p q r hb
  have a29 := mlo_29 c s p q r hb
  have b29 := mhi_29 c s p q r hb
  unfold CP_20
  constructor <;> linarith
lemma enc_21 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (-11401603359 / 10000000000 : ℝ) ≤ CP_21 c s p q r ∧ CP_21 c s p q r ≤ (-11401602797 / 10000000000 : ℝ) := by
  have a20 := mlo_20 c s p q r hb
  have b20 := mhi_20 c s p q r hb
  have a22 := mlo_22 c s p q r hb
  have b22 := mhi_22 c s p q r hb
  unfold CP_21
  constructor <;> linarith
lemma enc_22 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (5583690581 / 2500000000 : ℝ) ≤ CP_22 c s p q r ∧ CP_22 c s p q r ≤ (11167381747 / 5000000000 : ℝ) := by
  have a2 := mlo_2 c s p q r hb
  have b2 := mhi_2 c s p q r hb
  have a10 := mlo_10 c s p q r hb
  have b10 := mhi_10 c s p q r hb
  have a12 := mlo_12 c s p q r hb
  have b12 := mhi_12 c s p q r hb
  have a16 := mlo_16 c s p q r hb
  have b16 := mhi_16 c s p q r hb
  have a18 := mlo_18 c s p q r hb
  have b18 := mhi_18 c s p q r hb
  have a27 := mlo_27 c s p q r hb
  have b27 := mhi_27 c s p q r hb
  have a36 := mlo_36 c s p q r hb
  have b36 := mhi_36 c s p q r hb
  have a37 := mlo_37 c s p q r hb
  have b37 := mhi_37 c s p q r hb
  unfold CP_22
  constructor <;> linarith
lemma enc_23 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (-2419187399 / 5000000000 : ℝ) ≤ CP_23 c s p q r ∧ CP_23 c s p q r ≤ (-1209593479 / 2500000000 : ℝ) := by
  have a31 := mlo_31 c s p q r hb
  have b31 := mhi_31 c s p q r hb
  have a33 := mlo_33 c s p q r hb
  have b33 := mhi_33 c s p q r hb
  unfold CP_23
  constructor <;> linarith
lemma enc_24 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (3625060923 / 10000000000 : ℝ) ≤ CP_24 c s p q r ∧ CP_24 c s p q r ≤ (3625062429 / 10000000000 : ℝ) := by
  have a4 := mlo_4 c s p q r hb
  have b4 := mhi_4 c s p q r hb
  have a14 := mlo_14 c s p q r hb
  have b14 := mhi_14 c s p q r hb
  have a26 := mlo_26 c s p q r hb
  have b26 := mhi_26 c s p q r hb
  have a27 := mlo_27 c s p q r hb
  have b27 := mhi_27 c s p q r hb
  unfold CP_24
  constructor <;> linarith
lemma enc_25 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (3523288973 / 5000000000 : ℝ) ≤ CP_25 c s p q r ∧ CP_25 c s p q r ≤ (352328927 / 500000000 : ℝ) := by
  have a31 := mlo_31 c s p q r hb
  have b31 := mhi_31 c s p q r hb
  have a32 := mlo_32 c s p q r hb
  have b32 := mhi_32 c s p q r hb
  unfold CP_25
  constructor <;> linarith
lemma enc_26 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (-36881829 / 40000000 : ℝ) ≤ CP_26 c s p q r ∧ CP_26 c s p q r ≤ (-922045661 / 1000000000 : ℝ) := by
  have a2 := mlo_2 c s p q r hb
  have b2 := mhi_2 c s p q r hb
  have a14 := mlo_14 c s p q r hb
  have b14 := mhi_14 c s p q r hb
  have a25 := mlo_25 c s p q r hb
  have b25 := mhi_25 c s p q r hb
  have a27 := mlo_27 c s p q r hb
  have b27 := mhi_27 c s p q r hb
  unfold CP_26
  constructor <;> linarith
lemma enc_27 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (11401602797 / 10000000000 : ℝ) ≤ CP_27 c s p q r ∧ CP_27 c s p q r ≤ (11401603359 / 10000000000 : ℝ) := by
  have a20 := mlo_20 c s p q r hb
  have b20 := mhi_20 c s p q r hb
  have a22 := mlo_22 c s p q r hb
  have b22 := mhi_22 c s p q r hb
  unfold CP_27
  constructor <;> linarith
lemma enc_28 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (4182931157 / 10000000000 : ℝ) ≤ CP_28 c s p q r ∧ CP_28 c s p q r ≤ (4182931621 / 10000000000 : ℝ) := by
  have a2 := mlo_2 c s p q r hb
  have b2 := mhi_2 c s p q r hb
  have a12 := mlo_12 c s p q r hb
  have b12 := mhi_12 c s p q r hb
  have a27 := mlo_27 c s p q r hb
  have b27 := mhi_27 c s p q r hb
  unfold CP_28
  constructor <;> linarith
lemma enc_29 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (6144189481 / 2500000000 : ℝ) ≤ CP_29 c s p q r ∧ CP_29 c s p q r ≤ (24576759021 / 10000000000 : ℝ) := by
  have a1 := mlo_1 c s p q r hb
  have b1 := mhi_1 c s p q r hb
  have a2 := mlo_2 c s p q r hb
  have b2 := mhi_2 c s p q r hb
  have a10 := mlo_10 c s p q r hb
  have b10 := mhi_10 c s p q r hb
  have a16 := mlo_16 c s p q r hb
  have b16 := mhi_16 c s p q r hb
  have a18 := mlo_18 c s p q r hb
  have b18 := mhi_18 c s p q r hb
  have a27 := mlo_27 c s p q r hb
  have b27 := mhi_27 c s p q r hb
  unfold CP_29
  constructor <;> linarith
lemma enc_30 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (18516045801 / 10000000000 : ℝ) ≤ CP_30 c s p q r ∧ CP_30 c s p q r ≤ (18516047667 / 10000000000 : ℝ) := by
  have a4 := mlo_4 c s p q r hb
  have b4 := mhi_4 c s p q r hb
  have a14 := mlo_14 c s p q r hb
  have b14 := mhi_14 c s p q r hb
  have a24 := mlo_24 c s p q r hb
  have b24 := mhi_24 c s p q r hb
  have a27 := mlo_27 c s p q r hb
  have b27 := mhi_27 c s p q r hb
  unfold CP_30
  constructor <;> linarith
lemma enc_31 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (-15453797787 / 5000000000 : ℝ) ≤ CP_31 c s p q r ∧ CP_31 c s p q r ≤ (-15453796921 / 5000000000 : ℝ) := by
  have a2 := mlo_2 c s p q r hb
  have b2 := mhi_2 c s p q r hb
  have a14 := mlo_14 c s p q r hb
  have b14 := mhi_14 c s p q r hb
  have a24 := mlo_24 c s p q r hb
  have b24 := mhi_24 c s p q r hb
  have a27 := mlo_27 c s p q r hb
  have b27 := mhi_27 c s p q r hb
  unfold CP_31
  constructor <;> linarith
lemma enc_32 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (-3090759513 / 1000000000 : ℝ) ≤ CP_32 c s p q r ∧ CP_32 c s p q r ≤ (-15453797017 / 5000000000 : ℝ) := by
  have a2 := mlo_2 c s p q r hb
  have b2 := mhi_2 c s p q r hb
  have a10 := mlo_10 c s p q r hb
  have b10 := mhi_10 c s p q r hb
  have a27 := mlo_27 c s p q r hb
  have b27 := mhi_27 c s p q r hb
  unfold CP_32
  constructor <;> linarith
lemma enc_33 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (-5360934973 / 5000000000 : ℝ) ≤ CP_33 c s p q r ∧ CP_33 c s p q r ≤ (-17154991 / 16000000 : ℝ) := by
  have a14 := mlo_14 c s p q r hb
  have b14 := mhi_14 c s p q r hb
  have a15 := mlo_15 c s p q r hb
  have b15 := mhi_15 c s p q r hb
  unfold CP_33
  constructor <;> linarith
lemma enc_34 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (-16499261019 / 5000000000 : ℝ) ≤ CP_34 c s p q r ∧ CP_34 c s p q r ≤ (-4124815153 / 1250000000 : ℝ) := by
  have a6 := mlo_6 c s p q r hb
  have b6 := mhi_6 c s p q r hb
  have a7 := mlo_7 c s p q r hb
  have b7 := mhi_7 c s p q r hb
  unfold CP_34
  constructor <;> linarith
lemma enc_35 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (17154991 / 16000000 : ℝ) ≤ CP_35 c s p q r ∧ CP_35 c s p q r ≤ (5360934973 / 5000000000 : ℝ) := by
  have a14 := mlo_14 c s p q r hb
  have b14 := mhi_14 c s p q r hb
  have a15 := mlo_15 c s p q r hb
  have b15 := mhi_15 c s p q r hb
  unfold CP_35
  constructor <;> linarith
lemma enc_36 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (4124815153 / 1250000000 : ℝ) ≤ CP_36 c s p q r ∧ CP_36 c s p q r ≤ (16499261019 / 5000000000 : ℝ) := by
  have a6 := mlo_6 c s p q r hb
  have b6 := mhi_6 c s p q r hb
  have a7 := mlo_7 c s p q r hb
  have b7 := mhi_7 c s p q r hb
  unfold CP_36
  constructor <;> linarith
lemma enc_37 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (12472120941 / 5000000000 : ℝ) ≤ CP_37 c s p q r ∧ CP_37 c s p q r ≤ (24944243537 / 10000000000 : ℝ) := by
  have a2 := mlo_2 c s p q r hb
  have b2 := mhi_2 c s p q r hb
  have a3 := mlo_3 c s p q r hb
  have b3 := mhi_3 c s p q r hb
  have a5 := mlo_5 c s p q r hb
  have b5 := mhi_5 c s p q r hb
  have a14 := mlo_14 c s p q r hb
  have b14 := mhi_14 c s p q r hb
  have a16 := mlo_16 c s p q r hb
  have b16 := mhi_16 c s p q r hb
  have a18 := mlo_18 c s p q r hb
  have b18 := mhi_18 c s p q r hb
  have a19 := mlo_19 c s p q r hb
  have b19 := mhi_19 c s p q r hb
  have a27 := mlo_27 c s p q r hb
  have b27 := mhi_27 c s p q r hb
  have a29 := mlo_29 c s p q r hb
  have b29 := mhi_29 c s p q r hb
  have a30 := mlo_30 c s p q r hb
  have b30 := mhi_30 c s p q r hb
  have a34 := mlo_34 c s p q r hb
  have b34 := mhi_34 c s p q r hb
  unfold CP_37
  constructor <;> linarith
lemma enc_38 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (9927050187 / 10000000000 : ℝ) ≤ CP_38 c s p q r ∧ CP_38 c s p q r ≤ (79416411 / 80000000 : ℝ) := by
  have a22 := mlo_22 c s p q r hb
  have b22 := mhi_22 c s p q r hb
  have a23 := mlo_23 c s p q r hb
  have b23 := mhi_23 c s p q r hb
  have a33 := mlo_33 c s p q r hb
  have b33 := mhi_33 c s p q r hb
  unfold CP_38
  constructor <;> linarith
lemma enc_39 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (1081376697 / 10000000000 : ℝ) ≤ CP_39 c s p q r ∧ CP_39 c s p q r ≤ (21627577 / 200000000 : ℝ) := by
  have a4 := mlo_4 c s p q r hb
  have b4 := mhi_4 c s p q r hb
  have a5 := mlo_5 c s p q r hb
  have b5 := mhi_5 c s p q r hb
  have a19 := mlo_19 c s p q r hb
  have b19 := mhi_19 c s p q r hb
  have a30 := mlo_30 c s p q r hb
  have b30 := mhi_30 c s p q r hb
  have a34 := mlo_34 c s p q r hb
  have b34 := mhi_34 c s p q r hb
  unfold CP_39
  constructor <;> linarith
lemma enc_40 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (1583378451 / 1250000000 : ℝ) ≤ CP_40 c s p q r ∧ CP_40 c s p q r ≤ (63335147 / 50000000 : ℝ) := by
  have a20 := mlo_20 c s p q r hb
  have b20 := mhi_20 c s p q r hb
  have a23 := mlo_23 c s p q r hb
  have b23 := mhi_23 c s p q r hb
  have a31 := mlo_31 c s p q r hb
  have b31 := mhi_31 c s p q r hb
  have a33 := mlo_33 c s p q r hb
  have b33 := mhi_33 c s p q r hb
  unfold CP_40
  constructor <;> linarith
lemma enc_41 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (-352328927 / 500000000 : ℝ) ≤ CP_41 c s p q r ∧ CP_41 c s p q r ≤ (-3523288973 / 5000000000 : ℝ) := by
  have a31 := mlo_31 c s p q r hb
  have b31 := mhi_31 c s p q r hb
  have a32 := mlo_32 c s p q r hb
  have b32 := mhi_32 c s p q r hb
  unfold CP_41
  constructor <;> linarith
lemma enc_42 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (5633947199 / 2000000000 : ℝ) ≤ CP_42 c s p q r ∧ CP_42 c s p q r ≤ (14084869009 / 5000000000 : ℝ) := by
  have a2 := mlo_2 c s p q r hb
  have b2 := mhi_2 c s p q r hb
  have a12 := mlo_12 c s p q r hb
  have b12 := mhi_12 c s p q r hb
  have a13 := mlo_13 c s p q r hb
  have b13 := mhi_13 c s p q r hb
  have a14 := mlo_14 c s p q r hb
  have b14 := mhi_14 c s p q r hb
  have a16 := mlo_16 c s p q r hb
  have b16 := mhi_16 c s p q r hb
  have a18 := mlo_18 c s p q r hb
  have b18 := mhi_18 c s p q r hb
  have a27 := mlo_27 c s p q r hb
  have b27 := mhi_27 c s p q r hb
  have a34 := mlo_34 c s p q r hb
  have b34 := mhi_34 c s p q r hb
  have a37 := mlo_37 c s p q r hb
  have b37 := mhi_37 c s p q r hb
  unfold CP_42
  constructor <;> linarith
lemma enc_43 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (-63335147 / 50000000 : ℝ) ≤ CP_43 c s p q r ∧ CP_43 c s p q r ≤ (-1583378451 / 1250000000 : ℝ) := by
  have a20 := mlo_20 c s p q r hb
  have b20 := mhi_20 c s p q r hb
  have a23 := mlo_23 c s p q r hb
  have b23 := mhi_23 c s p q r hb
  have a31 := mlo_31 c s p q r hb
  have b31 := mhi_31 c s p q r hb
  have a33 := mlo_33 c s p q r hb
  have b33 := mhi_33 c s p q r hb
  unfold CP_43
  constructor <;> linarith
lemma enc_44 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (27719180941 / 10000000000 : ℝ) ≤ CP_44 c s p q r ∧ CP_44 c s p q r ≤ (27719182479 / 10000000000 : ℝ) := by
  have a4 := mlo_4 c s p q r hb
  have b4 := mhi_4 c s p q r hb
  have a14 := mlo_14 c s p q r hb
  have b14 := mhi_14 c s p q r hb
  have a27 := mlo_27 c s p q r hb
  have b27 := mhi_27 c s p q r hb
  have a37 := mlo_37 c s p q r hb
  have b37 := mhi_37 c s p q r hb
  unfold CP_44
  constructor <;> linarith
lemma enc_45 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (-14924892379 / 5000000000 : ℝ) ≤ CP_45 c s p q r ∧ CP_45 c s p q r ≤ (-14924891967 / 5000000000 : ℝ) := by
  have a6 := mlo_6 c s p q r hb
  have b6 := mhi_6 c s p q r hb
  have a8 := mlo_8 c s p q r hb
  have b8 := mhi_8 c s p q r hb
  have a20 := mlo_20 c s p q r hb
  have b20 := mhi_20 c s p q r hb
  have a22 := mlo_22 c s p q r hb
  have b22 := mhi_22 c s p q r hb
  unfold CP_45
  constructor <;> linarith
lemma enc_46 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (6144189447 / 2500000000 : ℝ) ≤ CP_46 c s p q r ∧ CP_46 c s p q r ≤ (24576759303 / 10000000000 : ℝ) := by
  have a1 := mlo_1 c s p q r hb
  have b1 := mhi_1 c s p q r hb
  have a2 := mlo_2 c s p q r hb
  have b2 := mhi_2 c s p q r hb
  have a14 := mlo_14 c s p q r hb
  have b14 := mhi_14 c s p q r hb
  have a16 := mlo_16 c s p q r hb
  have b16 := mhi_16 c s p q r hb
  have a18 := mlo_18 c s p q r hb
  have b18 := mhi_18 c s p q r hb
  have a27 := mlo_27 c s p q r hb
  have b27 := mhi_27 c s p q r hb
  have a34 := mlo_34 c s p q r hb
  have b34 := mhi_34 c s p q r hb
  unfold CP_46
  constructor <;> linarith
lemma enc_47 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (18516045761 / 10000000000 : ℝ) ≤ CP_47 c s p q r ∧ CP_47 c s p q r ≤ (18516047827 / 10000000000 : ℝ) := by
  have a4 := mlo_4 c s p q r hb
  have b4 := mhi_4 c s p q r hb
  have a14 := mlo_14 c s p q r hb
  have b14 := mhi_14 c s p q r hb
  have a27 := mlo_27 c s p q r hb
  have b27 := mhi_27 c s p q r hb
  have a34 := mlo_34 c s p q r hb
  have b34 := mhi_34 c s p q r hb
  unfold CP_47
  constructor <;> linarith
lemma enc_48 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (28070218779 / 10000000000 : ℝ) ≤ CP_48 c s p q r ∧ CP_48 c s p q r ≤ (28070219539 / 10000000000 : ℝ) := by
  have a1 := mlo_1 c s p q r hb
  have b1 := mhi_1 c s p q r hb
  have a14 := mlo_14 c s p q r hb
  have b14 := mhi_14 c s p q r hb
  have a15 := mlo_15 c s p q r hb
  have b15 := mhi_15 c s p q r hb
  unfold CP_48
  constructor <;> linarith
lemma enc_49 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (-10197104337 / 5000000000 : ℝ) ≤ CP_49 c s p q r ∧ CP_49 c s p q r ≤ (-10197103649 / 5000000000 : ℝ) := by
  have a20 := mlo_20 c s p q r hb
  have b20 := mhi_20 c s p q r hb
  have a21 := mlo_21 c s p q r hb
  have b21 := mhi_21 c s p q r hb
  unfold CP_49
  constructor <;> linarith
lemma enc_50 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (-28070219539 / 10000000000 : ℝ) ≤ CP_50 c s p q r ∧ CP_50 c s p q r ≤ (-28070218779 / 10000000000 : ℝ) := by
  have a1 := mlo_1 c s p q r hb
  have b1 := mhi_1 c s p q r hb
  have a14 := mlo_14 c s p q r hb
  have b14 := mhi_14 c s p q r hb
  have a15 := mlo_15 c s p q r hb
  have b15 := mhi_15 c s p q r hb
  unfold CP_50
  constructor <;> linarith
lemma enc_51 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (10197103649 / 5000000000 : ℝ) ≤ CP_51 c s p q r ∧ CP_51 c s p q r ≤ (10197104337 / 5000000000 : ℝ) := by
  have a20 := mlo_20 c s p q r hb
  have b20 := mhi_20 c s p q r hb
  have a21 := mlo_21 c s p q r hb
  have b21 := mhi_21 c s p q r hb
  unfold CP_51
  constructor <;> linarith
lemma enc_52 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (-79416411 / 80000000 : ℝ) ≤ CP_52 c s p q r ∧ CP_52 c s p q r ≤ (-9927050187 / 10000000000 : ℝ) := by
  have a22 := mlo_22 c s p q r hb
  have b22 := mhi_22 c s p q r hb
  have a23 := mlo_23 c s p q r hb
  have b23 := mhi_23 c s p q r hb
  have a33 := mlo_33 c s p q r hb
  have b33 := mhi_33 c s p q r hb
  unfold CP_52
  constructor <;> linarith
lemma enc_53 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (1209593479 / 2500000000 : ℝ) ≤ CP_53 c s p q r ∧ CP_53 c s p q r ≤ (2419187399 / 5000000000 : ℝ) := by
  have a31 := mlo_31 c s p q r hb
  have b31 := mhi_31 c s p q r hb
  have a33 := mlo_33 c s p q r hb
  have b33 := mhi_33 c s p q r hb
  unfold CP_53
  constructor <;> linarith
lemma enc_54 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (-20495683391 / 10000000000 : ℝ) ≤ CP_54 c s p q r ∧ CP_54 c s p q r ≤ (-10247840919 / 5000000000 : ℝ) := by
  have a6 := mlo_6 c s p q r hb
  have b6 := mhi_6 c s p q r hb
  have a9 := mlo_9 c s p q r hb
  have b9 := mhi_9 c s p q r hb
  have a20 := mlo_20 c s p q r hb
  have b20 := mhi_20 c s p q r hb
  have a23 := mlo_23 c s p q r hb
  have b23 := mhi_23 c s p q r hb
  unfold CP_54
  constructor <;> linarith
lemma enc_55 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (3067627203 / 5000000000 : ℝ) ≤ CP_55 c s p q r ∧ CP_55 c s p q r ≤ (306762759 / 500000000 : ℝ) := by
  have a23 := mlo_23 c s p q r hb
  have b23 := mhi_23 c s p q r hb
  have a32 := mlo_32 c s p q r hb
  have b32 := mhi_32 c s p q r hb
  have a33 := mlo_33 c s p q r hb
  have b33 := mhi_33 c s p q r hb
  unfold CP_55
  constructor <;> linarith
lemma enc_56 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (681353149 / 250000000 : ℝ) ≤ CP_56 c s p q r ∧ CP_56 c s p q r ≤ (27254126559 / 10000000000 : ℝ) := by
  have a1 := mlo_1 c s p q r hb
  have b1 := mhi_1 c s p q r hb
  have a15 := mlo_15 c s p q r hb
  have b15 := mhi_15 c s p q r hb
  have a28 := mlo_28 c s p q r hb
  have b28 := mhi_28 c s p q r hb
  unfold CP_56
  constructor <;> linarith
lemma enc_57 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (-31 / 8 : ℝ) ≤ CP_57 c s p q r ∧ CP_57 c s p q r ≤ (-31 / 8 : ℝ) := by

  unfold CP_57
  constructor <;> linarith
lemma enc_58 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (27254125869 / 10000000000 : ℝ) ≤ CP_58 c s p q r ∧ CP_58 c s p q r ≤ (27254126613 / 10000000000 : ℝ) := by
  have a11 := mlo_11 c s p q r hb
  have b11 := mhi_11 c s p q r hb
  have a35 := mlo_35 c s p q r hb
  have b35 := mhi_35 c s p q r hb
  unfold CP_58
  constructor <;> linarith
lemma enc_59 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (135 / 64 : ℝ) ≤ CP_59 c s p q r ∧ CP_59 c s p q r ≤ (135 / 64 : ℝ) := by

  unfold CP_59
  constructor <;> linarith
lemma enc_60 (c s p q r : ℝ) (hb : InBox c s p q r) :
    (1 / 32 : ℝ) ≤ CP_60 c s p q r ∧ CP_60 c s p q r ≤ (1 / 32 : ℝ) := by

  unfold CP_60
  constructor <;> linarith
lemma kk_0_0 (C u : ℝ) (h1 : (21338030157 / 10000000000 : ℝ) ≤ C) (h2 : C ≤ (21338030631 / 10000000000 : ℝ)) :
    0 ≤ (C - (13336269 / 6250000 : ℝ)) * u ^ 2 + (243 / 10000000000 : ℝ) * u ^ 2 :=
  diag_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_0_3 (C u v : ℝ) (h1 : (1285564049 / 1250000000 : ℝ) ≤ C) (h2 : C ≤ (2571128247 / 2500000000 : ℝ)) :
    0 ≤ (C - (20086939093809 / 19531250000000 : ℝ)) * (u * v) + (10601 / 250000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_0_6 (C u v : ℝ) (h1 : (478325869 / 10000000000 : ℝ) ≤ C) (h2 : C ≤ (23916303 / 500000000 : ℝ)) :
    0 ≤ (C - (467115022641 / 9765625000000 : ℝ)) * (u * v) + (13841 / 500000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_0_9 (C u v : ℝ) (h1 : (478325869 / 10000000000 : ℝ) ≤ C) (h2 : C ≤ (23916303 / 500000000 : ℝ)) :
    0 ≤ (C - (467115022641 / 9765625000000 : ℝ)) * (u * v) + (13841 / 500000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_0_12 (C u v : ℝ) (h1 : (1285564049 / 1250000000 : ℝ) ≤ C) (h2 : C ≤ (2571128247 / 2500000000 : ℝ)) :
    0 ≤ (C - (20086939093809 / 19531250000000 : ℝ)) * (u * v) + (10601 / 250000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_0_15 (C u v : ℝ) (h1 : (55242717 / 156250000 : ℝ) ≤ C) (h2 : C ≤ (3535534039 / 10000000000 : ℝ)) :
    0 ≤ (C - (1726334934957 / 4882812500000 : ℝ)) * (u * v) + (9221 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_0_18 (C u v : ℝ) (h1 : (55242717 / 156250000 : ℝ) ≤ C) (h2 : C ≤ (3535534039 / 10000000000 : ℝ)) :
    0 ≤ (C - (1726334934957 / 4882812500000 : ℝ)) * (u * v) + (9221 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_1_1 (C u : ℝ) (h1 : (15887974301 / 5000000000 : ℝ) ≤ C) (h2 : C ≤ (31775949877 / 10000000000 : ℝ)) :
    0 ≤ (C - (79439873 / 25000000 : ℝ)) * u ^ 2 + (677 / 10000000000 : ℝ) * u ^ 2 :=
  diag_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_1_3 (C u v : ℝ) (h1 : (-25334057577 / 10000000000 : ℝ) ≤ C) (h2 : C ≤ (-6333514073 / 2500000000 : ℝ)) :
    0 ≤ (C - (-1583378569430769 / 625000000000000 : ℝ)) * (u * v) + (8189 / 100000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_1_4 (C u v : ℝ) (h1 : (18516046493 / 10000000000 : ℝ) ≤ C) (h2 : C ≤ (18516047111 / 10000000000 : ℝ)) :
    0 ≤ (C - (578626471714307 / 312500000000000 : ℝ)) * (u * v) + (30093 / 500000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_1_6 (C u v : ℝ) (h1 : (-11401603359 / 5000000000 : ℝ) ≤ C) (h2 : C ≤ (-11401602797 / 5000000000 : ℝ)) :
    0 ≤ (C - (-2850400765248133 / 1250000000000000 : ℝ)) * (u * v) + (29801 / 500000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_1_7 (C u v : ℝ) (h1 : (-15453797481 / 5000000000 : ℝ) ≤ C) (h2 : C ≤ (-15453797239 / 5000000000 : ℝ)) :
    0 ≤ (C - (-19317246581349 / 6250000000000 : ℝ)) * (u * v) + (8637 / 200000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_1_9 (C u v : ℝ) (h1 : (11401602797 / 5000000000 : ℝ) ≤ C) (h2 : C ≤ (11401603359 / 5000000000 : ℝ)) :
    0 ≤ (C - (2850400765248133 / 1250000000000000 : ℝ)) * (u * v) + (29801 / 500000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_1_10 (C u v : ℝ) (h1 : (-15453797481 / 5000000000 : ℝ) ≤ C) (h2 : C ≤ (-15453797239 / 5000000000 : ℝ)) :
    0 ≤ (C - (-19317246581349 / 6250000000000 : ℝ)) * (u * v) + (8637 / 200000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_1_12 (C u v : ℝ) (h1 : (6333514073 / 2500000000 : ℝ) ≤ C) (h2 : C ≤ (25334057577 / 10000000000 : ℝ)) :
    0 ≤ (C - (1583378569430769 / 625000000000000 : ℝ)) * (u * v) + (8189 / 100000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_1_13 (C u v : ℝ) (h1 : (18516046493 / 10000000000 : ℝ) ≤ C) (h2 : C ≤ (18516047111 / 10000000000 : ℝ)) :
    0 ≤ (C - (578626471714307 / 312500000000000 : ℝ)) * (u * v) + (30093 / 500000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_1_16 (C u v : ℝ) (h1 : (55242717 / 156250000 : ℝ) ≤ C) (h2 : C ≤ (3535534039 / 10000000000 : ℝ)) :
    0 ≤ (C - (441941758976149 / 1250000000000000 : ℝ)) * (u * v) + (18381 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_1_19 (C u v : ℝ) (h1 : (55242717 / 156250000 : ℝ) ≤ C) (h2 : C ≤ (3535534039 / 10000000000 : ℝ)) :
    0 ≤ (C - (441941758976149 / 1250000000000000 : ℝ)) * (u * v) + (18381 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_2_2 (C u : ℝ) (h1 : (12288379109 / 5000000000 : ℝ) ≤ C) (h2 : C ≤ (24576758809 / 10000000000 : ℝ)) :
    0 ≤ (C - (49153517 / 20000000 : ℝ)) * u ^ 2 + (309 / 10000000000 : ℝ) * u ^ 2 :=
  diag_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_2_5 (C u v : ℝ) (h1 : (18516046493 / 10000000000 : ℝ) ≤ C) (h2 : C ≤ (18516047111 / 10000000000 : ℝ)) :
    0 ≤ (C - (1851604682680327 / 1000000000000000 : ℝ)) * (u * v) + (33381 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_2_8 (C u v : ℝ) (h1 : (-15453797481 / 5000000000 : ℝ) ≤ C) (h2 : C ≤ (-15453797239 / 5000000000 : ℝ)) :
    0 ≤ (C - (-1545379745803561 / 500000000000000 : ℝ)) * (u * v) + (1369 / 31250000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_2_11 (C u v : ℝ) (h1 : (-15453797481 / 5000000000 : ℝ) ≤ C) (h2 : C ≤ (-15453797239 / 5000000000 : ℝ)) :
    0 ≤ (C - (-1545379745803561 / 500000000000000 : ℝ)) * (u * v) + (1369 / 31250000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_2_14 (C u v : ℝ) (h1 : (18516046493 / 10000000000 : ℝ) ≤ C) (h2 : C ≤ (18516047111 / 10000000000 : ℝ)) :
    0 ≤ (C - (1851604682680327 / 1000000000000000 : ℝ)) * (u * v) + (33381 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_2_15 (C u v : ℝ) (h1 : (-17348349593 / 5000000000 : ℝ) ≤ C) (h2 : C ≤ (-4337087351 / 1250000000 : ℝ)) :
    0 ≤ (C - (-3469669919188157 / 1000000000000000 : ℝ)) * (u * v) + (38389 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_2_17 (C u v : ℝ) (h1 : (55242717 / 156250000 : ℝ) ≤ C) (h2 : C ≤ (3535534039 / 10000000000 : ℝ)) :
    0 ≤ (C - (70710684145019 / 200000000000000 : ℝ)) * (u * v) + (15963 / 500000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_2_18 (C u v : ℝ) (h1 : (4337087351 / 1250000000 : ℝ) ≤ C) (h2 : C ≤ (17348349593 / 5000000000 : ℝ)) :
    0 ≤ (C - (3469669919188157 / 1000000000000000 : ℝ)) * (u * v) + (38389 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_2_20 (C u v : ℝ) (h1 : (55242717 / 156250000 : ℝ) ≤ C) (h2 : C ≤ (3535534039 / 10000000000 : ℝ)) :
    0 ≤ (C - (70710684145019 / 200000000000000 : ℝ)) * (u * v) + (15963 / 500000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_3_3 (C u : ℝ) (h1 : (961850497 / 312500000 : ℝ) ≤ C) (h2 : C ≤ (30779217449 / 10000000000 : ℝ)) :
    0 ≤ (C - (192370103932589877124501 / 62500000000000000000000 : ℝ)) * u ^ 2 + (81979 / 1000000000000 : ℝ) * u ^ 2 :=
  diag_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_3_4 (C u v : ℝ) (h1 : (-306762759 / 500000000 : ℝ) ≤ C) (h2 : C ≤ (-3067627203 / 5000000000 : ℝ)) :
    0 ≤ (C - (-9586335544196943578271 / 15625000000000000000000 : ℝ)) * (u * v) + (10793 / 250000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_3_6 (C u v : ℝ) (h1 : (12587748421 / 5000000000 : ℝ) ≤ C) (h2 : C ≤ (25175498609 / 10000000000 : ℝ)) :
    0 ≤ (C - (157346860507025886428873 / 62500000000000000000000 : ℝ)) * (u * v) + (23197 / 250000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_3_7 (C u v : ℝ) (h1 : (10247840919 / 5000000000 : ℝ) ≤ C) (h2 : C ≤ (20495683391 / 10000000000 : ℝ)) :
    0 ≤ (C - (640490085476883601497 / 312500000000000000000 : ℝ)) * (u * v) + (89727 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_3_9 (C u v : ℝ) (h1 : (-21208812479 / 10000000000 : ℝ) ≤ C) (h2 : C ≤ (-21208811147 / 10000000000 : ℝ)) :
    0 ≤ (C - (-5302202992954262969329 / 2500000000000000000000 : ℝ)) * (u * v) + (41241 / 500000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_3_10 (C u v : ℝ) (h1 : (14924891967 / 5000000000 : ℝ) ≤ C) (h2 : C ≤ (14924892379 / 5000000000 : ℝ)) :
    0 ≤ (C - (932805763991654851497 / 312500000000000000000 : ℝ)) * (u * v) + (25687 / 500000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_3_12 (C u v : ℝ) (h1 : (-34612200439 / 10000000000 : ℝ) ≤ C) (h2 : C ≤ (-34612199567 / 10000000000 : ℝ)) :
    0 ≤ (C - (-108163125644305718517013 / 31250000000000000000000 : ℝ)) * (u * v) + (31959 / 500000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_3_13 (C u v : ℝ) (h1 : (-11401603359 / 10000000000 : ℝ) ≤ C) (h2 : C ≤ (-11401602797 / 10000000000 : ℝ)) :
    0 ≤ (C - (-17815004900904412328271 / 15625000000000000000000 : ℝ)) * (u * v) + (16979 / 500000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_3_15 (C u v : ℝ) (h1 : (55242717 / 156250000 : ℝ) ≤ C) (h2 : C ≤ (3535534039 / 10000000000 : ℝ)) :
    0 ≤ (C - (345266981399726427339 / 976562500000000000000 : ℝ)) * (u * v) + (14947 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_3_16 (u v : ℝ) :
    0 ≤ (0 - (-721769159775897 / 62500000000000000000000 : ℝ)) * (u * v) + (11549 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc (le_refl 0) (le_refl 0) (by norm_num) (by norm_num)
lemma kk_3_18 (C u v : ℝ) (h1 : (55242717 / 156250000 : ℝ) ≤ C) (h2 : C ≤ (3535534039 / 10000000000 : ℝ)) :
    0 ≤ (C - (345266981399726427339 / 976562500000000000000 : ℝ)) * (u * v) + (14947 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_3_19 (u v : ℝ) :
    0 ≤ (0 - (-721769159775897 / 62500000000000000000000 : ℝ)) * (u * v) + (11549 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc (le_refl 0) (le_refl 0) (by norm_num) (by norm_num)
lemma kk_4_4 (C u : ℝ) (h1 : (5583690581 / 2500000000 : ℝ) ≤ C) (h2 : C ≤ (11167381747 / 5000000000 : ℝ)) :
    0 ≤ (C - (69796134208169530658511 / 31250000000000000000000 : ℝ)) * u ^ 2 + (31131 / 500000000000 : ℝ) * u ^ 2 :=
  diag_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_4_6 (C u v : ℝ) (h1 : (-2419187399 / 5000000000 : ℝ) ≤ C) (h2 : C ≤ (-1209593479 / 2500000000 : ℝ)) :
    0 ≤ (C - (-30239839964310053528979 / 62500000000000000000000 : ℝ)) * (u * v) + (47829 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_4_7 (C u v : ℝ) (h1 : (3625060923 / 10000000000 : ℝ) ≤ C) (h2 : C ≤ (3625062429 / 10000000000 : ℝ)) :
    0 ≤ (C - (2265663519995064917163 / 6250000000000000000000 : ℝ)) * (u * v) + (79701 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_4_9 (C u v : ℝ) (h1 : (3523288973 / 5000000000 : ℝ) ≤ C) (h2 : C ≤ (352328927 / 500000000 : ℝ)) :
    0 ≤ (C - (22020556755089647625977 / 31250000000000000000000 : ℝ)) * (u * v) + (18919 / 500000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_4_10 (C u v : ℝ) (h1 : (-36881829 / 40000000 : ℝ) ≤ C) (h2 : C ≤ (-922045661 / 1000000000 : ℝ)) :
    0 ≤ (C - (-720348192538187028707 / 781250000000000000000 : ℝ)) * (u * v) + (4819 / 125000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_4_12 (C u v : ℝ) (h1 : (11401602797 / 10000000000 : ℝ) ≤ C) (h2 : C ≤ (11401603359 / 10000000000 : ℝ)) :
    0 ≤ (C - (71260020238553912541509 / 62500000000000000000000 : ℝ)) * (u * v) + (44117 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_4_13 (C u v : ℝ) (h1 : (4182931157 / 10000000000 : ℝ) ≤ C) (h2 : C ≤ (4182931621 / 10000000000 : ℝ)) :
    0 ≤ (C - (26143321912465847219909 / 62500000000000000000000 : ℝ)) * (u * v) + (349 / 10000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_4_15 (u v : ℝ) :
    0 ≤ (0 - (155810118000197 / 12500000000000000000000 : ℝ)) * (u * v) + (2493 / 200000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc (le_refl 0) (le_refl 0) (by norm_num) (by norm_num)
lemma kk_4_16 (C u v : ℝ) (h1 : (55242717 / 156250000 : ℝ) ≤ C) (h2 : C ≤ (3535534039 / 10000000000 : ℝ)) :
    0 ≤ (C - (11048543096312152602571 / 31250000000000000000000 : ℝ)) * (u * v) + (24819 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_4_18 (u v : ℝ) :
    0 ≤ (0 - (155810118000197 / 12500000000000000000000 : ℝ)) * (u * v) + (2493 / 200000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc (le_refl 0) (le_refl 0) (by norm_num) (by norm_num)
lemma kk_4_19 (C u v : ℝ) (h1 : (55242717 / 156250000 : ℝ) ≤ C) (h2 : C ≤ (3535534039 / 10000000000 : ℝ)) :
    0 ≤ (C - (11048543096312152602571 / 31250000000000000000000 : ℝ)) * (u * v) + (24819 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_5_5 (C u : ℝ) (h1 : (6144189481 / 2500000000 : ℝ) ≤ C) (h2 : C ≤ (24576759021 / 10000000000 : ℝ)) :
    0 ≤ (C - (491535169358949755710437 / 200000000000000000000000 : ℝ)) * u ^ 2 + (27653 / 500000000000 : ℝ) * u ^ 2 :=
  diag_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_5_8 (C u v : ℝ) (h1 : (18516045801 / 10000000000 : ℝ) ≤ C) (h2 : C ≤ (18516047667 / 10000000000 : ℝ)) :
    0 ≤ (C - (92580232844965591866709 / 50000000000000000000000 : ℝ)) * (u * v) + (109801 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_5_11 (C u v : ℝ) (h1 : (-15453797787 / 5000000000 : ℝ) ≤ C) (h2 : C ≤ (-15453796921 / 5000000000 : ℝ)) :
    0 ≤ (C - (-154537973486130928133291 / 50000000000000000000000 : ℝ)) * (u * v) + (43839 / 500000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_5_14 (C u v : ℝ) (h1 : (-3090759513 / 1000000000 : ℝ) ≤ C) (h2 : C ≤ (-15453797017 / 5000000000 : ℝ)) :
    0 ≤ (C - (-309075947845925364289563 / 100000000000000000000000 : ℝ)) * (u * v) + (3753 / 50000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_5_15 (C u v : ℝ) (h1 : (-5360934973 / 5000000000 : ℝ) ≤ C) (h2 : C ≤ (-17154991 / 16000000 : ℝ)) :
    0 ≤ (C - (-107218698140347193040167 / 100000000000000000000000 : ℝ)) * (u * v) + (343 / 7812500000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_5_16 (C u v : ℝ) (h1 : (-16499261019 / 5000000000 : ℝ) ≤ C) (h2 : C ≤ (-4124815153 / 1250000000 : ℝ)) :
    0 ≤ (C - (-1649926091680733 / 500000000000000 : ℝ)) * (u * v) + (30481 / 500000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_5_17 (C u v : ℝ) (h1 : (55242717 / 156250000 : ℝ) ≤ C) (h2 : C ≤ (3535534039 / 10000000000 : ℝ)) :
    0 ≤ (C - (7071067757099002034689 / 20000000000000000000000 : ℝ)) * (u * v) + (8023 / 500000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_5_18 (C u v : ℝ) (h1 : (17154991 / 16000000 : ℝ) ≤ C) (h2 : C ≤ (5360934973 / 5000000000 : ℝ)) :
    0 ≤ (C - (107218698140347193040167 / 100000000000000000000000 : ℝ)) * (u * v) + (343 / 7812500000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_5_19 (C u v : ℝ) (h1 : (4124815153 / 1250000000 : ℝ) ≤ C) (h2 : C ≤ (16499261019 / 5000000000 : ℝ)) :
    0 ≤ (C - (1649926091680733 / 500000000000000 : ℝ)) * (u * v) + (30481 / 500000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_5_20 (C u v : ℝ) (h1 : (55242717 / 156250000 : ℝ) ≤ C) (h2 : C ≤ (3535534039 / 10000000000 : ℝ)) :
    0 ≤ (C - (7071067757099002034689 / 20000000000000000000000 : ℝ)) * (u * v) + (8023 / 500000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_6_6 (C u : ℝ) (h1 : (12472120941 / 5000000000 : ℝ) ≤ C) (h2 : C ≤ (24944243537 / 10000000000 : ℝ)) :
    0 ≤ (C - (1247212134669064004036031 / 500000000000000000000000 : ℝ)) * u ^ 2 + (42181 / 500000000000 : ℝ) * u ^ 2 :=
  diag_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_6_7 (C u v : ℝ) (h1 : (9927050187 / 10000000000 : ℝ) ≤ C) (h2 : C ≤ (79416411 / 80000000 : ℝ)) :
    0 ≤ (C - (124088136996323414673809 / 125000000000000000000000 : ℝ)) * (u * v) + (77271 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_6_9 (C u v : ℝ) (h1 : (1081376697 / 10000000000 : ℝ) ≤ C) (h2 : C ≤ (21627577 / 200000000 : ℝ)) :
    0 ≤ (C - (13517220630694455242709 / 125000000000000000000000 : ℝ)) * (u * v) + (23991 / 200000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_6_10 (C u v : ℝ) (h1 : (1583378451 / 1250000000 : ℝ) ≤ C) (h2 : C ≤ (63335147 / 50000000 : ℝ)) :
    0 ≤ (C - (4948058001129295044881 / 3906250000000000000000 : ℝ)) * (u * v) + (91711 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_6_12 (C u v : ℝ) (h1 : (-21208812479 / 10000000000 : ℝ) ≤ C) (h2 : C ≤ (-21208811147 / 10000000000 : ℝ)) :
    0 ≤ (C - (-530220292348536503435909 / 250000000000000000000000 : ℝ)) * (u * v) + (39253 / 500000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_6_13 (C u v : ℝ) (h1 : (-352328927 / 500000000 : ℝ) ≤ C) (h2 : C ≤ (-3523288973 / 5000000000 : ℝ)) :
    0 ≤ (C - (-176164459394358017778029 / 250000000000000000000000 : ℝ)) * (u * v) + (21489 / 500000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_6_15 (C u v : ℝ) (h1 : (55242717 / 156250000 : ℝ) ≤ C) (h2 : C ≤ (3535534039 / 10000000000 : ℝ)) :
    0 ≤ (C - (3535534074335333928983 / 10000000000000000000000 : ℝ)) * (u * v) + (9317 / 500000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_6_16 (u v : ℝ) :
    0 ≤ (0 - (2211652065156611 / 125000000000000000000000 : ℝ)) * (u * v) + (8847 / 500000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc (le_refl 0) (le_refl 0) (by norm_num) (by norm_num)
lemma kk_6_18 (C u v : ℝ) (h1 : (55242717 / 156250000 : ℝ) ≤ C) (h2 : C ≤ (3535534039 / 10000000000 : ℝ)) :
    0 ≤ (C - (3535534074335333928983 / 10000000000000000000000 : ℝ)) * (u * v) + (9317 / 500000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_6_19 (u v : ℝ) :
    0 ≤ (0 - (2211652065156611 / 125000000000000000000000 : ℝ)) * (u * v) + (8847 / 500000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc (le_refl 0) (le_refl 0) (by norm_num) (by norm_num)
lemma kk_7_7 (C u : ℝ) (h1 : (5633947199 / 2000000000 : ℝ) ≤ C) (h2 : C ≤ (14084869009 / 5000000000 : ℝ)) :
    0 ≤ (C - (140848685019532575759229 / 50000000000000000000000 : ℝ)) * u ^ 2 + (10141 / 100000000000 : ℝ) * u ^ 2 :=
  diag_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_7_9 (C u v : ℝ) (h1 : (-63335147 / 50000000 : ℝ) ≤ C) (h2 : C ≤ (-1583378451 / 1250000000 : ℝ)) :
    0 ≤ (C - (-158337857362793611830137 / 125000000000000000000000 : ℝ)) * (u * v) + (98103 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_7_10 (C u v : ℝ) (h1 : (27719180941 / 10000000000 : ℝ) ≤ C) (h2 : C ≤ (27719182479 / 10000000000 : ℝ)) :
    0 ≤ (C - (692979546945595033808067 / 250000000000000000000000 : ℝ)) * (u * v) + (93683 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_7_12 (C u v : ℝ) (h1 : (-14924892379 / 5000000000 : ℝ) ≤ C) (h2 : C ≤ (-14924891967 / 5000000000 : ℝ)) :
    0 ≤ (C - (-746244610665947432270459 / 250000000000000000000000 : ℝ)) * (u * v) + (3079 / 62500000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_7_13 (C u v : ℝ) (h1 : (-36881829 / 40000000 : ℝ) ≤ C) (h2 : C ≤ (-922045661 / 1000000000 : ℝ)) :
    0 ≤ (C - (-230511425625866116927723 / 250000000000000000000000 : ℝ)) * (u * v) + (1297 / 31250000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_7_15 (u v : ℝ) :
    0 ≤ (0 - (-1281580535478037 / 125000000000000000000000 : ℝ)) * (u * v) + (10253 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc (le_refl 0) (le_refl 0) (by norm_num) (by norm_num)
lemma kk_7_16 (C u v : ℝ) (h1 : (55242717 / 156250000 : ℝ) ≤ C) (h2 : C ≤ (3535534039 / 10000000000 : ℝ)) :
    0 ≤ (C - (22097086303183512619229 / 62500000000000000000000 : ℝ)) * (u * v) + (461 / 20000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_7_18 (u v : ℝ) :
    0 ≤ (0 - (-1281580535478037 / 125000000000000000000000 : ℝ)) * (u * v) + (10253 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc (le_refl 0) (le_refl 0) (by norm_num) (by norm_num)
lemma kk_7_19 (C u v : ℝ) (h1 : (55242717 / 156250000 : ℝ) ≤ C) (h2 : C ≤ (3535534039 / 10000000000 : ℝ)) :
    0 ≤ (C - (22097086303183512619229 / 62500000000000000000000 : ℝ)) * (u * v) + (461 / 20000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_8_8 (C u : ℝ) (h1 : (6144189447 / 2500000000 : ℝ) ≤ C) (h2 : C ≤ (24576759303 / 10000000000 : ℝ)) :
    0 ≤ (C - (614418964468703812718499 / 250000000000000000000000 : ℝ)) * u ^ 2 + (3163 / 40000000000 : ℝ) * u ^ 2 :=
  diag_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_8_11 (C u v : ℝ) (h1 : (18516045761 / 10000000000 : ℝ) ≤ C) (h2 : C ≤ (18516047827 / 10000000000 : ℝ)) :
    0 ≤ (C - (46290116998159632057781 / 25000000000000000000000 : ℝ)) * (u * v) + (103827 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_8_14 (C u v : ℝ) (h1 : (-15453797787 / 5000000000 : ℝ) ≤ C) (h2 : C ≤ (-15453796921 / 5000000000 : ℝ)) :
    0 ≤ (C - (-772689866744924737045219 / 250000000000000000000000 : ℝ)) * (u * v) + (90421 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_8_15 (C u v : ℝ) (h1 : (28070218779 / 10000000000 : ℝ) ≤ C) (h2 : C ≤ (28070219539 / 10000000000 : ℝ)) :
    0 ≤ (C - (701755479124699817014933 / 250000000000000000000000 : ℝ)) * (u * v) + (38599 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_8_16 (C u v : ℝ) (h1 : (-10197104337 / 5000000000 : ℝ) ≤ C) (h2 : C ≤ (-10197103649 / 5000000000 : ℝ)) :
    0 ≤ (C - (-50985520039708352355877 / 25000000000000000000000 : ℝ)) * (u * v) + (71789 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_8_17 (C u v : ℝ) (h1 : (55242717 / 156250000 : ℝ) ≤ C) (h2 : C ≤ (3535534039 / 10000000000 : ℝ)) :
    0 ≤ (C - (88388348235523709787771 / 250000000000000000000000 : ℝ)) * (u * v) + (5479 / 500000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_8_18 (C u v : ℝ) (h1 : (-28070219539 / 10000000000 : ℝ) ≤ C) (h2 : C ≤ (-28070218779 / 10000000000 : ℝ)) :
    0 ≤ (C - (-701755479124699817014933 / 250000000000000000000000 : ℝ)) * (u * v) + (38599 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_8_19 (C u v : ℝ) (h1 : (10197103649 / 5000000000 : ℝ) ≤ C) (h2 : C ≤ (10197104337 / 5000000000 : ℝ)) :
    0 ≤ (C - (50985520039708352355877 / 25000000000000000000000 : ℝ)) * (u * v) + (71789 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_8_20 (C u v : ℝ) (h1 : (55242717 / 156250000 : ℝ) ≤ C) (h2 : C ≤ (3535534039 / 10000000000 : ℝ)) :
    0 ≤ (C - (88388348235523709787771 / 250000000000000000000000 : ℝ)) * (u * v) + (5479 / 500000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_9_9 (C u : ℝ) (h1 : (12472120941 / 5000000000 : ℝ) ≤ C) (h2 : C ≤ (24944243537 / 10000000000 : ℝ)) :
    0 ≤ (C - (623606067097880791165941 / 250000000000000000000000 : ℝ)) * u ^ 2 + (85309 / 1000000000000 : ℝ) * u ^ 2 :=
  diag_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_9_10 (C u v : ℝ) (h1 : (-79416411 / 80000000 : ℝ) ≤ C) (h2 : C ≤ (-9927050187 / 10000000000 : ℝ)) :
    0 ≤ (C - (-248176266229135113558191 / 250000000000000000000000 : ℝ)) * (u * v) + (9073 / 125000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_9_12 (C u v : ℝ) (h1 : (12587748421 / 5000000000 : ℝ) ≤ C) (h2 : C ≤ (25175498609 / 10000000000 : ℝ)) :
    0 ≤ (C - (629387442940024403588587 / 250000000000000000000000 : ℝ)) * (u * v) + (4457 / 50000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_9_13 (C u v : ℝ) (h1 : (1209593479 / 2500000000 : ℝ) ≤ C) (h2 : C ≤ (2419187399 / 5000000000 : ℝ)) :
    0 ≤ (C - (120959356357014342123509 / 250000000000000000000000 : ℝ)) * (u * v) + (13593 / 250000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_9_15 (C u v : ℝ) (h1 : (55242717 / 156250000 : ℝ) ≤ C) (h2 : C ≤ (3535534039 / 10000000000 : ℝ)) :
    0 ≤ (C - (44194175476218175039609 / 125000000000000000000000 : ℝ)) * (u * v) + (1501 / 100000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_9_16 (u v : ℝ) :
    0 ≤ (0 - (-357312974704153 / 125000000000000000000000 : ℝ)) * (u * v) + (2859 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc (le_refl 0) (le_refl 0) (by norm_num) (by norm_num)
lemma kk_9_18 (C u v : ℝ) (h1 : (55242717 / 156250000 : ℝ) ≤ C) (h2 : C ≤ (3535534039 / 10000000000 : ℝ)) :
    0 ≤ (C - (44194175476218175039609 / 125000000000000000000000 : ℝ)) * (u * v) + (1501 / 100000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_9_19 (u v : ℝ) :
    0 ≤ (0 - (-357312974704153 / 125000000000000000000000 : ℝ)) * (u * v) + (2859 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc (le_refl 0) (le_refl 0) (by norm_num) (by norm_num)
lemma kk_10_10 (C u : ℝ) (h1 : (5633947199 / 2000000000 : ℝ) ≤ C) (h2 : C ≤ (14084869009 / 5000000000 : ℝ)) :
    0 ≤ (C - (2816973701002158320898167 / 1000000000000000000000000 : ℝ)) * u ^ 2 + (101503 / 1000000000000 : ℝ) * u ^ 2 :=
  diag_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_10_12 (C u v : ℝ) (h1 : (-20495683391 / 10000000000 : ℝ) ≤ C) (h2 : C ≤ (-10247840919 / 5000000000 : ℝ)) :
    0 ≤ (C - (-1024784128156254661867189 / 500000000000000000000000 : ℝ)) * (u * v) + (20697 / 250000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_10_13 (C u v : ℝ) (h1 : (3625060923 / 10000000000 : ℝ) ≤ C) (h2 : C ≤ (3625062429 / 10000000000 : ℝ)) :
    0 ≤ (C - (181253091388818564535903 / 500000000000000000000000 : ℝ)) * (u * v) + (45239 / 500000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_10_15 (u v : ℝ) :
    0 ≤ (0 - (-155436643001669 / 62500000000000000000000 : ℝ)) * (u * v) + (2487 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc (le_refl 0) (le_refl 0) (by norm_num) (by norm_num)
lemma kk_10_16 (C u v : ℝ) (h1 : (55242717 / 156250000 : ℝ) ≤ C) (h2 : C ≤ (3535534039 / 10000000000 : ℝ)) :
    0 ≤ (C - (22097086722619205334703 / 62500000000000000000000 : ℝ)) * (u * v) + (16339 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_10_18 (u v : ℝ) :
    0 ≤ (0 - (-155436643001669 / 62500000000000000000000 : ℝ)) * (u * v) + (2487 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc (le_refl 0) (le_refl 0) (by norm_num) (by norm_num)
lemma kk_10_19 (C u v : ℝ) (h1 : (55242717 / 156250000 : ℝ) ≤ C) (h2 : C ≤ (3535534039 / 10000000000 : ℝ)) :
    0 ≤ (C - (22097086722619205334703 / 62500000000000000000000 : ℝ)) * (u * v) + (16339 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_11_11 (C u : ℝ) (h1 : (6144189447 / 2500000000 : ℝ) ≤ C) (h2 : C ≤ (24576759303 / 10000000000 : ℝ)) :
    0 ≤ (C - (491535170900670175934163 / 200000000000000000000000 : ℝ)) * u ^ 2 + (75797 / 1000000000000 : ℝ) * u ^ 2 :=
  diag_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_11_14 (C u v : ℝ) (h1 : (18516045801 / 10000000000 : ℝ) ≤ C) (h2 : C ≤ (18516047667 / 10000000000 : ℝ)) :
    0 ≤ (C - (185160467340110959682531 / 100000000000000000000000 : ℝ)) * (u * v) + (46651 / 500000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_11_15 (C u v : ℝ) (h1 : (28070218779 / 10000000000 : ℝ) ≤ C) (h2 : C ≤ (28070219539 / 10000000000 : ℝ)) :
    0 ≤ (C - (280702191589685968111839 / 100000000000000000000000 : ℝ)) * (u * v) + (9501 / 250000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_11_16 (C u v : ℝ) (h1 : (10197103649 / 5000000000 : ℝ) ≤ C) (h2 : C ≤ (10197104337 / 5000000000 : ℝ)) :
    0 ≤ (C - (101971039929816145021829 / 50000000000000000000000 : ℝ)) * (u * v) + (17201 / 250000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_11_17 (C u v : ℝ) (h1 : (55242717 / 156250000 : ℝ) ≤ C) (h2 : C ≤ (3535534039 / 10000000000 : ℝ)) :
    0 ≤ (C - (17677669817597184898277 / 50000000000000000000000 : ℝ)) * (u * v) + (59 / 7812500000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_11_18 (C u v : ℝ) (h1 : (-28070219539 / 10000000000 : ℝ) ≤ C) (h2 : C ≤ (-28070218779 / 10000000000 : ℝ)) :
    0 ≤ (C - (-280702191589685968111839 / 100000000000000000000000 : ℝ)) * (u * v) + (9501 / 250000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_11_19 (C u v : ℝ) (h1 : (-10197104337 / 5000000000 : ℝ) ≤ C) (h2 : C ≤ (-10197103649 / 5000000000 : ℝ)) :
    0 ≤ (C - (-101971039929816145021829 / 50000000000000000000000 : ℝ)) * (u * v) + (17201 / 250000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_11_20 (C u v : ℝ) (h1 : (55242717 / 156250000 : ℝ) ≤ C) (h2 : C ≤ (3535534039 / 10000000000 : ℝ)) :
    0 ≤ (C - (17677669817597184898277 / 50000000000000000000000 : ℝ)) * (u * v) + (59 / 7812500000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_12_12 (C u : ℝ) (h1 : (961850497 / 312500000 : ℝ) ≤ C) (h2 : C ≤ (30779217449 / 10000000000 : ℝ)) :
    0 ≤ (C - (3077921672517064162266463 / 1000000000000000000000000 : ℝ)) * u ^ 2 + (41059 / 500000000000 : ℝ) * u ^ 2 :=
  diag_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_12_13 (C u v : ℝ) (h1 : (3067627203 / 5000000000 : ℝ) ≤ C) (h2 : C ≤ (306762759 / 500000000 : ℝ)) :
    0 ≤ (C - (1227050937805013812599 / 2000000000000000000000 : ℝ)) * (u * v) + (24549 / 500000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_12_15 (C u v : ℝ) (h1 : (55242717 / 156250000 : ℝ) ≤ C) (h2 : C ≤ (3535534039 / 10000000000 : ℝ)) :
    0 ≤ (C - (176776697499664619553077 / 500000000000000000000000 : ℝ)) * (u * v) + (8901 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_12_16 (u v : ℝ) :
    0 ≤ (0 - (-1773962953992707 / 500000000000000000000000 : ℝ)) * (u * v) + (887 / 250000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc (le_refl 0) (le_refl 0) (by norm_num) (by norm_num)
lemma kk_12_18 (C u v : ℝ) (h1 : (55242717 / 156250000 : ℝ) ≤ C) (h2 : C ≤ (3535534039 / 10000000000 : ℝ)) :
    0 ≤ (C - (176776697499664619553077 / 500000000000000000000000 : ℝ)) * (u * v) + (8901 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_12_19 (u v : ℝ) :
    0 ≤ (0 - (-1773962953992707 / 500000000000000000000000 : ℝ)) * (u * v) + (887 / 250000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc (le_refl 0) (le_refl 0) (by norm_num) (by norm_num)
lemma kk_13_13 (C u : ℝ) (h1 : (5583690581 / 2500000000 : ℝ) ≤ C) (h2 : C ≤ (11167381747 / 5000000000 : ℝ)) :
    0 ≤ (C - (558369071713414028483403 / 250000000000000000000000 : ℝ)) * u ^ 2 + (62547 / 1000000000000 : ℝ) * u ^ 2 :=
  diag_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_13_15 (u v : ℝ) :
    0 ≤ (0 - (-625704165189869 / 50000000000000000000000 : ℝ)) * (u * v) + (2503 / 200000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc (le_refl 0) (le_refl 0) (by norm_num) (by norm_num)
lemma kk_13_16 (C u v : ℝ) (h1 : (55242717 / 156250000 : ℝ) ≤ C) (h2 : C ≤ (3535534039 / 10000000000 : ℝ)) :
    0 ≤ (C - (88388347236247872915517 / 250000000000000000000000 : ℝ)) * (u * v) + (3739 / 250000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_13_18 (u v : ℝ) :
    0 ≤ (0 - (-625704165189869 / 50000000000000000000000 : ℝ)) * (u * v) + (2503 / 200000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc (le_refl 0) (le_refl 0) (by norm_num) (by norm_num)
lemma kk_13_19 (C u v : ℝ) (h1 : (55242717 / 156250000 : ℝ) ≤ C) (h2 : C ≤ (3535534039 / 10000000000 : ℝ)) :
    0 ≤ (C - (88388347236247872915517 / 250000000000000000000000 : ℝ)) * (u * v) + (3739 / 250000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_14_14 (C u : ℝ) (h1 : (6144189481 / 2500000000 : ℝ) ≤ C) (h2 : C ≤ (24576759021 / 10000000000 : ℝ)) :
    0 ≤ (C - (122883792157832918569507 / 50000000000000000000000 : ℝ)) * u ^ 2 + (921 / 15625000000 : ℝ) * u ^ 2 :=
  diag_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_14_15 (C u v : ℝ) (h1 : (-5360934973 / 5000000000 : ℝ) ≤ C) (h2 : C ≤ (-17154991 / 16000000 : ℝ)) :
    0 ≤ (C - (-134023370756227723343807 / 125000000000000000000000 : ℝ)) * (u * v) + (28551 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_14_16 (C u v : ℝ) (h1 : (4124815153 / 1250000000 : ℝ) ≤ C) (h2 : C ≤ (16499261019 / 5000000000 : ℝ)) :
    0 ≤ (C - (164992608154888506743897 / 50000000000000000000000 : ℝ)) * (u * v) + (40703 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_14_17 (C u v : ℝ) (h1 : (55242717 / 156250000 : ℝ) ≤ C) (h2 : C ≤ (3535534039 / 10000000000 : ℝ)) :
    0 ≤ (C - (176776698175921261194461 / 500000000000000000000000 : ℝ)) * (u * v) + (59 / 7812500000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_14_18 (C u v : ℝ) (h1 : (17154991 / 16000000 : ℝ) ≤ C) (h2 : C ≤ (5360934973 / 5000000000 : ℝ)) :
    0 ≤ (C - (134023370756227723343807 / 125000000000000000000000 : ℝ)) * (u * v) + (28551 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_14_19 (C u v : ℝ) (h1 : (-16499261019 / 5000000000 : ℝ) ≤ C) (h2 : C ≤ (-4124815153 / 1250000000 : ℝ)) :
    0 ≤ (C - (-164992608154888506743897 / 50000000000000000000000 : ℝ)) * (u * v) + (40703 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_14_20 (C u v : ℝ) (h1 : (55242717 / 156250000 : ℝ) ≤ C) (h2 : C ≤ (3535534039 / 10000000000 : ℝ)) :
    0 ≤ (C - (176776698175921261194461 / 500000000000000000000000 : ℝ)) * (u * v) + (59 / 7812500000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_15_15 (C u : ℝ) (h1 : (681353149 / 250000000 : ℝ) ≤ C) (h2 : C ≤ (27254126559 / 10000000000 : ℝ)) :
    0 ≤ (C - (2725412624428780942232819 / 1000000000000000000000000 : ℝ)) * u ^ 2 + (1967 / 62500000000 : ℝ) * u ^ 2 :=
  diag_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_15_16 (u v : ℝ) :
    0 ≤ (0 - (547235049681947 / 500000000000000000000000 : ℝ)) * (u * v) + (219 / 200000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc (le_refl 0) (le_refl 0) (by norm_num) (by norm_num)
lemma kk_15_17 (u v : ℝ) :
    0 ≤ (0 - (6017243802638057 / 500000000000000000000000 : ℝ)) * (u * v) + (2407 / 200000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc (le_refl 0) (le_refl 0) (by norm_num) (by norm_num)
lemma kk_15_18 (C u v : ℝ) (h1 : (-31 / 8 : ℝ) ≤ C) (h2 : C ≤ (-31 / 8 : ℝ)) :
    0 ≤ (C - (-1937499993994924102298053 / 500000000000000000000000 : ℝ)) * (u * v) + (12011 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_15_19 (u v : ℝ) :
    0 ≤ (0 - (-4024086721295033 / 500000000000000000000000 : ℝ)) * (u * v) + (8049 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc (le_refl 0) (le_refl 0) (by norm_num) (by norm_num)
lemma kk_15_20 (u v : ℝ) :
    0 ≤ (0 - (6017243802638057 / 500000000000000000000000 : ℝ)) * (u * v) + (2407 / 200000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc (le_refl 0) (le_refl 0) (by norm_num) (by norm_num)
lemma kk_16_16 (C u : ℝ) (h1 : (27254125869 / 10000000000 : ℝ) ≤ C) (h2 : C ≤ (27254126613 / 10000000000 : ℝ)) :
    0 ≤ (C - (2725412625902305611915409 / 1000000000000000000000000 : ℝ)) * u ^ 2 + (39003 / 1000000000000 : ℝ) * u ^ 2 :=
  diag_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_16_17 (u v : ℝ) :
    0 ≤ (0 - (-116004239759277 / 125000000000000000000000 : ℝ)) * (u * v) + (929 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc (le_refl 0) (le_refl 0) (by norm_num) (by norm_num)
lemma kk_16_18 (u v : ℝ) :
    0 ≤ (0 - (-4024086721295033 / 500000000000000000000000 : ℝ)) * (u * v) + (8049 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc (le_refl 0) (le_refl 0) (by norm_num) (by norm_num)
lemma kk_16_19 (C u v : ℝ) (h1 : (-31 / 8 : ℝ) ≤ C) (h2 : C ≤ (-31 / 8 : ℝ)) :
    0 ≤ (C - (-1937499995636615723408463 / 500000000000000000000000 : ℝ)) * (u * v) + (8727 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_16_20 (u v : ℝ) :
    0 ≤ (0 - (-116004239759277 / 125000000000000000000000 : ℝ)) * (u * v) + (929 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc (le_refl 0) (le_refl 0) (by norm_num) (by norm_num)
lemma kk_17_17 (C u : ℝ) (h1 : (135 / 64 : ℝ) ≤ C) (h2 : C ≤ (135 / 64 : ℝ)) :
    0 ≤ (C - (2109374999317288147373281 / 1000000000000000000000000 : ℝ)) * u ^ 2 + (683 / 1000000000000 : ℝ) * u ^ 2 :=
  diag_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_17_18 (u v : ℝ) :
    0 ≤ (0 - (46427957716883 / 100000000000000000000000 : ℝ)) * (u * v) + (93 / 200000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc (le_refl 0) (le_refl 0) (by norm_num) (by norm_num)
lemma kk_17_19 (u v : ℝ) :
    0 ≤ (0 - (116004239759277 / 125000000000000000000000 : ℝ)) * (u * v) + (929 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc (le_refl 0) (le_refl 0) (by norm_num) (by norm_num)
lemma kk_17_20 (C u v : ℝ) (h1 : (1 / 32 : ℝ) ≤ C) (h2 : C ≤ (1 / 32 : ℝ)) :
    0 ≤ (C - (15624991959659647373281 / 500000000000000000000000 : ℝ)) * (u * v) + (16081 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_18_18 (C u : ℝ) (h1 : (681353149 / 250000000 : ℝ) ≤ C) (h2 : C ≤ (27254126559 / 10000000000 : ℝ)) :
    0 ≤ (C - (545082524931946185086951 / 200000000000000000000000 : ℝ)) * u ^ 2 + (31241 / 1000000000000 : ℝ) * u ^ 2 :=
  diag_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_18_19 (u v : ℝ) :
    0 ≤ (0 - (547235049681947 / 500000000000000000000000 : ℝ)) * (u * v) + (219 / 200000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc (le_refl 0) (le_refl 0) (by norm_num) (by norm_num)
lemma kk_18_20 (u v : ℝ) :
    0 ≤ (0 - (46427957716883 / 100000000000000000000000 : ℝ)) * (u * v) + (93 / 200000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc (le_refl 0) (le_refl 0) (by norm_num) (by norm_num)
lemma kk_19_19 (C u : ℝ) (h1 : (27254125869 / 10000000000 : ℝ) ≤ C) (h2 : C ≤ (27254126613 / 10000000000 : ℝ)) :
    0 ≤ (C - (545082525226651119023469 / 200000000000000000000000 : ℝ)) * u ^ 2 + (19617 / 500000000000 : ℝ) * u ^ 2 :=
  diag_of_enc h1 h2 (by norm_num) (by norm_num)
lemma kk_19_20 (u v : ℝ) :
    0 ≤ (0 - (116004239759277 / 125000000000000000000000 : ℝ)) * (u * v) + (929 / 1000000000000 : ℝ) / 2 * (u ^ 2 + v ^ 2) :=
  cross_of_enc (le_refl 0) (le_refl 0) (by norm_num) (by norm_num)
lemma kk_20_20 (C u : ℝ) (h1 : (135 / 64 : ℝ) ≤ C) (h2 : C ≤ (135 / 64 : ℝ)) :
    0 ≤ (C - (16479492154048238706777 / 7812500000000000000000 : ℝ)) * u ^ 2 + (2141 / 500000000000 : ℝ) * u ^ 2 :=
  diag_of_enc h1 h2 (by norm_num) (by norm_num)
lemma ss_0 (u : ℝ) : 0 ≤ (9896393 / 1000000000000 : ℝ) * u ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
lemma ss_1 (u : ℝ) : 0 ≤ (151079 / 15625000000 : ℝ) * u ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
lemma ss_2 (u : ℝ) : 0 ≤ (2455399 / 250000000000 : ℝ) * u ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
lemma ss_3 (u : ℝ) : 0 ≤ (19201337 / 2000000000000 : ℝ) * u ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
lemma ss_4 (u : ℝ) : 0 ≤ (19414613 / 2000000000000 : ℝ) * u ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
lemma ss_5 (u : ℝ) : 0 ≤ (4835411 / 500000000000 : ℝ) * u ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
lemma ss_6 (u : ℝ) : 0 ≤ (9560149 / 1000000000000 : ℝ) * u ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
lemma ss_7 (u : ℝ) : 0 ≤ (2394767 / 250000000000 : ℝ) * u ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
lemma ss_8 (u : ℝ) : 0 ≤ (19251301 / 2000000000000 : ℝ) * u ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
lemma ss_9 (u : ℝ) : 0 ≤ (9575943 / 1000000000000 : ℝ) * u ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
lemma ss_10 (u : ℝ) : 0 ≤ (19194987 / 2000000000000 : ℝ) * u ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
lemma ss_11 (u : ℝ) : 0 ≤ (19291071 / 2000000000000 : ℝ) * u ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
lemma ss_12 (u : ℝ) : 0 ≤ (19229741 / 2000000000000 : ℝ) * u ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
lemma ss_13 (u : ℝ) : 0 ≤ (1941249 / 200000000000 : ℝ) * u ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
lemma ss_14 (u : ℝ) : 0 ≤ (1214771 / 125000000000 : ℝ) * u ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
lemma ss_15 (u : ℝ) : 0 ≤ (19599951 / 2000000000000 : ℝ) * u ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
lemma ss_16 (u : ℝ) : 0 ≤ (4881703 / 500000000000 : ℝ) * u ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
lemma ss_17 (u : ℝ) : 0 ≤ (19894161 / 2000000000000 : ℝ) * u ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
lemma ss_18 (u : ℝ) : 0 ≤ (19623553 / 2000000000000 : ℝ) * u ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
lemma ss_19 (u : ℝ) : 0 ≤ (390527 / 40000000000 : ℝ) * u ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
lemma ss_20 (u : ℝ) : 0 ≤ (19886963 / 2000000000000 : ℝ) * u ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
lemma sq_0 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : ℝ) : 0 ≤ (831759 / 390625 : ℝ) * (x0 + (0 : ℝ) * x1 + (0 : ℝ) * x2 + (24149951 / 100000000 : ℝ) * x3 + (0 : ℝ) * x4 + (0 : ℝ) * x5 + (561599 / 50000000 : ℝ) * x6 + (0 : ℝ) * x7 + (0 : ℝ) * x8 + (561599 / 50000000 : ℝ) * x9 + (0 : ℝ) * x10 + (0 : ℝ) * x11 + (24149951 / 100000000 : ℝ) * x12 + (0 : ℝ) * x13 + (0 : ℝ) * x14 + (2075523 / 25000000 : ℝ) * x15 + (0 : ℝ) * x16 + (0 : ℝ) * x17 + (2075523 / 25000000 : ℝ) * x18 + (0 : ℝ) * x19 + (0 : ℝ) * x20) ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
lemma sq_1 (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : ℝ) : 0 ≤ (79327373 / 25000000 : ℝ) * (x1 + (0 : ℝ) * x2 + (-19960053 / 50000000 : ℝ) * x3 + (7294159 / 25000000 : ℝ) * x4 + (0 : ℝ) * x5 + (-35932121 / 100000000 : ℝ) * x6 + (-243513 / 500000 : ℝ) * x7 + (0 : ℝ) * x8 + (35932121 / 100000000 : ℝ) * x9 + (-243513 / 500000 : ℝ) * x10 + (0 : ℝ) * x11 + (19960053 / 50000000 : ℝ) * x12 + (7294159 / 25000000 : ℝ) * x13 + (0 : ℝ) * x14 + (0 : ℝ) * x15 + (5571113 / 100000000 : ℝ) * x16 + (0 : ℝ) * x17 + (0 : ℝ) * x18 + (5571113 / 100000000 : ℝ) * x19 + (0 : ℝ) * x20) ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
lemma sq_2 (x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : ℝ) : 0 ≤ (49063517 / 20000000 : ℝ) * (x2 + (0 : ℝ) * x3 + (0 : ℝ) * x4 + (37738931 / 100000000 : ℝ) * x5 + (0 : ℝ) * x6 + (0 : ℝ) * x7 + (-31497533 / 50000000 : ℝ) * x8 + (0 : ℝ) * x9 + (0 : ℝ) * x10 + (-31497533 / 50000000 : ℝ) * x11 + (0 : ℝ) * x12 + (0 : ℝ) * x13 + (37738931 / 100000000 : ℝ) * x14 + (-70717921 / 100000000 : ℝ) * x15 + (0 : ℝ) * x16 + (1441207 / 20000000 : ℝ) * x17 + (70717921 / 100000000 : ℝ) * x18 + (0 : ℝ) * x19 + (1441207 / 20000000 : ℝ) * x20) ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
lemma sq_3 (x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : ℝ) : 0 ≤ (24435673 / 10000000 : ℝ) * (x3 + (642693 / 25000000 : ℝ) * x4 + (0 : ℝ) * x5 + (32650867 / 100000000 : ℝ) * x6 + (8345727 / 50000000 : ℝ) * x7 + (0 : ℝ) * x8 + (-6251753 / 25000000 : ℝ) * x9 + (1119741 / 3125000 : ℝ) * x10 + (0 : ℝ) * x11 + (-11042267 / 20000000 : ℝ) * x12 + (-8205171 / 100000000 : ℝ) * x13 + (0 : ℝ) * x14 + (5487273 / 100000000 : ℝ) * x15 + (90249 / 3125000 : ℝ) * x16 + (0 : ℝ) * x17 + (5487273 / 100000000 : ℝ) * x18 + (90249 / 3125000 : ℝ) * x19 + (0 : ℝ) * x20) ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
lemma sq_4 (x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : ℝ) : 0 ≤ (195724339 / 100000000 : ℝ) * (x4 + (0 : ℝ) * x5 + (112133 / 3125000 : ℝ) * x6 + (15880947 / 50000000 : ℝ) * x7 + (0 : ℝ) * x8 + (903759 / 50000000 : ℝ) * x9 + (-1667753 / 100000000 : ℝ) * x10 + (0 : ℝ) * x11 + (12015973 / 100000000 : ℝ) * x12 + (-2851819 / 100000000 : ℝ) * x13 + (0 : ℝ) * x14 + (-44029 / 25000000 : ℝ) * x15 + (315201 / 5000000 : ℝ) * x16 + (0 : ℝ) * x17 + (-44029 / 25000000 : ℝ) * x18 + (315201 / 5000000 : ℝ) * x19 + (0 : ℝ) * x20) ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
lemma sq_5 (x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : ℝ) : 0 ≤ (105189397 / 50000000 : ℝ) * (x5 + (0 : ℝ) * x6 + (0 : ℝ) * x7 + (35864169 / 50000000 : ℝ) * x8 + (0 : ℝ) * x9 + (0 : ℝ) * x10 + (-571689 / 1250000 : ℝ) * x11 + (0 : ℝ) * x12 + (0 : ℝ) * x13 + (-45032287 / 50000000 : ℝ) * x14 + (1409537 / 25000000 : ℝ) * x15 + (-15685289 / 20000000 : ℝ) * x16 + (5231661 / 100000000 : ℝ) * x17 + (-1409537 / 25000000 : ℝ) * x18 + (15685289 / 20000000 : ℝ) * x19 + (5231661 / 100000000 : ℝ) * x20) ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
lemma sq_6 (x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : ℝ) : 0 ≤ (181694819 / 100000000 : ℝ) * (x6 + (-2950193 / 25000000 : ℝ) * x7 + (0 : ℝ) * x8 + (9104993 / 25000000 : ℝ) * x9 + (-5686647 / 50000000 : ℝ) * x10 + (0 : ℝ) * x11 + (-9851723 / 100000000 : ℝ) * x12 + (2630729 / 100000000 : ℝ) * x13 + (0 : ℝ) * x14 + (3608657 / 50000000 : ℝ) * x15 + (248017 / 12500000 : ℝ) * x16 + (0 : ℝ) * x17 + (3608657 / 50000000 : ℝ) * x18 + (248017 / 12500000 : ℝ) * x19 + (0 : ℝ) * x20) ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
lemma sq_7 (x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : ℝ) : 0 ≤ (44225049 / 25000000 : ℝ) * (x7 + (0 : ℝ) * x8 + (5131963 / 100000000 : ℝ) * x9 + (26747007 / 100000000 : ℝ) * x10 + (0 : ℝ) * x11 + (-21091127 / 50000000 : ℝ) * x12 + (2640039 / 100000000 : ℝ) * x13 + (0 : ℝ) * x14 + (-328491 / 100000000 : ℝ) * x15 + (381849 / 3125000 : ℝ) * x16 + (0 : ℝ) * x17 + (-328491 / 100000000 : ℝ) * x18 + (381849 / 3125000 : ℝ) * x19 + (0 : ℝ) * x20) ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
lemma sq_8 (x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : ℝ) : 0 ≤ (7945471 / 20000000 : ℝ) * (x8 + (0 : ℝ) * x9 + (0 : ℝ) * x10 + (161711711 / 100000000 : ℝ) * x11 + (0 : ℝ) * x12 + (0 : ℝ) * x13 + (99909849 / 100000000 : ℝ) * x14 + (11355913 / 20000000 : ℝ) * x15 + (20609749 / 50000000 : ℝ) * x16 + (41138 / 78125 : ℝ) * x17 + (-11355913 / 20000000 : ℝ) * x18 + (-20609749 / 50000000 : ℝ) * x19 + (41138 / 78125 : ℝ) * x20) ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
lemma sq_9 (x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : ℝ) : 0 ≤ (42021553 / 25000000 : ℝ) * (x9 + (19600547 / 100000000 : ℝ) * x10 + (0 : ℝ) * x11 + (33298733 / 100000000 : ℝ) * x12 + (-9499691 / 100000000 : ℝ) * x13 + (0 : ℝ) * x14 + (9573843 / 100000000 : ℝ) * x15 + (-4302869 / 100000000 : ℝ) * x16 + (0 : ℝ) * x17 + (9573843 / 100000000 : ℝ) * x18 + (-4302869 / 100000000 : ℝ) * x19 + (0 : ℝ) * x20) ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
lemma sq_10 (x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : ℝ) : 0 ≤ (153092379 / 100000000 : ℝ) * (x10 + (0 : ℝ) * x11 + (9732303 / 100000000 : ℝ) * x12 + (23753519 / 50000000 : ℝ) * x13 + (0 : ℝ) * x14 + (-4126639 / 100000000 : ℝ) * x15 + (2614157 / 20000000 : ℝ) * x16 + (0 : ℝ) * x17 + (-4126639 / 100000000 : ℝ) * x18 + (2614157 / 20000000 : ℝ) * x19 + (0 : ℝ) * x20) ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
lemma sq_11 (x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : ℝ) : 0 ≤ (17901 / 25000000 : ℝ) * (x11 + (0 : ℝ) * x12 + (0 : ℝ) * x13 + (40443629 / 50000000 : ℝ) * x14 + (1755151 / 10000000 : ℝ) * x15 + (1065103 / 2500000 : ℝ) * x16 + (1646071 / 6250000 : ℝ) * x17 + (-1755151 / 10000000 : ℝ) * x18 + (-1065103 / 2500000 : ℝ) * x19 + (1646071 / 6250000 : ℝ) * x20) ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
lemma sq_12 (x12 x13 x14 x15 x16 x17 x18 x19 x20 : ℝ) : 0 ≤ (56858059 / 50000000 : ℝ) * (x12 + (-439727 / 3125000 : ℝ) * x13 + (0 : ℝ) * x14 + (15086741 / 100000000 : ℝ) * x15 + (4652579 / 100000000 : ℝ) * x16 + (0 : ℝ) * x17 + (15086741 / 100000000 : ℝ) * x18 + (4652579 / 100000000 : ℝ) * x19 + (0 : ℝ) * x20) ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
lemma sq_13 (x13 x14 x15 x16 x17 x18 x19 x20 : ℝ) : 0 ≤ (19439039 / 12500000 : ℝ) * (x13 + (0 : ℝ) * x14 + (4954467 / 100000000 : ℝ) * x15 + (2145419 / 100000000 : ℝ) * x16 + (0 : ℝ) * x17 + (4954467 / 100000000 : ℝ) * x18 + (2145419 / 100000000 : ℝ) * x19 + (0 : ℝ) * x20) ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
lemma sq_14 (x14 x15 x16 x17 x18 x19 x20 : ℝ) : 0 ≤ (12373 / 50000000 : ℝ) * (x14 + (-970097 / 10000000 : ℝ) * x15 + (29856161 / 100000000 : ℝ) * x16 + (14556407 / 100000000 : ℝ) * x17 + (970097 / 10000000 : ℝ) * x18 + (-29856161 / 100000000 : ℝ) * x19 + (14556407 / 100000000 : ℝ) * x20) ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
lemma sq_15 (x15 x16 x17 x18 x19 x20 : ℝ) : 0 ≤ (32001161 / 25000000 : ℝ) * (x15 + (0 : ℝ) * x16 + (1 / 100000000 : ℝ) * x17 + (-25589231 / 50000000 : ℝ) * x18 + (0 : ℝ) * x19 + (1 / 100000000 : ℝ) * x20) ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
lemma sq_16 (x16 x17 x18 x19 x20 : ℝ) : 0 ≤ (32001161 / 25000000 : ℝ) * (x16 + (0 : ℝ) * x17 + (0 : ℝ) * x18 + (-25589231 / 50000000 : ℝ) * x19 + (0 : ℝ) * x20) ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
lemma sq_17 (x17 x18 x19 x20 : ℝ) : 0 ≤ (197617047 / 100000000 : ℝ) * (x17 + (0 : ℝ) * x18 + (0 : ℝ) * x19 + (-1144431 / 20000000 : ℝ) * x20) ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
lemma sq_18 (x18 x19 x20 : ℝ) : 0 ≤ (4723861 / 5000000 : ℝ) * (x18 + (0 : ℝ) * x19 + (0 : ℝ) * x20) ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
lemma sq_19 (x19 x20 : ℝ) : 0 ≤ (4723861 / 5000000 : ℝ) * (x19 + (0 : ℝ) * x20) ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
lemma sq_20 (x20 : ℝ) : 0 ≤ (49242497 / 25000000 : ℝ) * (x20) ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)

end Reg
end ThomsonN7
/- END QCORE1 -/

/- BEGIN Q2 -/
open Real
open scoped RealInnerProductSpace
namespace ThomsonN7
namespace Reg
open Base

lemma sum_Ioi_seven (f : Fin 7 → Fin 7 → ℝ) :
    ∑ i, ∑ j ∈ Finset.Ioi i, f i j =
      f 0 1 + f 0 2 + f 0 3 + f 0 4 + f 0 5 + f 0 6 + f 1 2 + f 1 3 + f 1 4 + f 1 5 + f 1 6
      + f 2 3 + f 2 4 + f 2 5 + f 2 6 + f 3 4 + f 3 5 + f 3 6 + f 4 5 + f 4 6 + f 5 6 := by
  have hI : ∀ i : Fin 7, ∑ j ∈ Finset.Ioi i, f i j = ∑ j, if i < j then f i j else 0 := by
    intro i; rw [← Finset.sum_filter]; congr 1; ext j; simp
  simp only [hI, Fin.sum_univ_seven]
  simp
  ring

lemma phi_neg_one : phi (-1) = 1 / 2 := by
  unfold phi
  have : (2 - 2 * (-1 : ℝ)) = 2 ^ 2 := by norm_num
  rw [this, Real.sqrt_sq (by norm_num)]
  norm_num

lemma norm_sq_coord (v : R3) : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_three]

lemma inner_coord (u v : R3) : inner ℝ u v = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three]
  ring

lemma gP_0_1 : gP 0 1 = c1 := g_0_1
lemma gP_0_2 : gP 0 2 = c2 := g_0_2
lemma gP_0_3 : gP 0 3 = c2 := g_0_3
lemma gP_0_4 : gP 0 4 = c1 := g_0_4
lemma gP_0_5 : gP 0 5 = 0 := g_0_5
lemma gP_0_6 : gP 0 6 = 0 := g_0_6
lemma gP_1_2 : gP 1 2 = c1 := g_1_2
lemma gP_1_3 : gP 1 3 = c2 := g_1_3
lemma gP_1_4 : gP 1 4 = c2 := g_1_4
lemma gP_1_5 : gP 1 5 = 0 := g_1_5
lemma gP_1_6 : gP 1 6 = 0 := g_1_6
lemma gP_2_3 : gP 2 3 = c1 := g_2_3
lemma gP_2_4 : gP 2 4 = c2 := g_2_4
lemma gP_2_5 : gP 2 5 = 0 := g_2_5
lemma gP_2_6 : gP 2 6 = 0 := g_2_6
lemma gP_3_4 : gP 3 4 = c1 := g_3_4
lemma gP_3_5 : gP 3 5 = 0 := g_3_5
lemma gP_3_6 : gP 3 6 = 0 := g_3_6
lemma gP_4_5 : gP 4 5 = 0 := g_4_5
lemma gP_4_6 : gP 4 6 = 0 := g_4_6
lemma gP_5_6 : gP 5 6 = -1 := g_5_6
lemma pc_0_0 : pentBipyramid 0 0 = 1 := by
  rw [pent_0]; simp
lemma pc_0_1 : pentBipyramid 0 1 = 0 := by
  rw [pent_0]; simp
lemma pc_0_2 : pentBipyramid 0 2 = 0 := by
  rw [pent_0]; simp
lemma pc_1_0 : pentBipyramid 1 0 = c1 := by
  rw [pent_1]; simp
lemma pc_1_1 : pentBipyramid 1 1 = s1 := by
  rw [pent_1]; simp
lemma pc_1_2 : pentBipyramid 1 2 = 0 := by
  rw [pent_1]; simp
lemma pc_2_0 : pentBipyramid 2 0 = c2 := by
  rw [pent_2]; simp
lemma pc_2_1 : pentBipyramid 2 1 = s2 := by
  rw [pent_2]; simp
lemma pc_2_2 : pentBipyramid 2 2 = 0 := by
  rw [pent_2]; simp
lemma pc_3_0 : pentBipyramid 3 0 = c2 := by
  rw [pent_3]; simp
lemma pc_3_1 : pentBipyramid 3 1 = -s2 := by
  rw [pent_3]; simp
lemma pc_3_2 : pentBipyramid 3 2 = 0 := by
  rw [pent_3]; simp
lemma pc_4_0 : pentBipyramid 4 0 = c1 := by
  rw [pent_4]; simp
lemma pc_4_1 : pentBipyramid 4 1 = -s1 := by
  rw [pent_4]; simp
lemma pc_4_2 : pentBipyramid 4 2 = 0 := by
  rw [pent_4]; simp
lemma pc_5_0 : pentBipyramid 5 0 = 0 := by
  rw [pent_5']; simp
lemma pc_5_1 : pentBipyramid 5 1 = 0 := by
  rw [pent_5']; simp
lemma pc_5_2 : pentBipyramid 5 2 = 1 := by
  rw [pent_5']; simp
lemma pc_6_0 : pentBipyramid 6 0 = 0 := by
  rw [pent_6']; simp
lemma pc_6_1 : pentBipyramid 6 1 = 0 := by
  rw [pent_6']; simp
lemma pc_6_2 : pentBipyramid 6 2 = -1 := by
  rw [pent_6']; simp

lemma expansion (h : Fin 7 → R3) :
    Qhess h + 2 * Pen h = Fq c1 s1 (phi c1) (phi c2) (phi 0) (h 0 0) (h 0 1) (h 0 2) (h 1 0) (h 1 1) (h 1 2) (h 2 0) (h 2 1) (h 2 2) (h 3 0) (h 3 1) (h 3 2) (h 4 0) (h 4 1) (h 4 2) (h 5 0) (h 5 1) (h 5 2) (h 6 0) (h 6 1) (h 6 2) := by
  have hc2 : c2 = -1 / 2 - c1 := by unfold c1 c2; ring
  unfold Qhess Pen gaugeG Fq
  simp only [sum_Ioi_seven]
  simp only [Fin.sum_univ_seven, gP_0_1, gP_0_2, gP_0_3, gP_0_4, gP_0_5, gP_0_6,
    gP_1_2, gP_1_3, gP_1_4, gP_1_5, gP_1_6, gP_2_3, gP_2_4, gP_2_5, gP_2_6, gP_3_4, gP_3_5,
    gP_3_6, gP_4_5, gP_4_6, gP_5_6, inner_coord, norm_sq_coord,
    W_0_0, W_0_1, W_0_2, W_0_3, W_0_4, W_0_5, W_0_6, W_1_0, W_1_1, W_1_2, W_1_3, W_1_4, W_1_5, W_1_6,
    W_2_0, W_2_1, W_2_2, W_2_3, W_2_4, W_2_5, W_2_6, W_3_0, W_3_1, W_3_2, W_3_3, W_3_4, W_3_5, W_3_6,
    W_4_0, W_4_1, W_4_2, W_4_3, W_4_4, W_4_5, W_4_6, W_5_0, W_5_1, W_5_2, W_5_3, W_5_4, W_5_5, W_5_6,
    W_6_0, W_6_1, W_6_2, W_6_3, W_6_4, W_6_5, W_6_6,
    muP_0, muP_1, muP_2, muP_3, muP_4, muP_5, muP_6,
    pc_0_0, pc_0_1, pc_0_2, pc_1_0, pc_1_1, pc_1_2, pc_2_0, pc_2_1, pc_2_2, pc_3_0, pc_3_1, pc_3_2, pc_4_0, pc_4_1, pc_4_2, pc_5_0, pc_5_1, pc_5_2, pc_6_0, pc_6_1, pc_6_2]
  simp only [CP_0, CP_1, CP_2, CP_3, CP_4, CP_5, CP_6, CP_7, CP_8, CP_9, CP_10, CP_11, CP_12, CP_13, CP_14, CP_15, CP_16, CP_17, CP_18, CP_19, CP_20, CP_21, CP_22, CP_23, CP_24, CP_25, CP_26, CP_27, CP_28, CP_29, CP_30, CP_31, CP_32, CP_33, CP_34, CP_35, CP_36, CP_37, CP_38, CP_39, CP_40, CP_41, CP_42, CP_43, CP_44, CP_45, CP_46, CP_47, CP_48, CP_49, CP_50, CP_51, CP_52, CP_53, CP_54, CP_55, CP_56, CP_57, CP_58, CP_59, CP_60]
  simp only [phi_neg_one, s2_eq]
  generalize phi c1 = p
  generalize phi c2 = q
  generalize phi 0 = r
  rw [hc2]
  ring

end Reg
end ThomsonN7

/- END Q2 -/

/- BEGIN QCORE2 -/
namespace ThomsonN7
namespace Reg

lemma core (c s p q r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : ℝ) (hb : InBox c s p q r) :
    (449 / 100000 : ℝ) * (x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2 + x5 ^ 2 + x6 ^ 2 + x7 ^ 2 + x8 ^ 2 + x9 ^ 2 + x10 ^ 2 + x11 ^ 2 + x12 ^ 2 + x13 ^ 2 + x14 ^ 2 + x15 ^ 2 + x16 ^ 2 + x17 ^ 2 + x18 ^ 2 + x19 ^ 2 + x20 ^ 2) ≤ Fq c s p q r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 := by
  have e0 := enc_0 c s p q r hb
  have e1 := enc_1 c s p q r hb
  have e2 := enc_2 c s p q r hb
  have e3 := enc_3 c s p q r hb
  have e4 := enc_4 c s p q r hb
  have e5 := enc_5 c s p q r hb
  have e6 := enc_6 c s p q r hb
  have e7 := enc_7 c s p q r hb
  have e8 := enc_8 c s p q r hb
  have e9 := enc_9 c s p q r hb
  have e10 := enc_10 c s p q r hb
  have e11 := enc_11 c s p q r hb
  have e12 := enc_12 c s p q r hb
  have e13 := enc_13 c s p q r hb
  have e14 := enc_14 c s p q r hb
  have e15 := enc_15 c s p q r hb
  have e16 := enc_16 c s p q r hb
  have e17 := enc_17 c s p q r hb
  have e18 := enc_18 c s p q r hb
  have e19 := enc_19 c s p q r hb
  have e20 := enc_20 c s p q r hb
  have e21 := enc_21 c s p q r hb
  have e22 := enc_22 c s p q r hb
  have e23 := enc_23 c s p q r hb
  have e24 := enc_24 c s p q r hb
  have e25 := enc_25 c s p q r hb
  have e26 := enc_26 c s p q r hb
  have e27 := enc_27 c s p q r hb
  have e28 := enc_28 c s p q r hb
  have e29 := enc_29 c s p q r hb
  have e30 := enc_30 c s p q r hb
  have e31 := enc_31 c s p q r hb
  have e32 := enc_32 c s p q r hb
  have e33 := enc_33 c s p q r hb
  have e34 := enc_34 c s p q r hb
  have e35 := enc_35 c s p q r hb
  have e36 := enc_36 c s p q r hb
  have e37 := enc_37 c s p q r hb
  have e38 := enc_38 c s p q r hb
  have e39 := enc_39 c s p q r hb
  have e40 := enc_40 c s p q r hb
  have e41 := enc_41 c s p q r hb
  have e42 := enc_42 c s p q r hb
  have e43 := enc_43 c s p q r hb
  have e44 := enc_44 c s p q r hb
  have e45 := enc_45 c s p q r hb
  have e46 := enc_46 c s p q r hb
  have e47 := enc_47 c s p q r hb
  have e48 := enc_48 c s p q r hb
  have e49 := enc_49 c s p q r hb
  have e50 := enc_50 c s p q r hb
  have e51 := enc_51 c s p q r hb
  have e52 := enc_52 c s p q r hb
  have e53 := enc_53 c s p q r hb
  have e54 := enc_54 c s p q r hb
  have e55 := enc_55 c s p q r hb
  have e56 := enc_56 c s p q r hb
  have e57 := enc_57 c s p q r hb
  have e58 := enc_58 c s p q r hb
  have e59 := enc_59 c s p q r hb
  have e60 := enc_60 c s p q r hb
  have q_0 := sq_0 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
  have q_1 := sq_1 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
  have q_2 := sq_2 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
  have q_3 := sq_3 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
  have q_4 := sq_4 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
  have q_5 := sq_5 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
  have q_6 := sq_6 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
  have q_7 := sq_7 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
  have q_8 := sq_8 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
  have q_9 := sq_9 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
  have q_10 := sq_10 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
  have q_11 := sq_11 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
  have q_12 := sq_12 x12 x13 x14 x15 x16 x17 x18 x19 x20
  have q_13 := sq_13 x13 x14 x15 x16 x17 x18 x19 x20
  have q_14 := sq_14 x14 x15 x16 x17 x18 x19 x20
  have q_15 := sq_15 x15 x16 x17 x18 x19 x20
  have q_16 := sq_16 x16 x17 x18 x19 x20
  have q_17 := sq_17 x17 x18 x19 x20
  have q_18 := sq_18 x18 x19 x20
  have q_19 := sq_19 x19 x20
  have q_20 := sq_20 x20
  have k_0_0 := kk_0_0 (CP_0 c s p q r) x0 e0.1 e0.2
  have k_0_3 := kk_0_3 (CP_1 c s p q r) x0 x3 e1.1 e1.2
  have k_0_6 := kk_0_6 (CP_2 c s p q r) x0 x6 e2.1 e2.2
  have k_0_9 := kk_0_9 (CP_2 c s p q r) x0 x9 e2.1 e2.2
  have k_0_12 := kk_0_12 (CP_1 c s p q r) x0 x12 e1.1 e1.2
  have k_0_15 := kk_0_15 (CP_3 c s p q r) x0 x15 e3.1 e3.2
  have k_0_18 := kk_0_18 (CP_3 c s p q r) x0 x18 e3.1 e3.2
  have k_1_1 := kk_1_1 (CP_4 c s p q r) x1 e4.1 e4.2
  have k_1_3 := kk_1_3 (CP_5 c s p q r) x1 x3 e5.1 e5.2
  have k_1_4 := kk_1_4 (CP_6 c s p q r) x1 x4 e6.1 e6.2
  have k_1_6 := kk_1_6 (CP_7 c s p q r) x1 x6 e7.1 e7.2
  have k_1_7 := kk_1_7 (CP_8 c s p q r) x1 x7 e8.1 e8.2
  have k_1_9 := kk_1_9 (CP_9 c s p q r) x1 x9 e9.1 e9.2
  have k_1_10 := kk_1_10 (CP_8 c s p q r) x1 x10 e8.1 e8.2
  have k_1_12 := kk_1_12 (CP_10 c s p q r) x1 x12 e10.1 e10.2
  have k_1_13 := kk_1_13 (CP_6 c s p q r) x1 x13 e6.1 e6.2
  have k_1_16 := kk_1_16 (CP_3 c s p q r) x1 x16 e3.1 e3.2
  have k_1_19 := kk_1_19 (CP_3 c s p q r) x1 x19 e3.1 e3.2
  have k_2_2 := kk_2_2 (CP_11 c s p q r) x2 e11.1 e11.2
  have k_2_5 := kk_2_5 (CP_6 c s p q r) x2 x5 e6.1 e6.2
  have k_2_8 := kk_2_8 (CP_8 c s p q r) x2 x8 e8.1 e8.2
  have k_2_11 := kk_2_11 (CP_8 c s p q r) x2 x11 e8.1 e8.2
  have k_2_14 := kk_2_14 (CP_6 c s p q r) x2 x14 e6.1 e6.2
  have k_2_15 := kk_2_15 (CP_12 c s p q r) x2 x15 e12.1 e12.2
  have k_2_17 := kk_2_17 (CP_3 c s p q r) x2 x17 e3.1 e3.2
  have k_2_18 := kk_2_18 (CP_13 c s p q r) x2 x18 e13.1 e13.2
  have k_2_20 := kk_2_20 (CP_3 c s p q r) x2 x20 e3.1 e3.2
  have k_3_3 := kk_3_3 (CP_14 c s p q r) x3 e14.1 e14.2
  have k_3_4 := kk_3_4 (CP_15 c s p q r) x3 x4 e15.1 e15.2
  have k_3_6 := kk_3_6 (CP_16 c s p q r) x3 x6 e16.1 e16.2
  have k_3_7 := kk_3_7 (CP_17 c s p q r) x3 x7 e17.1 e17.2
  have k_3_9 := kk_3_9 (CP_18 c s p q r) x3 x9 e18.1 e18.2
  have k_3_10 := kk_3_10 (CP_19 c s p q r) x3 x10 e19.1 e19.2
  have k_3_12 := kk_3_12 (CP_20 c s p q r) x3 x12 e20.1 e20.2
  have k_3_13 := kk_3_13 (CP_21 c s p q r) x3 x13 e21.1 e21.2
  have k_3_15 := kk_3_15 (CP_3 c s p q r) x3 x15 e3.1 e3.2
  have k_3_16 := kk_3_16 x3 x16
  have k_3_18 := kk_3_18 (CP_3 c s p q r) x3 x18 e3.1 e3.2
  have k_3_19 := kk_3_19 x3 x19
  have k_4_4 := kk_4_4 (CP_22 c s p q r) x4 e22.1 e22.2
  have k_4_6 := kk_4_6 (CP_23 c s p q r) x4 x6 e23.1 e23.2
  have k_4_7 := kk_4_7 (CP_24 c s p q r) x4 x7 e24.1 e24.2
  have k_4_9 := kk_4_9 (CP_25 c s p q r) x4 x9 e25.1 e25.2
  have k_4_10 := kk_4_10 (CP_26 c s p q r) x4 x10 e26.1 e26.2
  have k_4_12 := kk_4_12 (CP_27 c s p q r) x4 x12 e27.1 e27.2
  have k_4_13 := kk_4_13 (CP_28 c s p q r) x4 x13 e28.1 e28.2
  have k_4_15 := kk_4_15 x4 x15
  have k_4_16 := kk_4_16 (CP_3 c s p q r) x4 x16 e3.1 e3.2
  have k_4_18 := kk_4_18 x4 x18
  have k_4_19 := kk_4_19 (CP_3 c s p q r) x4 x19 e3.1 e3.2
  have k_5_5 := kk_5_5 (CP_29 c s p q r) x5 e29.1 e29.2
  have k_5_8 := kk_5_8 (CP_30 c s p q r) x5 x8 e30.1 e30.2
  have k_5_11 := kk_5_11 (CP_31 c s p q r) x5 x11 e31.1 e31.2
  have k_5_14 := kk_5_14 (CP_32 c s p q r) x5 x14 e32.1 e32.2
  have k_5_15 := kk_5_15 (CP_33 c s p q r) x5 x15 e33.1 e33.2
  have k_5_16 := kk_5_16 (CP_34 c s p q r) x5 x16 e34.1 e34.2
  have k_5_17 := kk_5_17 (CP_3 c s p q r) x5 x17 e3.1 e3.2
  have k_5_18 := kk_5_18 (CP_35 c s p q r) x5 x18 e35.1 e35.2
  have k_5_19 := kk_5_19 (CP_36 c s p q r) x5 x19 e36.1 e36.2
  have k_5_20 := kk_5_20 (CP_3 c s p q r) x5 x20 e3.1 e3.2
  have k_6_6 := kk_6_6 (CP_37 c s p q r) x6 e37.1 e37.2
  have k_6_7 := kk_6_7 (CP_38 c s p q r) x6 x7 e38.1 e38.2
  have k_6_9 := kk_6_9 (CP_39 c s p q r) x6 x9 e39.1 e39.2
  have k_6_10 := kk_6_10 (CP_40 c s p q r) x6 x10 e40.1 e40.2
  have k_6_12 := kk_6_12 (CP_18 c s p q r) x6 x12 e18.1 e18.2
  have k_6_13 := kk_6_13 (CP_41 c s p q r) x6 x13 e41.1 e41.2
  have k_6_15 := kk_6_15 (CP_3 c s p q r) x6 x15 e3.1 e3.2
  have k_6_16 := kk_6_16 x6 x16
  have k_6_18 := kk_6_18 (CP_3 c s p q r) x6 x18 e3.1 e3.2
  have k_6_19 := kk_6_19 x6 x19
  have k_7_7 := kk_7_7 (CP_42 c s p q r) x7 e42.1 e42.2
  have k_7_9 := kk_7_9 (CP_43 c s p q r) x7 x9 e43.1 e43.2
  have k_7_10 := kk_7_10 (CP_44 c s p q r) x7 x10 e44.1 e44.2
  have k_7_12 := kk_7_12 (CP_45 c s p q r) x7 x12 e45.1 e45.2
  have k_7_13 := kk_7_13 (CP_26 c s p q r) x7 x13 e26.1 e26.2
  have k_7_15 := kk_7_15 x7 x15
  have k_7_16 := kk_7_16 (CP_3 c s p q r) x7 x16 e3.1 e3.2
  have k_7_18 := kk_7_18 x7 x18
  have k_7_19 := kk_7_19 (CP_3 c s p q r) x7 x19 e3.1 e3.2
  have k_8_8 := kk_8_8 (CP_46 c s p q r) x8 e46.1 e46.2
  have k_8_11 := kk_8_11 (CP_47 c s p q r) x8 x11 e47.1 e47.2
  have k_8_14 := kk_8_14 (CP_31 c s p q r) x8 x14 e31.1 e31.2
  have k_8_15 := kk_8_15 (CP_48 c s p q r) x8 x15 e48.1 e48.2
  have k_8_16 := kk_8_16 (CP_49 c s p q r) x8 x16 e49.1 e49.2
  have k_8_17 := kk_8_17 (CP_3 c s p q r) x8 x17 e3.1 e3.2
  have k_8_18 := kk_8_18 (CP_50 c s p q r) x8 x18 e50.1 e50.2
  have k_8_19 := kk_8_19 (CP_51 c s p q r) x8 x19 e51.1 e51.2
  have k_8_20 := kk_8_20 (CP_3 c s p q r) x8 x20 e3.1 e3.2
  have k_9_9 := kk_9_9 (CP_37 c s p q r) x9 e37.1 e37.2
  have k_9_10 := kk_9_10 (CP_52 c s p q r) x9 x10 e52.1 e52.2
  have k_9_12 := kk_9_12 (CP_16 c s p q r) x9 x12 e16.1 e16.2
  have k_9_13 := kk_9_13 (CP_53 c s p q r) x9 x13 e53.1 e53.2
  have k_9_15 := kk_9_15 (CP_3 c s p q r) x9 x15 e3.1 e3.2
  have k_9_16 := kk_9_16 x9 x16
  have k_9_18 := kk_9_18 (CP_3 c s p q r) x9 x18 e3.1 e3.2
  have k_9_19 := kk_9_19 x9 x19
  have k_10_10 := kk_10_10 (CP_42 c s p q r) x10 e42.1 e42.2
  have k_10_12 := kk_10_12 (CP_54 c s p q r) x10 x12 e54.1 e54.2
  have k_10_13 := kk_10_13 (CP_24 c s p q r) x10 x13 e24.1 e24.2
  have k_10_15 := kk_10_15 x10 x15
  have k_10_16 := kk_10_16 (CP_3 c s p q r) x10 x16 e3.1 e3.2
  have k_10_18 := kk_10_18 x10 x18
  have k_10_19 := kk_10_19 (CP_3 c s p q r) x10 x19 e3.1 e3.2
  have k_11_11 := kk_11_11 (CP_46 c s p q r) x11 e46.1 e46.2
  have k_11_14 := kk_11_14 (CP_30 c s p q r) x11 x14 e30.1 e30.2
  have k_11_15 := kk_11_15 (CP_48 c s p q r) x11 x15 e48.1 e48.2
  have k_11_16 := kk_11_16 (CP_51 c s p q r) x11 x16 e51.1 e51.2
  have k_11_17 := kk_11_17 (CP_3 c s p q r) x11 x17 e3.1 e3.2
  have k_11_18 := kk_11_18 (CP_50 c s p q r) x11 x18 e50.1 e50.2
  have k_11_19 := kk_11_19 (CP_49 c s p q r) x11 x19 e49.1 e49.2
  have k_11_20 := kk_11_20 (CP_3 c s p q r) x11 x20 e3.1 e3.2
  have k_12_12 := kk_12_12 (CP_14 c s p q r) x12 e14.1 e14.2
  have k_12_13 := kk_12_13 (CP_55 c s p q r) x12 x13 e55.1 e55.2
  have k_12_15 := kk_12_15 (CP_3 c s p q r) x12 x15 e3.1 e3.2
  have k_12_16 := kk_12_16 x12 x16
  have k_12_18 := kk_12_18 (CP_3 c s p q r) x12 x18 e3.1 e3.2
  have k_12_19 := kk_12_19 x12 x19
  have k_13_13 := kk_13_13 (CP_22 c s p q r) x13 e22.1 e22.2
  have k_13_15 := kk_13_15 x13 x15
  have k_13_16 := kk_13_16 (CP_3 c s p q r) x13 x16 e3.1 e3.2
  have k_13_18 := kk_13_18 x13 x18
  have k_13_19 := kk_13_19 (CP_3 c s p q r) x13 x19 e3.1 e3.2
  have k_14_14 := kk_14_14 (CP_29 c s p q r) x14 e29.1 e29.2
  have k_14_15 := kk_14_15 (CP_33 c s p q r) x14 x15 e33.1 e33.2
  have k_14_16 := kk_14_16 (CP_36 c s p q r) x14 x16 e36.1 e36.2
  have k_14_17 := kk_14_17 (CP_3 c s p q r) x14 x17 e3.1 e3.2
  have k_14_18 := kk_14_18 (CP_35 c s p q r) x14 x18 e35.1 e35.2
  have k_14_19 := kk_14_19 (CP_34 c s p q r) x14 x19 e34.1 e34.2
  have k_14_20 := kk_14_20 (CP_3 c s p q r) x14 x20 e3.1 e3.2
  have k_15_15 := kk_15_15 (CP_56 c s p q r) x15 e56.1 e56.2
  have k_15_16 := kk_15_16 x15 x16
  have k_15_17 := kk_15_17 x15 x17
  have k_15_18 := kk_15_18 (CP_57 c s p q r) x15 x18 e57.1 e57.2
  have k_15_19 := kk_15_19 x15 x19
  have k_15_20 := kk_15_20 x15 x20
  have k_16_16 := kk_16_16 (CP_58 c s p q r) x16 e58.1 e58.2
  have k_16_17 := kk_16_17 x16 x17
  have k_16_18 := kk_16_18 x16 x18
  have k_16_19 := kk_16_19 (CP_57 c s p q r) x16 x19 e57.1 e57.2
  have k_16_20 := kk_16_20 x16 x20
  have k_17_17 := kk_17_17 (CP_59 c s p q r) x17 e59.1 e59.2
  have k_17_18 := kk_17_18 x17 x18
  have k_17_19 := kk_17_19 x17 x19
  have k_17_20 := kk_17_20 (CP_60 c s p q r) x17 x20 e60.1 e60.2
  have k_18_18 := kk_18_18 (CP_56 c s p q r) x18 e56.1 e56.2
  have k_18_19 := kk_18_19 x18 x19
  have k_18_20 := kk_18_20 x18 x20
  have k_19_19 := kk_19_19 (CP_58 c s p q r) x19 e58.1 e58.2
  have k_19_20 := kk_19_20 x19 x20
  have k_20_20 := kk_20_20 (CP_59 c s p q r) x20 e59.1 e59.2
  have s_0 := ss_0 x0
  have s_1 := ss_1 x1
  have s_2 := ss_2 x2
  have s_3 := ss_3 x3
  have s_4 := ss_4 x4
  have s_5 := ss_5 x5
  have s_6 := ss_6 x6
  have s_7 := ss_7 x7
  have s_8 := ss_8 x8
  have s_9 := ss_9 x9
  have s_10 := ss_10 x10
  have s_11 := ss_11 x11
  have s_12 := ss_12 x12
  have s_13 := ss_13 x13
  have s_14 := ss_14 x14
  have s_15 := ss_15 x15
  have s_16 := ss_16 x16
  have s_17 := ss_17 x17
  have s_18 := ss_18 x18
  have s_19 := ss_19 x19
  have s_20 := ss_20 x20
  unfold Fq
  linear_combination q_0 + q_1 + q_2 + q_3 + q_4 + q_5 + q_6 + q_7 + q_8 + q_9 + q_10 + q_11 + q_12 + q_13 + q_14 + q_15 + q_16 + q_17 + q_18 + q_19 + q_20 + k_0_0 + k_0_3 + k_0_6 + k_0_9 + k_0_12 + k_0_15 + k_0_18 + k_1_1 + k_1_3 + k_1_4 + k_1_6 + k_1_7 + k_1_9 + k_1_10 + k_1_12 + k_1_13 + k_1_16 + k_1_19 + k_2_2 + k_2_5 + k_2_8 + k_2_11 + k_2_14 + k_2_15 + k_2_17 + k_2_18 + k_2_20 + k_3_3 + k_3_4 + k_3_6 + k_3_7 + k_3_9 + k_3_10 + k_3_12 + k_3_13 + k_3_15 + k_3_16 + k_3_18 + k_3_19 + k_4_4 + k_4_6 + k_4_7 + k_4_9 + k_4_10 + k_4_12 + k_4_13 + k_4_15 + k_4_16 + k_4_18 + k_4_19 + k_5_5 + k_5_8 + k_5_11 + k_5_14 + k_5_15 + k_5_16 + k_5_17 + k_5_18 + k_5_19 + k_5_20 + k_6_6 + k_6_7 + k_6_9 + k_6_10 + k_6_12 + k_6_13 + k_6_15 + k_6_16 + k_6_18 + k_6_19 + k_7_7 + k_7_9 + k_7_10 + k_7_12 + k_7_13 + k_7_15 + k_7_16 + k_7_18 + k_7_19 + k_8_8 + k_8_11 + k_8_14 + k_8_15 + k_8_16 + k_8_17 + k_8_18 + k_8_19 + k_8_20 + k_9_9 + k_9_10 + k_9_12 + k_9_13 + k_9_15 + k_9_16 + k_9_18 + k_9_19 + k_10_10 + k_10_12 + k_10_13 + k_10_15 + k_10_16 + k_10_18 + k_10_19 + k_11_11 + k_11_14 + k_11_15 + k_11_16 + k_11_17 + k_11_18 + k_11_19 + k_11_20 + k_12_12 + k_12_13 + k_12_15 + k_12_16 + k_12_18 + k_12_19 + k_13_13 + k_13_15 + k_13_16 + k_13_18 + k_13_19 + k_14_14 + k_14_15 + k_14_16 + k_14_17 + k_14_18 + k_14_19 + k_14_20 + k_15_15 + k_15_16 + k_15_17 + k_15_18 + k_15_19 + k_15_20 + k_16_16 + k_16_17 + k_16_18 + k_16_19 + k_16_20 + k_17_17 + k_17_18 + k_17_19 + k_17_20 + k_18_18 + k_18_19 + k_18_20 + k_19_19 + k_19_20 + k_20_20 + s_0 + s_1 + s_2 + s_3 + s_4 + s_5 + s_6 + s_7 + s_8 + s_9 + s_10 + s_11 + s_12 + s_13 + s_14 + s_15 + s_16 + s_17 + s_18 + s_19 + s_20

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

lemma sqrt5_lo : (2236067977499789 / 1000000000000000 : ℝ) ≤ √5 := by
  rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num

lemma sqrt5_hi : √5 ≤ (2236067977499790 / 1000000000000000 : ℝ) := by
  rw [Real.sqrt_le_left (by norm_num)]; norm_num

lemma box_phi {p u ulo uhi plo phi : ℝ} (hp : 0 < p) (hpu : p ^ 2 * u = 1) (h1 : ulo ≤ u)
    (h2 : u ≤ uhi) (hulo : 0 < ulo) (hlo : plo ^ 2 * uhi ≤ 1) (hhi : 1 ≤ phi ^ 2 * ulo)
    (hplo : 0 ≤ plo) (hphi : 0 ≤ phi) : plo ≤ p ∧ p ≤ phi := by
  have hu : 0 < u := lt_of_lt_of_le hulo h1
  constructor
  · by_contra hc
    push_neg at hc
    have h3 : p ^ 2 < plo ^ 2 := by nlinarith
    have h4 : p ^ 2 * u < plo ^ 2 * u := mul_lt_mul_of_pos_right h3 hu
    have h5 : plo ^ 2 * u ≤ plo ^ 2 * uhi := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    linarith
  · by_contra hc
    push_neg at hc
    have h3 : phi ^ 2 < p ^ 2 := by nlinarith
    have h4 : phi ^ 2 * u < p ^ 2 * u := mul_lt_mul_of_pos_right h3 hu
    have h5 : phi ^ 2 * ulo ≤ phi ^ 2 * u := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    linarith

lemma box_sq {p a alo ahi plo phi : ℝ} (hp : 0 < p) (hpa : p ^ 2 = a) (h1 : alo ≤ a)
    (h2 : a ≤ ahi) (hlo : plo ^ 2 ≤ alo) (hhi : ahi ≤ phi ^ 2) (hplo : 0 ≤ plo)
    (hphi : 0 ≤ phi) : plo ≤ p ∧ p ≤ phi := by
  constructor
  · by_contra hc
    push_neg at hc
    have h3 : p ^ 2 < plo ^ 2 := by nlinarith
    linarith
  · by_contra hc
    push_neg at hc
    have h3 : phi ^ 2 < p ^ 2 := by nlinarith
    linarith

lemma c1_box : (30901699 / 100000000 : ℝ) ≤ c1 ∧ c1 ≤ (309017 / 1000000 : ℝ) := by
  have h5 := sqrt5_lo
  have h6 := sqrt5_hi
  unfold c1
  constructor <;> linarith

lemma c1_lt_one : c1 < 1 := by
  have h6 := sqrt5_hi
  unfold c1
  linarith

lemma c2_lt_one : c2 < 1 := by
  have h5 := sqrt5_lo
  unfold c2
  linarith

lemma s1_box : (95105651 / 100000000 : ℝ) ≤ s1 ∧ s1 ≤ (23776413 / 25000000 : ℝ) := by
  have h5 := sqrt5_lo
  have h6 := sqrt5_hi
  have hs : s1 ^ 2 = 3 / 4 + c1 / 2 := by
    have := s1_sq
    have := hF4
    linarith
  have hpos : 0 < s1 := by
    unfold s1
    exact Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  have hc : (1236067977499789 / 4000000000000000 : ℝ) ≤ c1 ∧ c1 ≤ (123606797749979 / 400000000000000 : ℝ) := by
    unfold c1
    constructor <;> linarith
  exact box_sq hpos hs (a := 3 / 4 + c1 / 2) (alo := (7236067977499789 / 8000000000000000 : ℝ)) (ahi := (723606797749979 / 800000000000000 : ℝ))
    (by linarith [hc.1]) (by linarith [hc.2]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma phi_c1_box : (2126627 / 2500000 : ℝ) ≤ phi c1 ∧ phi c1 ≤ (85065081 / 100000000 : ℝ) := by
  have h5 := sqrt5_lo
  have h6 := sqrt5_hi
  refine box_phi (phi_pos c1_lt_one) (phi_sq_mul c1_lt_one) (ulo := (276393202250021 / 200000000000000 : ℝ)) (uhi := (2763932022500211 / 2000000000000000 : ℝ))
    ?_ ?_ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · unfold c1; linarith
  · unfold c1; linarith

lemma phi_c2_box : (52573111 / 100000000 : ℝ) ≤ phi c2 ∧ phi c2 ≤ (6571639 / 12500000 : ℝ) := by
  have h5 := sqrt5_lo
  have h6 := sqrt5_hi
  refine box_phi (phi_pos c2_lt_one) (phi_sq_mul c2_lt_one) (ulo := (7236067977499789 / 2000000000000000 : ℝ)) (uhi := (723606797749979 / 200000000000000 : ℝ))
    ?_ ?_ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · unfold c2; linarith
  · unfold c2; linarith

lemma phi_zero_box : (35355339 / 50000000 : ℝ) ≤ phi 0 ∧ phi 0 ≤ (70710679 / 100000000 : ℝ) := by
  have h0 : (0 : ℝ) < 1 := one_pos
  refine box_phi (phi_pos h0) (phi_sq_mul h0) (ulo := 2) (uhi := 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma atoms_inBox : InBox c1 s1 (phi c1) (phi c2) (phi 0) :=
  ⟨c1_box.1, c1_box.2, s1_box.1, s1_box.2, phi_c1_box.1, phi_c1_box.2, phi_c2_box.1,
    phi_c2_box.2, phi_zero_box.1, phi_zero_box.2⟩

/-- The penalised Hessian bound `449/100000 ∑ ‖hᵢ‖² ≤ Qhess h + 2 Pen h`, from the certificate. -/
lemma hessian_lower (h : Fin 7 → R3) :
    449 / 100000 * ∑ i, ‖h i‖ ^ 2 ≤ Qhess h + 2 * Pen h := by
  rw [expansion h]
  have hc := core c1 s1 (phi c1) (phi c2) (phi 0) (h 0 0) (h 0 1) (h 0 2) (h 1 0) (h 1 1) (h 1 2)
    (h 2 0) (h 2 1) (h 2 2) (h 3 0) (h 3 1) (h 3 2) (h 4 0) (h 4 1) (h 4 2) (h 5 0) (h 5 1) (h 5 2)
    (h 6 0) (h 6 1) (h 6 2) atoms_inBox
  simp only [Fin.sum_univ_seven, norm_sq_coord]
  linarith [hc]

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
theorem solution (h : Fin 7 → R3) :
    449 / 100000 * ∑ i, ‖h i‖ ^ 2 ≤ Reg.Qhess h + 2 * Reg.Pen h :=
  ThomsonN7.Reg.hessian_lower h
