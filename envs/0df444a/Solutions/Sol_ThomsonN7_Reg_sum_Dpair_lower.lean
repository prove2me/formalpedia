-- Prove2me | solution 1 for ThomsonN7.Reg.sum_Dpair_lower
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-10-10T02:09:00.014988+00:00
-- url     : https://prove2.me/submissions/a451afe9-ed4e-4733-8355-c742c3791435

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

lemma inner_lt_one_of_ne {x y : R3} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hne : x ≠ y) :
    inner ℝ x y < 1 := by
  have h := norm_sub_sq_of_unit hx hy
  have : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  nlinarith

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

lemma inner_vec3 (a b c d e f : ℝ) :
    inner ℝ (!₂[a, b, c] : R3) !₂[d, e, f] = a * d + b * e + c * f := by
  simp [PiLp.inner_apply, Fin.sum_univ_three] <;> ring

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

lemma g_3_4 : inner ℝ (pentBipyramid 3) (pentBipyramid 4) = c1 := by
  rw [pent_3, pent_4, inner_vec3]
  linear_combination (c1) * hF1 + (s1) * hF2 + (2*c1) * hF3 + (-2*c1) * hF4

lemma g_3_5 : inner ℝ (pentBipyramid 3) (pentBipyramid 5) = 0 :=
  pent_inner_north (by decide)

lemma g_3_6 : inner ℝ (pentBipyramid 3) (pentBipyramid 6) = 0 :=
  pent_inner_south (by decide)

lemma g_4_5 : inner ℝ (pentBipyramid 4) (pentBipyramid 5) = 0 :=
  pent_inner_north (by decide)

lemma g_4_6 : inner ℝ (pentBipyramid 4) (pentBipyramid 6) = 0 :=
  pent_inner_south (by decide)

lemma g_5_6 : inner ℝ (pentBipyramid 5) (pentBipyramid 6) = -1 := pent_inner_poles

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

lemma tau_expand (y : Fin 7 → R3) (i j : Fin 7) :
    tau y i j = inner ℝ (pentBipyramid i) (y j - pentBipyramid j)
      + inner ℝ (y i - pentBipyramid i) (pentBipyramid j)
      + inner ℝ (y i - pentBipyramid i) (y j - pentBipyramid j) := by
  unfold tau gP
  simp only [inner_sub_left, inner_sub_right]
  ring

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

lemma c1_lt_one : c1 < 1 := by
  have h6 := sqrt5_hi
  unfold c1
  linarith

lemma c2_lt_one : c2 < 1 := by
  have h5 := sqrt5_lo
  unfold c2
  linarith

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

lemma phi_c1_le : phi c1 ≤ 8507 / 10000 := by
  have := phi_c1_box.2
  linarith

lemma phi_c2_le : phi c2 ≤ 8507 / 10000 := by
  have := phi_c2_box.2
  linarith

lemma phi_zero_le : phi 0 ≤ 8507 / 10000 := by
  have := phi_zero_box.2
  linarith

lemma phi_neg_one_le : phi (-1) ≤ 8507 / 10000 := by
  rw [phi_neg_one]; norm_num
lemma pb_0_1 : phi (gP 0 1) ≤ 8507 / 10000 := by
  rw [gP_0_1]; exact phi_c1_le

lemma pb_0_2 : phi (gP 0 2) ≤ 8507 / 10000 := by
  rw [gP_0_2]; exact phi_c2_le

lemma pb_0_3 : phi (gP 0 3) ≤ 8507 / 10000 := by
  rw [gP_0_3]; exact phi_c2_le

lemma pb_0_4 : phi (gP 0 4) ≤ 8507 / 10000 := by
  rw [gP_0_4]; exact phi_c1_le

lemma pb_0_5 : phi (gP 0 5) ≤ 8507 / 10000 := by
  rw [gP_0_5]; exact phi_zero_le

lemma pb_0_6 : phi (gP 0 6) ≤ 8507 / 10000 := by
  rw [gP_0_6]; exact phi_zero_le

lemma pb_1_2 : phi (gP 1 2) ≤ 8507 / 10000 := by
  rw [gP_1_2]; exact phi_c1_le

lemma pb_1_3 : phi (gP 1 3) ≤ 8507 / 10000 := by
  rw [gP_1_3]; exact phi_c2_le

lemma pb_1_4 : phi (gP 1 4) ≤ 8507 / 10000 := by
  rw [gP_1_4]; exact phi_c2_le

lemma pb_1_5 : phi (gP 1 5) ≤ 8507 / 10000 := by
  rw [gP_1_5]; exact phi_zero_le

lemma pb_1_6 : phi (gP 1 6) ≤ 8507 / 10000 := by
  rw [gP_1_6]; exact phi_zero_le

lemma pb_2_3 : phi (gP 2 3) ≤ 8507 / 10000 := by
  rw [gP_2_3]; exact phi_c1_le

lemma pb_2_4 : phi (gP 2 4) ≤ 8507 / 10000 := by
  rw [gP_2_4]; exact phi_c2_le

lemma pb_2_5 : phi (gP 2 5) ≤ 8507 / 10000 := by
  rw [gP_2_5]; exact phi_zero_le

lemma pb_2_6 : phi (gP 2 6) ≤ 8507 / 10000 := by
  rw [gP_2_6]; exact phi_zero_le

lemma pb_3_4 : phi (gP 3 4) ≤ 8507 / 10000 := by
  rw [gP_3_4]; exact phi_c1_le

lemma pb_3_5 : phi (gP 3 5) ≤ 8507 / 10000 := by
  rw [gP_3_5]; exact phi_zero_le

lemma pb_3_6 : phi (gP 3 6) ≤ 8507 / 10000 := by
  rw [gP_3_6]; exact phi_zero_le

lemma pb_4_5 : phi (gP 4 5) ≤ 8507 / 10000 := by
  rw [gP_4_5]; exact phi_zero_le

lemma pb_4_6 : phi (gP 4 6) ≤ 8507 / 10000 := by
  rw [gP_4_6]; exact phi_zero_le

lemma pb_5_6 : phi (gP 5 6) ≤ 8507 / 10000 := by
  rw [gP_5_6]; exact phi_neg_one_le

/-- Per-pair remainder bound: with `τ = t1 + q`, `|t1| ≤ ρᵢ + ρⱼ`, `|q| ≤ ρᵢρⱼ`, `ρ ≤ r ≤ 1/1000`,
`3/2 A τ² + 5/2 B τ³ - 3/2 A t1² ≥ -(3A + 10.1 B) r (ρᵢ² + ρⱼ²)` for `A, B ≥ 0`. -/
lemma pair_rem {A B t1 q ri rj r : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hri : 0 ≤ ri) (hrj : 0 ≤ rj)
    (hri' : ri ≤ r) (hrj' : rj ≤ r) (hr : r ≤ 1 / 1000)
    (ht1 : |t1| ≤ ri + rj) (hq : |q| ≤ ri * rj) :
    -((3 * A + 101 / 10 * B) * r * (ri ^ 2 + rj ^ 2))
      ≤ 3 / 2 * A * (t1 + q) ^ 2 + 5 / 2 * B * (t1 + q) ^ 3 - 3 / 2 * A * t1 ^ 2 := by
  have hr0 : 0 ≤ r := hri.trans hri'
  have hs0 : 0 ≤ ri + rj := add_nonneg hri hrj
  -- second order part
  have e0 : -(2 * r * (ri ^ 2 + rj ^ 2)) ≤ 2 * t1 * q := by
    have h1 : |t1 * q| ≤ (ri + rj) * (ri * rj) := by
      rw [abs_mul]; exact mul_le_mul ht1 hq (abs_nonneg _) hs0
    have h2 : (ri + rj) * (ri * rj) ≤ r * (ri ^ 2 + rj ^ 2) := by
      nlinarith [mul_nonneg (sub_nonneg.2 hrj') (sq_nonneg ri),
        mul_nonneg (sub_nonneg.2 hri') (sq_nonneg rj)]
    have h3 := neg_abs_le (t1 * q)
    nlinarith
  have e1 : -(2 * r * (ri ^ 2 + rj ^ 2)) ≤ (t1 + q) ^ 2 - t1 ^ 2 := by
    nlinarith [sq_nonneg q]
  -- third order part
  have hτ : |t1 + q| ≤ (1 + r) * (ri + rj) := by
    have h1 : |t1 + q| ≤ |t1| + |q| := abs_add_le _ _
    have h2 : ri * rj ≤ r * (ri + rj) := by
      nlinarith [mul_nonneg hri (sub_nonneg.2 hrj'), mul_nonneg hrj hri]
    nlinarith
  have hσ : ri + rj ≤ 2 * r := by linarith
  have h3a : |t1 + q| ^ 3 ≤ ((1 + r) * (ri + rj)) ^ 3 :=
    pow_le_pow_left₀ (abs_nonneg _) hτ 3
  have h3b : ((1 + r) * (ri + rj)) ^ 3 ≤ 4 * r * (1 + r) ^ 3 * (ri ^ 2 + rj ^ 2) := by
    have h1 : (ri + rj) ^ 2 ≤ 2 * (ri ^ 2 + rj ^ 2) := by nlinarith [sq_nonneg (ri - rj)]
    have h2 : (ri + rj) ^ 3 ≤ 2 * (ri ^ 2 + rj ^ 2) * (2 * r) := by
      calc (ri + rj) ^ 3 = (ri + rj) ^ 2 * (ri + rj) := by ring
        _ ≤ (2 * (ri ^ 2 + rj ^ 2)) * (2 * r) :=
          mul_le_mul h1 hσ hs0 (by positivity)
    have h4 : 0 ≤ (1 + r) ^ 3 := by positivity
    calc ((1 + r) * (ri + rj)) ^ 3 = (1 + r) ^ 3 * (ri + rj) ^ 3 := by ring
      _ ≤ (1 + r) ^ 3 * (2 * (ri ^ 2 + rj ^ 2) * (2 * r)) := mul_le_mul_of_nonneg_left h2 h4
      _ = 4 * r * (1 + r) ^ 3 * (ri ^ 2 + rj ^ 2) := by ring
  have h3c : 4 * r * (1 + r) ^ 3 * (ri ^ 2 + rj ^ 2) ≤ 402 / 100 * r * (ri ^ 2 + rj ^ 2) := by
    have : (1 + r) ^ 3 ≤ 1005 / 1000 := by nlinarith [sq_nonneg r]
    have h5 : 0 ≤ r * (ri ^ 2 + rj ^ 2) := by positivity
    nlinarith
  have e2 : -(402 / 100 * r * (ri ^ 2 + rj ^ 2)) ≤ (t1 + q) ^ 3 := by
    have := neg_abs_le ((t1 + q) ^ 3)
    have h6 : |(t1 + q) ^ 3| = |t1 + q| ^ 3 := abs_pow _ _
    linarith
  have f1 := mul_le_mul_of_nonneg_left e1 (by positivity : 0 ≤ 3 / 2 * A)
  have f2 := mul_le_mul_of_nonneg_left e2 (by positivity : 0 ≤ 5 / 2 * B)
  have h7 : 0 ≤ A * (r * (ri ^ 2 + rj ^ 2)) := by positivity
  have h8 : 0 ≤ B * (r * (ri ^ 2 + rj ^ 2)) := by positivity
  nlinarith [f1, f2, h7, h8]

lemma Dpair_lower {y : Fin 7 → R3} {r : ℝ} (hr : r ≤ 1 / 1000)
    (hρ : ∀ i, ‖y i - pentBipyramid i‖ ≤ r) {i j : Fin 7} (hij : i ≠ j)
    (hφ : phi (gP i j) ≤ 8507 / 10000) :
    -(23 / 5 * r * (‖y i - pentBipyramid i‖ ^ 2 + ‖y j - pentBipyramid j‖ ^ 2))
      ≤ Dpair y i j := by
  have hA0 : 0 ≤ phi (gP i j) := (phi_pos (gP_lt_one hij)).le
  have hA : phi (gP i j) ^ 5 ≤ 4456 / 10000 := by
    have := pow_le_pow_left₀ hA0 hφ 5
    refine this.trans ?_
    norm_num
  have hB : phi (gP i j) ^ 7 ≤ 3225 / 10000 := by
    have := pow_le_pow_left₀ hA0 hφ 7
    refine this.trans ?_
    norm_num
  have ht1 : |inner ℝ (pentBipyramid i) (y j - pentBipyramid j)
        + inner ℝ (y i - pentBipyramid i) (pentBipyramid j)|
      ≤ ‖y i - pentBipyramid i‖ + ‖y j - pentBipyramid j‖ := by
    calc _ ≤ |inner ℝ (pentBipyramid i) (y j - pentBipyramid j)|
          + |inner ℝ (y i - pentBipyramid i) (pentBipyramid j)| := abs_add_le _ _
      _ ≤ ‖pentBipyramid i‖ * ‖y j - pentBipyramid j‖
          + ‖y i - pentBipyramid i‖ * ‖pentBipyramid j‖ :=
        add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
      _ = _ := by rw [pent_norm i, pent_norm j]; ring
  have hq : |inner ℝ (y i - pentBipyramid i) (y j - pentBipyramid j)|
      ≤ ‖y i - pentBipyramid i‖ * ‖y j - pentBipyramid j‖ := abs_real_inner_le_norm _ _
  have h := pair_rem (A := phi (gP i j) ^ 5) (B := phi (gP i j) ^ 7) (r := r)
    (pow_nonneg hA0 5) (pow_nonneg hA0 7) (norm_nonneg _) (norm_nonneg _) (hρ i) (hρ j) hr ht1 hq
  have hw : 3 * phi (gP i j) ^ 5 + 101 / 10 * phi (gP i j) ^ 7 ≤ 23 / 5 := by linarith
  have hr0 : 0 ≤ r := (norm_nonneg _).trans (hρ i)
  have hnn : 0 ≤ r * (‖y i - pentBipyramid i‖ ^ 2 + ‖y j - pentBipyramid j‖ ^ 2) := by positivity
  have h2 := mul_le_mul_of_nonneg_right hw hnn
  unfold Dpair
  rw [tau_expand y i j]
  linarith [h, h2]

lemma sum_Dpair_lower {y : Fin 7 → R3} {r : ℝ} (hr : r ≤ 1 / 1000)
    (hρ : ∀ i, ‖y i - pentBipyramid i‖ ≤ r) :
    -(28 * r * ∑ i, ‖y i - pentBipyramid i‖ ^ 2)
      ≤ ∑ i, ∑ j ∈ Finset.Ioi i, Dpair y i j := by
  have hr0 : 0 ≤ r := (norm_nonneg _).trans (hρ 0)
  rw [sum_Ioi_seven (fun i j => Dpair y i j)]
  have p01 := Dpair_lower hr hρ (i := 0) (j := 1) (by decide) pb_0_1
  have p02 := Dpair_lower hr hρ (i := 0) (j := 2) (by decide) pb_0_2
  have p03 := Dpair_lower hr hρ (i := 0) (j := 3) (by decide) pb_0_3
  have p04 := Dpair_lower hr hρ (i := 0) (j := 4) (by decide) pb_0_4
  have p05 := Dpair_lower hr hρ (i := 0) (j := 5) (by decide) pb_0_5
  have p06 := Dpair_lower hr hρ (i := 0) (j := 6) (by decide) pb_0_6
  have p12 := Dpair_lower hr hρ (i := 1) (j := 2) (by decide) pb_1_2
  have p13 := Dpair_lower hr hρ (i := 1) (j := 3) (by decide) pb_1_3
  have p14 := Dpair_lower hr hρ (i := 1) (j := 4) (by decide) pb_1_4
  have p15 := Dpair_lower hr hρ (i := 1) (j := 5) (by decide) pb_1_5
  have p16 := Dpair_lower hr hρ (i := 1) (j := 6) (by decide) pb_1_6
  have p23 := Dpair_lower hr hρ (i := 2) (j := 3) (by decide) pb_2_3
  have p24 := Dpair_lower hr hρ (i := 2) (j := 4) (by decide) pb_2_4
  have p25 := Dpair_lower hr hρ (i := 2) (j := 5) (by decide) pb_2_5
  have p26 := Dpair_lower hr hρ (i := 2) (j := 6) (by decide) pb_2_6
  have p34 := Dpair_lower hr hρ (i := 3) (j := 4) (by decide) pb_3_4
  have p35 := Dpair_lower hr hρ (i := 3) (j := 5) (by decide) pb_3_5
  have p36 := Dpair_lower hr hρ (i := 3) (j := 6) (by decide) pb_3_6
  have p45 := Dpair_lower hr hρ (i := 4) (j := 5) (by decide) pb_4_5
  have p46 := Dpair_lower hr hρ (i := 4) (j := 6) (by decide) pb_4_6
  have p56 := Dpair_lower hr hρ (i := 5) (j := 6) (by decide) pb_5_6
  simp only [Fin.sum_univ_seven]
  have hS : 0 ≤ r * (‖y 0 - pentBipyramid 0‖ ^ 2 + ‖y 1 - pentBipyramid 1‖ ^ 2
      + ‖y 2 - pentBipyramid 2‖ ^ 2 + ‖y 3 - pentBipyramid 3‖ ^ 2 + ‖y 4 - pentBipyramid 4‖ ^ 2
      + ‖y 5 - pentBipyramid 5‖ ^ 2 + ‖y 6 - pentBipyramid 6‖ ^ 2) := by positivity
  linarith

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
theorem solution {y : Fin 7 → R3} {r : ℝ} (hr : r ≤ 1 / 1000)
    (hρ : ∀ i, ‖y i - pentBipyramid i‖ ≤ r) :
    -(28 * r * ∑ i, ‖y i - pentBipyramid i‖ ^ 2)
      ≤ ∑ i, ∑ j ∈ Finset.Ioi i, Reg.Dpair y i j :=
  ThomsonN7.Reg.sum_Dpair_lower hr hρ
