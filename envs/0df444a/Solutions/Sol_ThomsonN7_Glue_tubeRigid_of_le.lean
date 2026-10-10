-- Prove2me | solution 1 for ThomsonN7.Glue.tubeRigid_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-10-10T02:09:09.536274+00:00
-- url     : https://prove2.me/submissions/87355cbc-33b3-4142-bd50-1d2346b322ea

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

lemma pent_cases (i : Fin 7) : (i : ℕ) < 5 ∨ i = 5 ∨ i = 6 := by
  fin_cases i <;> simp

/- BEGIN M0 -/
namespace Base

open Finset

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

lemma det4h_scale {R : Type*} [CommRing R] (s δ p01 p02 p03 p12 p13 p23 : R) :
    det4h (s * δ) (s * p01) (s * p02) (s * p03) (s * p12) (s * p13) (s * p23) =
      s ^ 4 * det4h δ p01 p02 p03 p12 p13 p23 := by
  unfold det4h; ring

lemma det_fin_four_unit (p01 p02 p03 p12 p13 p23 : ℝ) :
    Matrix.det !![1, p01, p02, p03; p01, 1, p12, p13; p02, p12, 1, p23; p03, p13, p23, 1] =
      det4h 1 p01 p02 p03 p12 p13 p23 := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, det4h, Fin.succAbove]
  ring

/-- Four unit vectors of `ℝ³` have vanishing Gram determinant. -/
lemma det4h_inner_eq_zero (u : Fin 4 → R3) (hu : ∀ i, ‖u i‖ = 1) :
    det4h 1 (⟪u 0, u 1⟫_ℝ) (⟪u 0, u 2⟫_ℝ) (⟪u 0, u 3⟫_ℝ) (⟪u 1, u 2⟫_ℝ) (⟪u 1, u 3⟫_ℝ)
      (⟪u 2, u 3⟫_ℝ) = 0 := by
  have h0 : (Matrix.gram ℝ u).det = 0 := by
    by_contra h
    have := (Matrix.linearIndependent_of_det_gram_ne_zero h).fintype_card_le_finrank
    simp at this
  have hm : Matrix.gram ℝ u = !![1, ⟪u 0, u 1⟫_ℝ, ⟪u 0, u 2⟫_ℝ, ⟪u 0, u 3⟫_ℝ;
      ⟪u 0, u 1⟫_ℝ, 1, ⟪u 1, u 2⟫_ℝ, ⟪u 1, u 3⟫_ℝ;
      ⟪u 0, u 2⟫_ℝ, ⟪u 1, u 2⟫_ℝ, 1, ⟪u 2, u 3⟫_ℝ;
      ⟪u 0, u 3⟫_ℝ, ⟪u 1, u 3⟫_ℝ, ⟪u 2, u 3⟫_ℝ, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.gram_apply, hu] <;>
      exact real_inner_comm _ _
  rw [hm, det_fin_four_unit] at h0
  exact h0

lemma inner_cyl (ρ θ h ρ' θ' h' : ℝ) :
    ⟪cyl ρ θ h, cyl ρ' θ' h'⟫_ℝ = ρ * ρ' * cos (θ - θ') + h * h' := by
  simp [cyl, PiLp.inner_apply, Fin.sum_univ_three, cos_sub]
  ring

lemma cos_two_pi_div_five : cos (2 * π / 5) = cosB := by
  have h : 2 * π / 5 = 2 * (π / 5) := by ring
  rw [h, cos_two_mul, cos_pi_div_five, cosB]
  have : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith

lemma cos_four_pi_div_five : cos (4 * π / 5) = cosA := by
  have h : 4 * π / 5 = π - π / 5 := by ring
  rw [h, cos_pi_sub, cos_pi_div_five, cosA]
  ring

lemma cos_six_pi_div_five : cos (6 * π / 5) = cosA := by
  have h : 6 * π / 5 = π / 5 + π := by ring
  rw [h, cos_add_pi, cos_pi_div_five, cosA]
  ring

lemma cos_eight_pi_div_five : cos (8 * π / 5) = cosB := by
  have h : 8 * π / 5 = 2 * π - 2 * π / 5 := by ring
  rw [h, cos_two_pi_sub, cos_two_pi_div_five]

lemma cos_pent_diff (d : ℤ) (h1 : -4 ≤ d) (h2 : d ≤ 4) :
    cos (d * (2 * π / 5)) =
      if d = 0 then 1 else if d % 5 = 1 ∨ d % 5 = 4 then cosB else cosA := by
  have : d = -4 ∨ d = -3 ∨ d = -2 ∨ d = -1 ∨ d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show ((-4 : ℤ) : ℝ) * (2 * π / 5) = -(8 * π / 5) by push_cast; ring, cos_neg,
      cos_eight_pi_div_five]
    norm_num
  · rw [show ((-3 : ℤ) : ℝ) * (2 * π / 5) = -(6 * π / 5) by push_cast; ring, cos_neg,
      cos_six_pi_div_five]
    norm_num
  · rw [show ((-2 : ℤ) : ℝ) * (2 * π / 5) = -(4 * π / 5) by push_cast; ring, cos_neg,
      cos_four_pi_div_five]
    norm_num
  · rw [show ((-1 : ℤ) : ℝ) * (2 * π / 5) = -(2 * π / 5) by push_cast; ring, cos_neg,
      cos_two_pi_div_five]
    norm_num
  · simp
  · rw [show ((1 : ℤ) : ℝ) * (2 * π / 5) = 2 * π / 5 by push_cast; ring, cos_two_pi_div_five]
    norm_num
  · rw [show ((2 : ℤ) : ℝ) * (2 * π / 5) = 4 * π / 5 by push_cast; ring, cos_four_pi_div_five]
    norm_num
  · rw [show ((3 : ℤ) : ℝ) * (2 * π / 5) = 6 * π / 5 by push_cast; ring, cos_six_pi_div_five]
    norm_num
  · rw [show ((4 : ℤ) : ℝ) * (2 * π / 5) = 8 * π / 5 by push_cast; ring, cos_eight_pi_div_five]
    norm_num

lemma cos_pent (k l : ℕ) (hk : k < 5) (hl : l < 5) :
    cos (2 * π * k / 5 - 2 * π * l / 5) =
      if k = l then 1 else if (k + 5 - l) % 5 = 1 ∨ (l + 5 - k) % 5 = 1 then cosB else cosA := by
  have e : 2 * π * k / 5 - 2 * π * l / 5 = (((k : ℤ) - l : ℤ) : ℝ) * (2 * π / 5) := by
    push_cast; ring
  rw [e, cos_pent_diff ((k : ℤ) - l) (by omega) (by omega)]
  split_ifs <;> first | rfl | omega

lemma cP_pent_pole : ∀ k : Fin 7, (k : ℕ) < 5 →
    cP k 5 = 2 ∧ cP k 6 = 2 ∧ cP 5 k = 2 ∧ cP 6 k = 2 := by
  decide

lemma inner_P_pent {k l : Fin 7} (hk : (k : ℕ) < 5) (hl : (l : ℕ) < 5) :
    ⟪pentBipyramid k, pentBipyramid l⟫_ℝ = if k = l then 1 else val (cP k l) := by
  rw [pent_of_lt hk, pent_of_lt hl, inner_cyl, cos_pent _ _ hk hl]
  have hc : cP k l = if ((k : ℕ) + 5 - l) % 5 = 1 ∨ ((l : ℕ) + 5 - k) % 5 = 1 then 3 else 1 := by
    simp [cP, hk, hl]
  rw [hc]
  by_cases h : k = l
  · subst h; simp
  · have h' : (k : ℕ) ≠ l := fun e => h (Fin.ext e)
    rw [if_neg h, if_neg h']
    split_ifs <;> simp [val]

/-- The Gram matrix of the pentagonal bipyramid in terms of the contact values. -/
lemma inner_P (k l : Fin 7) :
    ⟪pentBipyramid k, pentBipyramid l⟫_ℝ = if k = l then 1 else val (cP k l) := by
  rcases pent_cases k with hk | rfl | rfl <;> rcases pent_cases l with hl | rfl | rfl
  · exact inner_P_pent hk hl
  · obtain ⟨h5, -, -, -⟩ := cP_pent_pole k hk
    have hne : k ≠ 5 := by rintro rfl; simp at hk
    rw [pent_of_lt hk, pent_five, inner_cyl, if_neg hne, h5]
    simp [val]
  · obtain ⟨-, h6, -, -⟩ := cP_pent_pole k hk
    have hne : k ≠ 6 := by rintro rfl; simp at hk
    rw [pent_of_lt hk, pent_six, inner_cyl, if_neg hne, h6]
    simp [val]
  · obtain ⟨-, -, h5, -⟩ := cP_pent_pole l hl
    have hne : (5 : Fin 7) ≠ l := by rintro rfl; simp at hl
    rw [pent_of_lt hl, pent_five, inner_cyl, if_neg hne, h5]
    simp [val]
  · rw [pent_five, inner_cyl, if_pos rfl]; norm_num
  · have h56 : cP 5 6 = 0 := by decide
    rw [pent_five, pent_six, inner_cyl, if_neg (by decide), h56]
    simp [val]
  · obtain ⟨-, -, -, h6⟩ := cP_pent_pole l hl
    have hne : (6 : Fin 7) ≠ l := by rintro rfl; simp at hl
    rw [pent_of_lt hl, pent_six, inner_cyl, if_neg hne, h6]
    simp [val]
  · have h65 : cP 6 5 = 0 := by decide
    rw [pent_six, pent_five, inner_cyl, if_neg (by decide), h65]
    simp [val]
  · rw [pent_six, inner_cyl, if_pos rfl]; norm_num

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

lemma iadd_mem {a b : ℤ × ℤ} {x y : ℝ} (hx : Imem a x) (hy : Imem b y) :
    Imem (iadd a b) (x + y) := by
  unfold Imem iadd at *
  push_cast
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

lemma iscale_mem {a : ℤ × ℤ} {x : ℝ} (c : ℤ) (hx : Imem a x) :
    Imem (iscale c a) (c * x) := by
  unfold Imem iscale at *
  by_cases hc : 0 ≤ c
  · have hc' : (0 : ℝ) ≤ c := by exact_mod_cast hc
    simp only [hc, ite_true]
    push_cast
    constructor <;> nlinarith [hx.1, hx.2]
  · have hc' : (c : ℝ) ≤ 0 := by exact_mod_cast (not_le.mp hc).le
    simp only [hc, ite_false]
    push_cast
    constructor <;> nlinarith [hx.1, hx.2]

lemma mul_ge_min4 {x y a1 a2 b1 b2 : ℝ} (hx1 : a1 ≤ x) (hx2 : x ≤ a2) (hy1 : b1 ≤ y)
    (hy2 : y ≤ b2) : min (min (a1 * b1) (a1 * b2)) (min (a2 * b1) (a2 * b2)) ≤ x * y := by
  rcases le_total 0 y with hy | hy
  · have h1 : a1 * y ≤ x * y := mul_le_mul_of_nonneg_right hx1 hy
    rcases le_total 0 a1 with ha | ha
    · have : a1 * b1 ≤ a1 * y := mul_le_mul_of_nonneg_left hy1 ha
      exact le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) (by linarith)
    · have : a1 * b2 ≤ a1 * y := mul_le_mul_of_nonpos_left hy2 ha
      exact le_trans (le_trans (min_le_left _ _) (min_le_right _ _)) (by linarith)
  · have h1 : a2 * y ≤ x * y := mul_le_mul_of_nonpos_right hx2 hy
    rcases le_total 0 a2 with ha | ha
    · have : a2 * b1 ≤ a2 * y := mul_le_mul_of_nonneg_left hy1 ha
      exact le_trans (le_trans (min_le_right _ _) (min_le_left _ _)) (by linarith)
    · have : a2 * b2 ≤ a2 * y := mul_le_mul_of_nonpos_left hy2 ha
      exact le_trans (le_trans (min_le_right _ _) (min_le_right _ _)) (by linarith)

lemma mul_le_max4 {x y a1 a2 b1 b2 : ℝ} (hx1 : a1 ≤ x) (hx2 : x ≤ a2) (hy1 : b1 ≤ y)
    (hy2 : y ≤ b2) : x * y ≤ max (max (a1 * b1) (a1 * b2)) (max (a2 * b1) (a2 * b2)) := by
  have := mul_ge_min4 (x := -x) (y := y) (a1 := -a2) (a2 := -a1) (b1 := b1) (b2 := b2)
    (by linarith) (by linarith) hy1 hy2
  have e : min (min (-a2 * b1) (-a2 * b2)) (min (-a1 * b1) (-a1 * b2)) =
      -max (max (a1 * b1) (a1 * b2)) (max (a2 * b1) (a2 * b2)) := by
    simp only [neg_mul, ← min_neg_neg]
    rw [min_comm (min _ _) (min _ _)]
  rw [e] at this
  linarith

lemma imul_mem {a b : ℤ × ℤ} {x y : ℝ} (hx : Imem a x) (hy : Imem b y) :
    Imem (imul a b) (x * y) := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  constructor
  · have := mul_ge_min4 hx1 hx2 hy1 hy2
    dsimp only [imul]
    push_cast [Int.cast_min]
    exact this
  · have := mul_le_max4 hx1 hx2 hy1 hy2
    dsimp only [imul]
    push_cast [Int.cast_max]
    exact this

lemma isq_mem {a : ℤ × ℤ} {x : ℝ} (hx : Imem a x) : Imem (isq a) (x ^ 2) := by
  obtain ⟨hx1, hx2⟩ := hx
  unfold isq
  split_ifs with h1 h2
  · have h1' : (0 : ℝ) ≤ a.1 := by exact_mod_cast h1
    show ((a.1 * a.1 : ℤ) : ℝ) ≤ x ^ 2 ∧ x ^ 2 ≤ ((a.2 * a.2 : ℤ) : ℝ)
    push_cast
    constructor <;> nlinarith
  · have h2' : (a.2 : ℝ) ≤ 0 := by exact_mod_cast h2
    show ((a.2 * a.2 : ℤ) : ℝ) ≤ x ^ 2 ∧ x ^ 2 ≤ ((a.1 * a.1 : ℤ) : ℝ)
    push_cast
    constructor <;> nlinarith
  · show ((0 : ℤ) : ℝ) ≤ x ^ 2 ∧ x ^ 2 ≤ ((max (a.1 * a.1) (a.2 * a.2) : ℤ) : ℝ)
    push_cast [Int.cast_max]
    constructor
    · positivity
    · rcases le_total 0 x with h | h
      · exact le_trans (by nlinarith) (le_max_right _ _)
      · exact le_trans (by nlinarith) (le_max_left _ _)

/-! ### Homogeneous Gram determinants and their interval enclosures -/

lemma idet3_mem (δ : ℤ) {A B C : ℤ × ℤ} {a b c : ℝ} (ha : Imem A a) (hb : Imem B b)
    (hc : Imem C c) : Imem (idet3 δ A B C) (det3h (δ : ℝ) a b c) := by
  have h0 : Imem ((δ ^ 3 : ℤ), (δ ^ 3 : ℤ)) ((δ : ℝ) ^ 3) := by
    unfold Imem; push_cast; constructor <;> exact le_refl _
  have h1 := iadd_mem h0 (iscale_mem 2 (imul_mem (imul_mem ha hb) hc))
  have h2 := iscale_mem (-δ) (iadd_mem (iadd_mem (isq_mem ha) (isq_mem hb)) (isq_mem hc))
  have h3 := iadd_mem h1 h2
  have e : (δ : ℝ) ^ 3 + ((2 : ℤ) : ℝ) * (a * b * c) + (((-δ : ℤ) : ℝ) * (a ^ 2 + b ^ 2 + c ^ 2))
      = det3h (δ : ℝ) a b c := by
    unfold det3h; push_cast; ring
  rw [e] at h3
  exact h3

lemma idet4_mem (δ : ℤ) {A B C D E F : ℤ × ℤ} {a b c d e f : ℝ} (ha : Imem A a)
    (hb : Imem B b) (hc : Imem C c) (hd : Imem D d) (he : Imem E e) (hf : Imem F f) :
    Imem (idet4 δ A B C D E F) (det4h (δ : ℝ) a b c d e f) := by
  have h0 : Imem ((δ ^ 4 : ℤ), (δ ^ 4 : ℤ)) ((δ : ℝ) ^ 4) := by
    unfold Imem; push_cast; constructor <;> exact le_refl _
  have sa := isq_mem ha
  have sb := isq_mem hb
  have sc := isq_mem hc
  have sd := isq_mem hd
  have se := isq_mem he
  have sf := isq_mem hf
  have hs := iadd_mem (iadd_mem (iadd_mem sa sb) sc) (iadd_mem (iadd_mem sd se) sf)
  have hq := iadd_mem (iadd_mem (imul_mem sa sf) (imul_mem sb se)) (imul_mem sc sd)
  have ht := iadd_mem (iadd_mem (imul_mem (imul_mem ha hd) hb) (imul_mem (imul_mem ha he) hc))
    (iadd_mem (imul_mem (imul_mem hb hf) hc) (imul_mem (imul_mem hd hf) he))
  have hu := iadd_mem (iadd_mem (imul_mem (imul_mem ha hb) (imul_mem he hf))
    (imul_mem (imul_mem ha hc) (imul_mem hd hf))) (imul_mem (imul_mem hb hc) (imul_mem hd he))
  have h1 := iadd_mem (iadd_mem h0 (iscale_mem (-(δ ^ 2)) hs))
    (iadd_mem hq (iscale_mem (2 * δ) ht))
  have h2 := iadd_mem h1 (iscale_mem (-2) hu)
  have e : (δ : ℝ) ^ 4 + (((-(δ ^ 2) : ℤ) : ℝ) * (a ^ 2 + b ^ 2 + c ^ 2 + (d ^ 2 + e ^ 2 + f ^ 2))) +
      ((a ^ 2 * f ^ 2 + b ^ 2 * e ^ 2 + c ^ 2 * d ^ 2) +
        ((2 * δ : ℤ) : ℝ) * (a * d * b + a * e * c + (b * f * c + d * f * e))) +
      (((-2 : ℤ) : ℝ) * (a * b * (e * f) + a * c * (d * f) + b * c * (d * e))) =
      det4h (δ : ℝ) a b c d e f := by
    unfold det4h; push_cast; ring
  rw [e] at h2
  exact h2

/-! ### Boxes, bisection and the two refutation checkers -/

lemma mid_bounds {I : ℤ × ℤ} (h : I.1 ≤ I.2) : I.1 ≤ mid I ∧ mid I ≤ I.2 := by
  unfold mid; omega

lemma imem_split {I : ℤ × ℤ} {x : ℝ} (h : Imem I x) :
    Imem (I.1, mid I) x ∨ Imem (mid I, I.2) x := by
  have hI : I.1 ≤ I.2 := by
    have := le_trans h.1 h.2
    exact_mod_cast this
  obtain ⟨m1, m2⟩ := mid_bounds hI
  rcases le_total x (mid I : ℝ) with hx | hx
  · exact Or.inl ⟨h.1, hx⟩
  · exact Or.inr ⟨hx, h.2⟩

lemma Box6.mem_split (j : ℕ) {b : Box6} {a₁ a₂ a₃ a₄ a₅ a₆ : ℝ}
    (h : b.Mem a₁ a₂ a₃ a₄ a₅ a₆) :
    (b.split j).1.Mem a₁ a₂ a₃ a₄ a₅ a₆ ∨ (b.split j).2.Mem a₁ a₂ a₃ a₄ a₅ a₆ := by
  obtain ⟨hA, hB, hC, hD, hE, hF⟩ := h
  match j with
  | 0 =>
    rcases imem_split hA with h | h
    · exact Or.inl ⟨h, hB, hC, hD, hE, hF⟩
    · exact Or.inr ⟨h, hB, hC, hD, hE, hF⟩
  | 1 =>
    rcases imem_split hB with h | h
    · exact Or.inl ⟨hA, h, hC, hD, hE, hF⟩
    · exact Or.inr ⟨hA, h, hC, hD, hE, hF⟩
  | 2 =>
    rcases imem_split hC with h | h
    · exact Or.inl ⟨hA, hB, h, hD, hE, hF⟩
    · exact Or.inr ⟨hA, hB, h, hD, hE, hF⟩
  | 3 =>
    rcases imem_split hD with h | h
    · exact Or.inl ⟨hA, hB, hC, h, hE, hF⟩
    · exact Or.inr ⟨hA, hB, hC, h, hE, hF⟩
  | 4 =>
    rcases imem_split hE with h | h
    · exact Or.inl ⟨hA, hB, hC, hD, h, hF⟩
    · exact Or.inr ⟨hA, hB, hC, hD, h, hF⟩
  | n + 5 =>
    rcases imem_split hF with h | h
    · exact Or.inl ⟨hA, hB, hC, hD, hE, h⟩
    · exact Or.inr ⟨hA, hB, hC, hD, hE, h⟩

theorem chk4_sound (δ : ℤ) : ∀ (n : ℕ) (b : Box6) (a₁ a₂ a₃ a₄ a₅ a₆ : ℝ),
    chk4 δ n b = true → b.Mem a₁ a₂ a₃ a₄ a₅ a₆ →
    det4h (δ : ℝ) a₁ a₂ a₃ a₄ a₅ a₆ ≠ 0 ∨ det3h (δ : ℝ) a₁ a₂ a₄ < 0 ∨
      det3h (δ : ℝ) a₁ a₃ a₅ < 0 ∨ det3h (δ : ℝ) a₂ a₃ a₆ < 0 ∨ det3h (δ : ℝ) a₄ a₅ a₆ < 0 := by
  intro n
  induction n with
  | zero => intro b a₁ a₂ a₃ a₄ a₅ a₆ h; simp [chk4] at h
  | succ n ih =>
    intro b a₁ a₂ a₃ a₄ a₅ a₆ h hm
    obtain ⟨hA, hB, hC, hD, hE, hF⟩ := hm
    have m4 := idet4_mem δ hA hB hC hD hE hF
    have t1 := idet3_mem δ hA hB hD
    have t2 := idet3_mem δ hA hC hE
    have t3 := idet3_mem δ hB hC hF
    have t4 := idet3_mem δ hD hE hF
    simp only [chk4, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ((((((h | h) | h) | h) | h) | h) | h)
    · left
      have := m4.1
      have h' : (0 : ℝ) < ((idet4 δ b.A b.B b.C b.D b.E b.F).1 : ℝ) := by exact_mod_cast h
      exact ne_of_gt (lt_of_lt_of_le h' this)
    · left
      have := m4.2
      have h' : ((idet4 δ b.A b.B b.C b.D b.E b.F).2 : ℝ) < 0 := by exact_mod_cast h
      exact ne_of_lt (lt_of_le_of_lt this h')
    · right; left
      have h' : ((idet3 δ b.A b.B b.D).2 : ℝ) < 0 := by exact_mod_cast h
      exact lt_of_le_of_lt t1.2 h'
    · right; right; left
      have h' : ((idet3 δ b.A b.C b.E).2 : ℝ) < 0 := by exact_mod_cast h
      exact lt_of_le_of_lt t2.2 h'
    · right; right; right; left
      have h' : ((idet3 δ b.B b.C b.F).2 : ℝ) < 0 := by exact_mod_cast h
      exact lt_of_le_of_lt t3.2 h'
    · right; right; right; right
      have h' : ((idet3 δ b.D b.E b.F).2 : ℝ) < 0 := by exact_mod_cast h
      exact lt_of_le_of_lt t4.2 h'
    · obtain ⟨h1, h2⟩ := h
      rcases Box6.mem_split (widest b) ⟨hA, hB, hC, hD, hE, hF⟩ with hs | hs
      · exact ih _ _ _ _ _ _ _ h1 hs
      · exact ih _ _ _ _ _ _ _ h2 hs

end M6
end ThomsonN7

open scoped InnerProductSpace

namespace ThomsonN7
namespace T4

open M6

/-- The Gram determinant of three unit vectors is non-negative. -/
lemma det3h_nonneg (u v w : R3) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    0 ≤ det3h (1 : ℝ) ⟪u, v⟫_ℝ ⟪u, w⟫_ℝ ⟪v, w⟫_ℝ := by
  have h := (Matrix.posSemidef_gram ℝ ![u, v, w]).det_nonneg
  rw [Matrix.det_fin_three] at h
  simp [Matrix.gram_apply, hu, hv, hw, real_inner_comm u v, real_inner_comm u w,
    real_inner_comm v w] at h
  unfold det3h
  nlinarith [h]

/-- Four unit vectors of `ℝ³` whose six pairwise inner products (times `1000`) lie in a box
certified by `chk4` cannot exist. -/
lemma box_exclude (n : ℕ) (bx : Box6) (hbx : chk4 1000 n bx = true) (e a b c : R3)
    (he : ‖e‖ = 1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hm : bx.Mem (1000 * ⟪e, a⟫_ℝ) (1000 * ⟪e, b⟫_ℝ) (1000 * ⟪e, c⟫_ℝ)
      (1000 * ⟪a, b⟫_ℝ) (1000 * ⟪a, c⟫_ℝ) (1000 * ⟪b, c⟫_ℝ)) : False := by
  have hz := M3.det4h_inner_eq_zero ![e, a, b, c]
    (by intro i; fin_cases i <;> simp [he, ha, hb, hc])
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hz
  have hs := chk4_sound 1000 n bx _ _ _ _ _ _ hbx hm
  have h4 : det4h ((1000 : ℤ) : ℝ) (1000 * ⟪e, a⟫_ℝ) (1000 * ⟪e, b⟫_ℝ) (1000 * ⟪e, c⟫_ℝ)
      (1000 * ⟪a, b⟫_ℝ) (1000 * ⟪a, c⟫_ℝ) (1000 * ⟪b, c⟫_ℝ) = 0 := by
    have := M3.det4h_scale (1000 : ℝ) 1 ⟪e, a⟫_ℝ ⟪e, b⟫_ℝ ⟪e, c⟫_ℝ ⟪a, b⟫_ℝ ⟪a, c⟫_ℝ ⟪b, c⟫_ℝ
    rw [hz, mul_zero, mul_one] at this
    unfold det4h
    unfold M3.det4h at this
    push_cast
    linarith
  have s3 : ∀ x y z : ℝ, det3h ((1000 : ℤ) : ℝ) (1000 * x) (1000 * y) (1000 * z) =
      1000 ^ 3 * det3h 1 x y z := by
    intro x y z; unfold det3h; push_cast; ring
  rw [s3, s3, s3, s3] at hs
  have n1 := det3h_nonneg e a b he ha hb
  have n2 := det3h_nonneg e a c he ha hc
  have n3 := det3h_nonneg e b c he hb hc
  have n4 := det3h_nonneg a b c ha hb hc
  rcases hs with h | h | h | h | h
  · exact h h4
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith

lemma imem_of {lo hi : ℤ} {x : ℝ} (h1 : (lo : ℝ) ≤ x) (h2 : x ≤ hi) : Imem (lo, hi) x :=
  ⟨h1, h2⟩

lemma sqrt5_bounds : (2.236 : ℝ) < √5 ∧ √5 < 2.237 := by
  have h0 : (0 : ℝ) ≤ √5 := Real.sqrt_nonneg 5
  have h1 : √5 * √5 = 5 := Real.mul_self_sqrt (by norm_num)
  constructor <;> nlinarith

/-- No three ring vectors with mutual inner products all near `cos (2π/5)` (together with a
vector nearly orthogonal to all three). -/
lemma no_mono_cosB {τ : ℝ} (hτ : τ ≤ 1 / 10) (e a b c : R3)
    (he : ‖e‖ = 1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hea : |⟪e, a⟫_ℝ| ≤ τ) (heb : |⟪e, b⟫_ℝ| ≤ τ) (hec : |⟪e, c⟫_ℝ| ≤ τ)
    (hab : |⟪a, b⟫_ℝ - M3.cosB| ≤ τ) (hac : |⟪a, c⟫_ℝ - M3.cosB| ≤ τ)
    (hbc : |⟪b, c⟫_ℝ - M3.cosB| ≤ τ) : False := by
  refine box_exclude 1 ⟨(-100, 100), (-100, 100), (-100, 100), (209, 410), (209, 410), (209, 410)⟩
    (by decide) e a b c he ha hb hc ?_
  obtain ⟨s1, s2⟩ := sqrt5_bounds
  have hB : M3.cosB = (√5 - 1) / 4 := rfl
  rw [hB] at hab hac hbc
  obtain ⟨a1, a2⟩ := abs_le.1 hea
  obtain ⟨b1, b2⟩ := abs_le.1 heb
  obtain ⟨c1, c2⟩ := abs_le.1 hec
  obtain ⟨d1, d2⟩ := abs_le.1 hab
  obtain ⟨e1, e2⟩ := abs_le.1 hac
  obtain ⟨f1, f2⟩ := abs_le.1 hbc
  unfold Box6.Mem
  refine ⟨imem_of ?_ ?_, imem_of ?_ ?_, imem_of ?_ ?_, imem_of ?_ ?_, imem_of ?_ ?_,
    imem_of ?_ ?_⟩ <;> push_cast <;> linarith

/-- No three ring vectors with mutual inner products all near `cos (4π/5)` (together with a
vector nearly orthogonal to all three). -/
lemma no_mono_cosA {τ : ℝ} (hτ : τ ≤ 1 / 10) (e a b c : R3)
    (he : ‖e‖ = 1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hea : |⟪e, a⟫_ℝ| ≤ τ) (heb : |⟪e, b⟫_ℝ| ≤ τ) (hec : |⟪e, c⟫_ℝ| ≤ τ)
    (hab : |⟪a, b⟫_ℝ - M3.cosA| ≤ τ) (hac : |⟪a, c⟫_ℝ - M3.cosA| ≤ τ)
    (hbc : |⟪b, c⟫_ℝ - M3.cosA| ≤ τ) : False := by
  refine box_exclude 1
    ⟨(-100, 100), (-100, 100), (-100, 100), (-910, -709), (-910, -709), (-910, -709)⟩
    (by decide) e a b c he ha hb hc ?_
  obtain ⟨s1, s2⟩ := sqrt5_bounds
  have hA : M3.cosA = -(1 + √5) / 4 := rfl
  rw [hA] at hab hac hbc
  obtain ⟨a1, a2⟩ := abs_le.1 hea
  obtain ⟨b1, b2⟩ := abs_le.1 heb
  obtain ⟨c1, c2⟩ := abs_le.1 hec
  obtain ⟨d1, d2⟩ := abs_le.1 hab
  obtain ⟨e1, e2⟩ := abs_le.1 hac
  obtain ⟨f1, f2⟩ := abs_le.1 hbc
  unfold Box6.Mem
  refine ⟨imem_of ?_ ?_, imem_of ?_ ?_, imem_of ?_ ?_, imem_of ?_ ?_, imem_of ?_ ?_,
    imem_of ?_ ?_⟩ <;> push_cast <;> linarith

/-! ### Combinatorics of the ring: a 2-colouring of `K₅` without monochromatic triangle is a pentagon -/

/-- Every 2-colouring of the edges of `K₅` without a monochromatic triangle is a pentagon
(and its complement): finite check over the `2 ^ 10` colourings. -/
theorem comb5_dec : ∀ b01 b02 b03 b04 b12 b13 b14 b23 b24 b34 : Bool,
    triFree (mk10 [b01, b02, b03, b04, b12, b13, b14, b23, b24, b34]) = true →
    isPent (mk10 [b01, b02, b03, b04, b12, b13, b14, b23, b24, b34]) = true := by
  decide

/-! ### The ring colouring of a configuration -/

lemma mk10_col (τ : ℝ) (y : Fin 7 → R3) (a b : Fin 5) (hab : a < b) :
    mk10 [col τ y 0 1, col τ y 0 2, col τ y 0 3, col τ y 0 4, col τ y 1 2, col τ y 1 3,
      col τ y 1 4, col τ y 2 3, col τ y 2 4, col τ y 3 4] a b = col τ y a b := by
  fin_cases a <;> fin_cases b <;> simp [mk10, pidx] at hab ⊢

/-! ### The relabelling of the bipyramid -/

lemma sigEquiv_apply (s : Equiv.Perm (Fin 5)) (i : Fin 7) : sigEquiv s i = sig7 s i := rfl

lemma sig7_zero (s : Equiv.Perm (Fin 5)) : sig7 s 0 = 5 := by simp [sig7]

lemma sig7_one (s : Equiv.Perm (Fin 5)) : sig7 s 1 = 6 := by simp [sig7]

lemma sig7_ring (s : Equiv.Perm (Fin 5)) (a : Fin 5) : sig7 s a.succ.succ = pentIdx (s a) := by
  have h : ¬ (a.succ.succ : Fin 7).val < 2 := by simp
  simp [sig7]

/-! ### Nominal Gram entries of the relabelled bipyramid -/

lemma inner_P_pole_pole : ⟪pentBipyramid 5, pentBipyramid 6⟫_ℝ = -1 := by
  rw [M3.inner_P]
  simp [M3.cP, M3.val]

lemma pentIdx_ne_five (a : Fin 5) : pentIdx a ≠ 5 := by
  intro h
  have := congrArg Fin.val h
  simp [pentIdx] at this
  omega

lemma pentIdx_ne_six (a : Fin 5) : pentIdx a ≠ 6 := by
  intro h
  have := congrArg Fin.val h
  simp [pentIdx] at this
  omega

lemma pentIdx_lt (a : Fin 5) : (pentIdx a).val < 5 := a.isLt

lemma inner_P_five_ring (a : Fin 5) : ⟪pentBipyramid 5, pentBipyramid (pentIdx a)⟫_ℝ = 0 := by
  obtain ⟨-, -, h, -⟩ := M3.cP_pent_pole (pentIdx a) (pentIdx_lt a)
  rw [M3.inner_P, if_neg (pentIdx_ne_five a).symm, h]
  simp [M3.val]

lemma inner_P_six_ring (a : Fin 5) : ⟪pentBipyramid 6, pentBipyramid (pentIdx a)⟫_ℝ = 0 := by
  obtain ⟨-, -, -, h⟩ := M3.cP_pent_pole (pentIdx a) (pentIdx_lt a)
  rw [M3.inner_P, if_neg (pentIdx_ne_six a).symm, h]
  simp [M3.val]

lemma pentIdx_injective : Function.Injective pentIdx := by
  intro a b h
  have := congrArg Fin.val h
  simp [pentIdx] at this
  exact Fin.ext this

lemma inner_P_ring (i j : Fin 5) (hij : i ≠ j) :
    ⟪pentBipyramid (pentIdx i), pentBipyramid (pentIdx j)⟫_ℝ =
      if pentc i j = true then M3.cosB else M3.cosA := by
  rw [M3.inner_P, if_neg (fun h => hij (pentIdx_injective h))]
  have hc : M3.cP (pentIdx i) (pentIdx j) = if pentc i j = true then 3 else 1 := by
    by_cases h : ((i : ℕ) + 5 - j) % 5 = 1 ∨ ((j : ℕ) + 5 - i) % 5 = 1 <;>
      simp [M3.cP, pentIdx, pentc, h]
  rw [hc]
  split_ifs <;> simp [M3.val]

/-! ### Ring rigidity -/

lemma ring_ge2 (a : Fin 5) : 2 ≤ (a.succ.succ : Fin 7).val := by simp

lemma ring_lt (a b : Fin 5) (h : a < b) : (a.succ.succ : Fin 7) < b.succ.succ :=
  Fin.succ_lt_succ_iff.2 (Fin.succ_lt_succ_iff.2 h)

lemma exists_ring (j : Fin 7) (hj : 2 ≤ j.val) : ∃ b : Fin 5, j = b.succ.succ :=
  ⟨⟨j.val - 2, by omega⟩, Fin.ext (by simp; omega)⟩

/-- **Ring pentagon.**  Five unit vectors (indices `2..6`) whose mutual inner products are within
`τ` of `cos (2π/5)` or `cos (4π/5)`, and which are all within `τ` of orthogonal to a further unit
vector (the pole `y 0`), form a relabelled regular pentagon in every Gram entry:
a complete graph on 5 vertices with no monochromatic triangle is a pentagon. -/
theorem ring_pentagon {τ : ℝ} (hτ : τ ≤ 1 / 10) (y : Fin 7 → R3) (hy : ∀ i, ‖y i‖ = 1)
    (h0r : ∀ r : Fin 7, 2 ≤ r.val → |⟪y 0, y r⟫_ℝ| ≤ τ)
    (hrr : ∀ r r' : Fin 7, 2 ≤ r.val → r < r' →
      |⟪y r, y r'⟫_ℝ - M3.cosB| ≤ τ ∨ |⟪y r, y r'⟫_ℝ - M3.cosA| ≤ τ) :
    ∃ s : Equiv.Perm (Fin 5), ∀ a b : Fin 5, a ≠ b →
      |⟪y a.succ.succ, y b.succ.succ⟫_ℝ -
        ⟪pentBipyramid (pentIdx (s a)), pentBipyramid (pentIdx (s b))⟫_ℝ| ≤ τ := by
  have hL : triFree (mk10 [col τ y 0 1, col τ y 0 2, col τ y 0 3, col τ y 0 4, col τ y 1 2,
      col τ y 1 3, col τ y 1 4, col τ y 2 3, col τ y 2 4, col τ y 3 4]) = true := by
    unfold triFree
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro a b c hab hbc ⟨h1, h2, h3⟩
      rw [mk10_col τ y a b hab] at h1
      rw [mk10_col τ y a c (hab.trans hbc)] at h2
      rw [mk10_col τ y b c hbc] at h3
      simp only [col, decide_eq_true_eq] at h1 h2 h3
      exact no_mono_cosB hτ (y 0) _ _ _ (hy _) (hy _) (hy _) (hy _) (h0r _ (ring_ge2 a))
        (h0r _ (ring_ge2 b)) (h0r _ (ring_ge2 c)) h1 h2 h3
    · rintro a b c hab hbc ⟨h1, h2, h3⟩
      rw [mk10_col τ y a b hab] at h1
      rw [mk10_col τ y a c (hab.trans hbc)] at h2
      rw [mk10_col τ y b c hbc] at h3
      simp only [col, decide_eq_false_iff_not] at h1 h2 h3
      have k1 := (hrr _ _ (ring_ge2 a) (ring_lt a b hab)).resolve_left h1
      have k2 := (hrr _ _ (ring_ge2 a) (ring_lt a c (hab.trans hbc))).resolve_left h2
      have k3 := (hrr _ _ (ring_ge2 b) (ring_lt b c hbc)).resolve_left h3
      exact no_mono_cosA hτ (y 0) _ _ _ (hy _) (hy _) (hy _) (hy _) (h0r _ (ring_ge2 a))
        (h0r _ (ring_ge2 b)) (h0r _ (ring_ge2 c)) k1 k2 k3
  have hP := comb5_dec _ _ _ _ _ _ _ _ _ _ hL
  unfold isPent at hP
  simp only [decide_eq_true_eq] at hP
  obtain ⟨s, hs⟩ := hP
  have hcol : ∀ a b : Fin 5, a < b → col τ y a b = pentc (s a) (s b) :=
    fun a b hab => (mk10_col τ y a b hab).symm.trans (hs a b hab)
  refine ⟨s, ?_⟩
  have key : ∀ a b : Fin 5, a < b →
      |⟪y a.succ.succ, y b.succ.succ⟫_ℝ -
        ⟪pentBipyramid (pentIdx (s a)), pentBipyramid (pentIdx (s b))⟫_ℝ| ≤ τ := by
    intro a b hab
    have hne : s a ≠ s b := fun h => (ne_of_lt hab) (s.injective h)
    rw [inner_P_ring _ _ hne]
    have hc := hcol a b hab
    by_cases hp : pentc (s a) (s b) = true
    · simp only [hp, ↓reduceIte]
      rw [hp] at hc
      simpa [col] using hc
    · simp only [hp]
      have hp' : pentc (s a) (s b) = false := by simpa using hp
      rw [hp'] at hc
      simp only [col, decide_eq_false_iff_not] at hc
      exact (hrr _ _ (ring_ge2 a) (ring_lt a b hab)).resolve_left hc
  intro a b hab
  rcases lt_or_gt_of_ne hab with h | h
  · exact key a b h
  · have := key b a h
    rwa [real_inner_comm (y a.succ.succ) (y b.succ.succ),
      real_inner_comm (pentBipyramid (pentIdx (s a))) (pentBipyramid (pentIdx (s b)))] at this

/-- **Tube rigidity.**  A unit configuration whose pole pair `(0,1)` is within `τ` of antipodal,
whose pole--ring inner products are within `τ` of `0` and whose ring--ring inner products are
within `τ` of `cos (2π/5)` or `cos (4π/5)` is, in every Gram entry, within `τ` of a relabelling
of the pentagonal bipyramid. (Any `τ ≤ 1/10`.) -/
theorem ring_rigid {τ : ℝ} (hτ : τ ≤ 1 / 10) (y : Fin 7 → R3) (hy : ∀ i, ‖y i‖ = 1)
    (h01 : |⟪y 0, y 1⟫_ℝ + 1| ≤ τ)
    (h0r : ∀ r : Fin 7, 2 ≤ r.val → |⟪y 0, y r⟫_ℝ| ≤ τ)
    (h1r : ∀ r : Fin 7, 2 ≤ r.val → |⟪y 1, y r⟫_ℝ| ≤ τ)
    (hrr : ∀ r r' : Fin 7, 2 ≤ r.val → r < r' →
      |⟪y r, y r'⟫_ℝ - M3.cosB| ≤ τ ∨ |⟪y r, y r'⟫_ℝ - M3.cosA| ≤ τ) :
    ∃ σ : Equiv.Perm (Fin 7), ∀ i j, i ≠ j →
      |⟪y i, y j⟫_ℝ - ⟪pentBipyramid (σ i), pentBipyramid (σ j)⟫_ℝ| ≤ τ := by
  obtain ⟨s, hs⟩ := ring_pentagon hτ y hy h0r hrr
  refine ⟨sigEquiv s, ?_⟩
  have key : ∀ i j : Fin 7, i < j →
      |⟪y i, y j⟫_ℝ - ⟪pentBipyramid (sigEquiv s i), pentBipyramid (sigEquiv s j)⟫_ℝ| ≤ τ := by
    intro i j hij
    have hij' : i.val < j.val := hij
    by_cases hi : i.val < 2
    · by_cases hj : j.val < 2
      · have hi0 : i = 0 := Fin.ext (by simp; omega)
        have hj1 : j = 1 := Fin.ext (by simp; omega)
        subst hi0
        subst hj1
        rw [sigEquiv_apply, sigEquiv_apply, sig7_zero, sig7_one, inner_P_pole_pole]
        simpa using h01
      · obtain ⟨b, rfl⟩ := exists_ring j (by omega)
        rw [sigEquiv_apply, sigEquiv_apply, sig7_ring]
        rcases (by omega : i.val = 0 ∨ i.val = 1) with h | h
        · have hi0 : i = 0 := Fin.ext (by simpa using h)
          subst hi0
          rw [sig7_zero, inner_P_five_ring]
          simpa using h0r _ (ring_ge2 b)
        · have hi1 : i = 1 := Fin.ext (by simpa using h)
          subst hi1
          rw [sig7_one, inner_P_six_ring]
          simpa using h1r _ (ring_ge2 b)
    · obtain ⟨a, rfl⟩ := exists_ring i (by omega)
      obtain ⟨b, rfl⟩ := exists_ring j (by omega)
      rw [sigEquiv_apply, sigEquiv_apply, sig7_ring, sig7_ring]
      exact hs a b (fun h => by subst h; exact lt_irrefl _ hij)
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h
  · have := key j i h
    rwa [real_inner_comm (y i) (y j),
      real_inner_comm (pentBipyramid (sigEquiv s i)) (pentBipyramid (sigEquiv s j))] at this

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

/-- `TubeRigid τ` holds for every `τ ≤ 1/10`: this is agent3's `T4.ring_rigid`. -/
theorem tubeRigid_of_le {τ : ℝ} (h : τ ≤ 1 / 10) : TubeRigid τ :=
  fun y hy h01 h0r h1r hrr => T4.ring_rigid h y hy h01 h0r h1r hrr

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
theorem solution {τ : ℝ} (h : τ ≤ 1 / 10) : Glue.TubeRigid τ :=
  ThomsonN7.Glue.tubeRigid_of_le h
