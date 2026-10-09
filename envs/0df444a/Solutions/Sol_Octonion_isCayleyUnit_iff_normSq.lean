-- Prove2me | solution 1 for Octonion.isCayleyUnit_iff_normSq
-- status  : ACCEPTED   (prove)
-- author  : @jawneeboy
-- created : 2026-09-23T13:29:46.545015+00:00
-- url     : https://prove2.me/submissions/a4feb9fe-7fde-46f6-b03b-ba3469a9c905

import Definitions.Def_Octonion_IsCayleyUnit
import Definitions.Def_Octonion_cayleyIntegers
import Definitions.Def_Octonion_normSq
import Definitions.Def_Octonion_octonions
import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open Quaternion BigOperators

namespace Octonion

/-- The norm of a half-vector is a quarter of the integer square sum: `N (a/2) = (Σ aᵢ²)/4`.
Proved over opaque quaternion halves (`set` + `rfl` coordinate facts): rewriting `normSq` at an
unfolded quaternion literal leaves terms not type-correct at reducible transparency. -/
theorem normSq_halfOf (a : Fin 8 → ℤ) :
    normSq (halfOf a) = (∑ i : Fin 8, ((a i : ℚ))^2) / 4 := by
  set p : ℍ[ℚ] := (halfOf a).fst
  set q : ℍ[ℚ] := (halfOf a).snd
  have hsum : normSq (halfOf a) = Quaternion.normSq p + Quaternion.normSq q := rfl
  rw [hsum, Quaternion.normSq_def', Quaternion.normSq_def']
  have e0 : p.1 = (a 0 : ℚ) / 2 := rfl
  have e1 : p.2 = (a 1 : ℚ) / 2 := rfl
  have e2 : p.3 = (a 2 : ℚ) / 2 := rfl
  have e3 : p.4 = (a 3 : ℚ) / 2 := rfl
  have e4 : q.1 = (a 4 : ℚ) / 2 := rfl
  have e5 : q.2 = (a 5 : ℚ) / 2 := rfl
  have e6 : q.3 = (a 6 : ℚ) / 2 := rfl
  have e7 : q.4 = (a 7 : ℚ) / 2 := rfl
  rw [e0, e1, e2, e3, e4, e5, e6, e7]
  rw [Fin.sum_univ_eight]
  field_simp
  ring

end Octonion

open BigOperators Quaternion

namespace Octonion

/-- Every extended Hamming codeword has weight `0 mod 4`: the sum of its indicator values is
divisible by `4`. Closed by `decide +kernel` over the sixteen codewords. -/
private theorem code_sum_mod4 : ∀ u ∈ cayleyCode,
    (∑ i : Fin 8, if u i then (1 : ℤ) else 0) % 4 = 0 := by
  decide +kernel

/-- The norm of a Cayley integer is an integer: writing `(a i)² = 4·eᵢ + [odd]`, the square sum
is `4 · Σ eᵢ + wt(code)`, and the codeword weight vanishes mod `4`. -/
theorem normSq_int {x : octonions ℚ} (hx : isCayley x) : ∃ n : ℤ, normSq x = n := by
  obtain ⟨a, rfl, pa⟩ := hx
  rw [normSq_halfOf]
  have hcode : 4 ∣ ∑ i : Fin 8, if decide (Odd (a i)) then (1 : ℤ) else 0 := by
    have h := code_sum_mod4 (fun i => decide (Odd (a i))) pa
    exact Int.dvd_of_emod_eq_zero h
  have hsq : ∀ i : Fin 8, ∃ t : ℤ, (a i)^2 = 4 * t + if decide (Odd (a i)) then 1 else 0 := by
    intro i
    rcases Int.even_or_odd (a i) with ⟨t, ht⟩ | ⟨t, ht⟩
    · refine ⟨t^2, ?_⟩
      have hnot : ¬ Odd (a i) := fun ho => by
        have hodd := Int.odd_iff.mp ho
        rw [ht] at hodd
        omega
      rw [if_neg (by simpa using hnot), ht]
      ring
    · refine ⟨t^2 + t, ?_⟩
      rw [if_pos (decide_eq_true (show Odd (a i) from ⟨t, ht⟩)), ht]
      ring
  choose e he using hsq
  obtain ⟨k, hk⟩ := hcode
  have hsumz : ∑ i : Fin 8, (a i)^2 = 4 * (∑ i : Fin 8, e i + k) := by
    rw [Finset.sum_congr rfl fun i _ => he i, Finset.sum_add_distrib, ← Finset.mul_sum, hk]
    ring
  refine ⟨∑ i : Fin 8, e i + k, ?_⟩
  have hq : (∑ i : Fin 8, ((a i : ℚ))^2) = ((4 * (∑ i : Fin 8, e i + k) : ℤ) : ℚ) := by
    exact_mod_cast hsumz
  rw [hq]
  push_cast
  ring

end Octonion

open Quaternion

namespace Octonion
variable {R : Type*} [CommRing R]

/-- The norm is multiplicative (the Hurwitz property): `N (x * y) = N x * N y`.
Proved over any commutative base ring by expanding both sides into eight coordinates
and closing with `ring`. This statement does not assert a division structure. -/
theorem normSq_mul (x y : octonions R) : normSq (x * y) = normSq x * normSq y := by
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  show Quaternion.normSq (((⟨a, b⟩ : octonions R) * ⟨c, d⟩).fst) +
      Quaternion.normSq (((⟨a, b⟩ : octonions R) * ⟨c, d⟩).snd) =
    (Quaternion.normSq a + Quaternion.normSq b) * (Quaternion.normSq c + Quaternion.normSq d)
  simp only [fst_mul, snd_mul, normSq_def', re_add, imI_add, imJ_add, imK_add, re_sub, imI_sub,
    imJ_sub, imK_sub, re_mul, imI_mul, imJ_mul, imK_mul,
    re_star, imI_star, imJ_star, imK_star]
  ring

end Octonion

namespace Octonion

/-- The norm of one is one. -/
@[simp]
theorem normSq_one : normSq (1 : octonions ℚ) = 1 := by simp [normSq]

end Octonion

open Quaternion

namespace Octonion

/-- `x · x̄ = N x`: the product with the conjugate is the real octonion of the norm. Expanded
coordinate by coordinate over `ℚ` (the `ext_coord8`/`fin_cases` pattern of `inGraves_mul`). -/
theorem mul_conj (x : octonions ℚ) : x * conj x = ⟨⟨normSq x, 0, 0, 0⟩, 0⟩ := by
  obtain ⟨a, b⟩ := x
  refine ext_coord8 fun i => ?_
  fin_cases i
  all_goals
    simp only [coord8, fst_mul, snd_mul, conj, re_add, imI_add, imJ_add, imK_add, re_sub, imI_sub,
      imJ_sub, imK_sub, re_mul, imI_mul, imJ_mul, imK_mul, re_star, imI_star, imJ_star, imK_star,
      re_neg, imI_neg, imJ_neg, imK_neg, normSq, Quaternion.normSq_def']
    simp
    try ring

end Octonion

open Quaternion

namespace Octonion

/-- `x̄ · x = N x`: the conjugate-side companion of `mul_conj`, needed because the octonion
product is not commutative (nor associative). Same coordinate expansion. -/
theorem conj_mul (x : octonions ℚ) : conj x * x = ⟨⟨normSq x, 0, 0, 0⟩, 0⟩ := by
  obtain ⟨a, b⟩ := x
  refine ext_coord8 fun i => ?_
  fin_cases i
  all_goals
    simp only [coord8, fst_mul, snd_mul, conj, re_add, imI_add, imJ_add, imK_add, re_sub, imI_sub,
      imJ_sub, imK_sub, re_mul, imI_mul, imJ_mul, imK_mul, re_star, imI_star, imJ_star, imK_star,
      re_neg, imI_neg, imJ_neg, imK_neg, normSq, Quaternion.normSq_def']
    simp
    try ring

end Octonion

namespace Octonion

/-- Membership in the Cayley integers is exactly the lattice condition `isCayley`: all eight
coordinates lie in `½ℤ` and the parity pattern of the doubled coordinates is a Hamming codeword.
As a `simp` lemma this insulates users from the subring's set representation. -/
@[simp]
theorem mem_cayleyIntegers (x : octonions ℚ) :
    x ∈ cayleyIntegers ↔ isCayley x :=
  Iff.rfl

end Octonion

open Quaternion

namespace Octonion

/-- The Cayley integers are closed under octonion conjugation: `star` negates the imaginary
coordinates, and negation preserves parity, so the doubled coordinate vector keeps its Hamming
pattern. -/
theorem star_mem_cayleyIntegers {x : octonions ℚ} (hx : x ∈ cayleyIntegers) :
    star x ∈ cayleyIntegers := by
  rw [mem_cayleyIntegers] at hx ⊢
  obtain ⟨a, rfl, pa⟩ := hx
  refine ⟨fun i => if i = 0 then a i else -a i, ?_, ?_⟩
  · apply ext_coord8
    intro i
    have hst : star (halfOf a) = conj (halfOf a) := rfl
    rw [hst, coord8_conj]
    by_cases h : i = 0
    · simp [h, coord8_halfOf]
    · simp only [if_neg h, coord8_halfOf]
      push_cast
      ring
  · obtain ⟨m, hm, ham⟩ := Finset.mem_image.mp pa
    refine Finset.mem_image.mpr ⟨m, hm, ?_⟩
    have key : (fun i => decide (Odd (if i = 0 then a i else -a i))) =
        fun i => decide (Odd (a i)) := by
      funext i
      by_cases hi : i = 0 <;> by_cases h : Odd (a i) <;> simp [hi, h]
    rw [key, ← ham]

end Octonion

open Quaternion

namespace Octonion

/-- The real unit octonion written as a coordinate literal. -/
private theorem one_coord8_zero : (⟨⟨(1 : ℚ), 0, 0, 0⟩, 0⟩ : octonions ℚ) = 1 := by
  apply ext_coord8
  intro i
  fin_cases i <;> simp [coord8, fst_one, snd_one]

end Octonion

open Octonion

/-- The unit criterion: a Cayley integer is invertible inside the order iff its norm is one.
Forward: multiplicativity makes the norms of `x` and its inverse integral factors of `1`, and
nonnegativity (a sum of squares) leaves only `1`. Backward: `mul_conj`/`conj_mul` exhibit
`conj x`, a Cayley integer, as the two-sided inverse at norm one. -/
theorem solution {x : octonions ℚ} (hx : Octonion.isCayley x) :
    Octonion.IsCayleyUnit x ↔ Octonion.normSq x = 1 := by
  constructor
  · rintro ⟨_, y, hy, hxy, _⟩
    obtain ⟨p, hp⟩ := Octonion.normSq_int hx
    obtain ⟨q, hq⟩ := Octonion.normSq_int hy
    have hprod : (p : ℚ) * q = 1 := by rw [← hp, ← hq, ← Octonion.normSq_mul, hxy, Octonion.normSq_one]
    have hx0 : (0 : ℚ) ≤ Octonion.normSq x := by
      obtain ⟨a, rfl, _⟩ := hx
      rw [Octonion.normSq_halfOf]
      refine div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) (by norm_num)
    have hy0 : (0 : ℚ) ≤ Octonion.normSq y := by
      obtain ⟨a, rfl, _⟩ := hy
      rw [Octonion.normSq_halfOf]
      refine div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) (by norm_num)
    -- integral nonnegative factors of `1` in `ℚ`: `(p-1)(q-1) ≥ 0` expands to `p + q ≤ 2`
    have hp1 : (1 : ℚ) ≤ p := by
      have hz : (0 : ℤ) ≤ p := by exact_mod_cast hx0.trans_eq hp
      have hne : p ≠ 0 := by
        intro hc
        subst hc
        simp at hprod
      have hge : (1 : ℤ) ≤ p := by omega
      exact_mod_cast hge
    have hq1 : (1 : ℚ) ≤ q := by
      have hz : (0 : ℤ) ≤ q := by exact_mod_cast hy0.trans_eq hq
      have hge : (1 : ℤ) ≤ q := by
        by_contra hc
        have hle : q ≤ 0 := by omega
        have : (p : ℚ) * q ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by exact_mod_cast hle)
        linarith
      exact_mod_cast hge
    have hkey : ((p : ℚ) - 1) * (q - 1) = (p : ℚ) * q - p - q + 1 := by ring
    have hge0 : (0 : ℚ) ≤ ((p : ℚ) - 1) * (q - 1) :=
      mul_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr hq1)
    rw [hkey, hprod] at hge0
    have hpeq : (p : ℚ) = 1 := by linarith
    rw [hp]
    exact hpeq
  · intro h1
    refine ⟨hx, Octonion.conj x, Octonion.star_mem_cayleyIntegers hx, ?_, ?_⟩
    · have e := Octonion.mul_conj x
      rw [h1] at e
      exact e.trans one_coord8_zero
    · have e := Octonion.conj_mul x
      rw [h1] at e
      exact e.trans one_coord8_zero

namespace Octonion


end Octonion
