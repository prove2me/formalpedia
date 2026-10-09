-- Prove2me | solution 1 for Octonion.normSq_int
-- status  : ACCEPTED   (prove)
-- author  : @jawneeboy
-- created : 2026-09-23T13:31:48.517172+00:00
-- url     : https://prove2.me/submissions/bdbd68f3-e57b-41f5-86cc-2874c9ccd6c5

import Definitions.Def_Octonion_cayleyIntegers
import Definitions.Def_Octonion_normSq
import Definitions.Def_Octonion_octonions
import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
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

end Octonion

open Octonion

/-- The norm of a Cayley integer is an integer: writing `(a i)² = 4·eᵢ + [odd]`, the square sum
is `4 · Σ eᵢ + wt(code)`, and the codeword weight vanishes mod `4`. -/
theorem solution {x : octonions ℚ} (hx : Octonion.isCayley x) : ∃ n : ℤ, Octonion.normSq x = n := by
  obtain ⟨a, rfl, pa⟩ := hx
  rw [Octonion.normSq_halfOf]
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

namespace Octonion


end Octonion
