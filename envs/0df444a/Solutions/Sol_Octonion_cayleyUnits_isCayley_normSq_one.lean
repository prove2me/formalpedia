-- Prove2me | solution 1 for Octonion.cayleyUnits_isCayley_normSq_one
-- status  : ACCEPTED   (prove)
-- author  : @jawneeboy
-- created : 2026-09-23T13:28:55.785278+00:00
-- url     : https://prove2.me/submissions/c8126231-4a5a-433b-ac0f-e21876397bea

import Definitions.Def_Octonion_cayleyIntegers
import Definitions.Def_Octonion_cayleyUnits
import Definitions.Def_Octonion_normSq
import Definitions.Def_Octonion_octonions
import Definitions.Def_Octonion_toRat8
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

open BigOperators

namespace Octonion

private theorem signedRep_isCayley {m : ℕ} (hm : m ∈ cayleyMasks) (t : ℕ) :
    isCayley (signedRep m t) := by
  refine ⟨_, rfl, Finset.mem_image.mpr ⟨m, hm, ?_⟩⟩
  funext i
  cases hm' : Nat.testBit m i.val <;> cases ht : Nat.testBit t i.val <;>
    simp [patOfMask, hm', ht]

private theorem signedRep_normSq {m : ℕ} (hm : m ∈ weight4Masks) (t : ℕ) :
    normSq (signedRep m t) = 1 := by
  rw [signedRep, normSq_halfOf]
  have hs (i : Fin 8) :
      (((if Nat.testBit m i.val then if Nat.testBit t i.val then 1 else -1 else 0 : ℤ) : ℚ))^2 =
        if Nat.testBit m i.val then 1 else 0 := by
    cases hm' : Nat.testBit m i.val <;> cases ht : Nat.testBit t i.val <;> norm_num
  simp_rw [hs]
  rw [Finset.sum_boole, (Finset.mem_filter.mp hm).2]
  norm_num

end Octonion

open Octonion

/-- Everything enumerated in `cayleyUnits` is a Cayley integer of norm one.
The signed half-vectors are handled uniformly by their parity and weight;
only the sixteen signed basis vectors require a small kernel computation. -/
theorem solution : ∀ u ∈ Octonion.cayleyUnits, Octonion.isCayley u ∧ Octonion.normSq u = 1 := by
  have hb : ∀ k : Fin 8, ∀ u ∈ ({Octonion.basisVec k, -Octonion.basisVec k} : Finset (octonions ℚ)),
      Octonion.decMem u = true ∧ Octonion.normSq u = 1 := by
    decide +kernel
  intro u hu
  rcases Finset.mem_union.mp hu with hu | hu
  · obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp hu
    exact ⟨Octonion.isCayley_of_decMem (hb k u hk).1, (hb k u hk).2⟩
  · obtain ⟨m, hm, hu⟩ := Finset.mem_biUnion.mp hu
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hu
    exact ⟨signedRep_isCayley (Finset.mem_filter.mp hm).1 t, signedRep_normSq hm t⟩

namespace Octonion


end Octonion
