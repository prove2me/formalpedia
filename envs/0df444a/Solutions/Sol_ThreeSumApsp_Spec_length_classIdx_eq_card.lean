-- Prove2me | solution 1 for ThreeSumApsp.Spec.length_classIdx_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-06T08:30:06.206654+00:00
-- url     : https://prove2.me/submissions/0837d9a3-d1c3-4e5f-ab0c-fc503fcc6ccd

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Problems
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Chunks
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Hashing
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Probability.Independence.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.DeriveFintype

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false



/-!
# The table of the chunks (proof of Theorem 17)

"For ϱ ∈ ℤ_p let W_ϱ be the set of edges (a,b) ∈ A × B with w(a,b) ≡ ϱ (mod p), and cut it into
chunks of at most n²/√D query pairs."  The routine lists the pairs class after class (`sortedIdx`).
Then a class is a segment of the list, from `classStart ϱ` to `classStart (ϱ + 1)`, and a chunk is a
segment of a class.  The table `chunkTab` has one entry for each chunk: its residue, the place where
it starts, and its number of pairs.

* The list has every pair once (`sortedIdx_nodup`, `classStart_eq_sq`), and the places of a class
  hold pairs of that class (`getD_sortedIdx_class`).
* An entry of the table is a nonempty segment of at most `cap` places (`chunkTab_entry`) whose pairs
  have the residue of the entry (`chunkTab_class`).
* The chunks follow each other (`chunkTab_pairwise`), so every place lies in exactly one chunk
  (`chunkTab_cover`, `chunkTab_unique`).
* "There are at most p + √D ≤ 2√D chunks in all" (`length_chunkTab_le`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

variable {n p cap : ℕ} {RAB : List ℕ}

/-! ## The classes and the list of all the pairs -/















/-- The places of a class. -/
theorem mem_classIdx {rho x : ℕ} : x ∈ classIdx n RAB rho ↔ x < n * n ∧ RAB.getD x 0 = rho := by
  simp [classIdx]












/-! ## The starts of the classes -/
































































/-! ## The chunks -/
























































































































































end ThreeSumApsp.Spec

end



/-!
# Index arithmetic: a pair of numbers as one number

General facts about natural numbers. A matrix with rows of length `n` is kept as one list, row
after row: the entry in row `a` and column `b < n` has the index `a * n + b`. This file has

* the bounds on such an index (`Nat.mul_add_lt_mul`, `Nat.mul_add_le_mul`);
* the way back from the index to the pair (`Nat.mul_add_div_of_lt`, `Nat.mul_add_inj_of_lt`,
  `Nat.div_lt_of_lt_mul'`, `Nat.mod_lt_of_lt_mul`, `Nat.exists_eq_mul_add_of_lt_mul`,
  `Nat.eq_mul_succ_iff`);
* the pair of the next index (`Nat.succ_div_mod_of_lt`, `Nat.succ_div_mod_of_ne`,
  `Nat.succ_div_mod_of_eq`);
* residues seen as natural numbers (`Int.toNat_emod_lt`, `Int.natCast_toNat_emod`).
-/

public section

namespace Nat

/-! ## Bounds on an index -/











/-! ## From the index back to the pair

The column is `Nat.mul_add_mod_of_lt : c < b → (a * b + c) % b = c`. -/












/-- The row of an index below `m * n` is below `m`. -/
theorem div_lt_of_lt_mul' {t m n : ℕ} (h : t < m * n) : t / n < m :=
  Nat.div_lt_of_lt_mul (Nat.mul_comm m n ▸ h)

/-- The column of an index below `m * n` is below `n`. -/
theorem mod_lt_of_lt_mul {t m n : ℕ} (h : t < m * n) : t % n < n :=
  Nat.mod_lt t (Nat.pos_of_mul_pos_left (Nat.zero_lt_of_lt h))

/-- Every index below `m * n` is the index of a pair. -/
theorem exists_eq_mul_add_of_lt_mul {t m n : ℕ} (h : t < m * n) : ∃ a < m, ∃ b < n, t = a * n + b :=
  ⟨t / n, div_lt_of_lt_mul' h, t % n, mod_lt_of_lt_mul h, (Nat.div_add_mod' t n).symm⟩










/-! ## The next index -/























end Nat

namespace Int

/-! ## Residues as natural numbers -/






/-- The residue of an integer modulo `M ≥ 1` is a natural number. -/
theorem natCast_toNat_emod {M : ℕ} (hM : 0 < M) (x : ℤ) : ((x % (M : ℤ)).toNat : ℤ) = x % (M : ℤ) :=
  Int.toNat_of_nonneg (Int.emod_nonneg x (Int.natCast_ne_zero_iff_pos.2 hM))

end Int

end



/-!
# Hashing modulo a prime (proof of Theorem 17), on numbers and lists

The reduction of Theorem 17 hashes the weights modulo a prime `p` of the window `√D/2 ≤ p < √D` and
selects the prime with the fewest triples `(a,b,c)` with `S(a,b,c) ≡ 0 (mod p)`, where
`S(a,b,c) = w(a,b) + w(b,c) + w(a,c)`.  This file has the parts of this step that a program
computes:

* the residue of a weight as a natural number below `p` (`resid`, `residList`);
* the entries of the matrices `P` and `Q` of the proof of Theorem 17 as unit vectors (`cycVec_matP`,
  `cycVec_matQ`), and the count of the triples, read off the vectors of `PQ` (`countZeroMod_eq`);
* the primes of the window by comparisons of integers (`primesList`, `primesInRange_eq`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## Residues -/




/-- The residue, as an integer. -/
theorem resid_cast {p : ℕ} (hp : p ≠ 0) (w : ℤ) : (resid p w : ℤ) = w % (p : ℤ) :=
  Int.natCast_toNat_emod (Nat.pos_of_ne_zero hp) w





/-- The residue is the number below `p` that is congruent to `w`. -/
theorem resid_eq_iff {p : ℕ} (hp : p ≠ 0) (w : ℤ) {r : ℕ} (hr : r < p) :
    resid p w = r ↔ w ≡ (r : ℤ) [ZMOD (p : ℤ)] := by
  rw [Int.ModEq, Int.emod_eq_of_lt (Int.natCast_nonneg r) (Int.ofNat_lt.2 hr), ← resid_cast hp,
    Nat.cast_inj]













/-- The residues of a list, read with a default: beyond the end of the list both sides are 0. -/
theorem getD_residList (p : ℕ) (l : List ℤ) (i : ℕ) :
    (residList p l).getD i 0 = resid p (l.getD i 0) := by
  rw [residList, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> simp [resid]







/-! ## The count of the proof of Theorem 17 -/






















/-! ## The primes of the window -/



































end ThreeSumApsp.Spec

end



/-!
# The number of chunks, on lists and on sets of pairs (proof of Theorem 17)

The routines work with lists of places: `classIdx` lists the places `a n + b` of the pairs of a
class, and the table `chunkTab` has one entry for each chunk.  The paper's class `W_ϱ` is a set of
pairs (`residueClass`).  The map `(a, b) ↦ a n + b` is a bijection between the set and the list, so
both have the same number of elements (`length_classIdx_eq_card`), and the table has as many entries
as there are chunks "in all" (`length_chunkTab_eq_totalChunks`).  The instance is
`triOf n AB BC AC`, whose weights `w(a,b)` are read from the list `AB`, row by row.
-/

public section

namespace ThreeSumApsp.Spec

variable (n : ℕ) {p : ℕ} (AB BC AC : List ℤ)

/-- The list of the places of a class has one entry for each pair of the class `W_ϱ`. -/
theorem length_classIdx_eq_card_sourceProof (hp : p ≠ 0) (ϱ : Fin p) :
    (classIdx n (residList p AB) ϱ).length = ((triOf n AB BC AC).residueClass p ϱ).card := by
  have hnodup : (classIdx n (residList p AB) ϱ).Nodup := List.nodup_range.filter _
  have hmem : ∀ q : Fin n × Fin n,
      pairIndex q ∈ (classIdx n (residList p AB) ϱ).toFinset ↔
        q ∈ (triOf n AB BC AC).residueClass p ϱ := fun q => by
    rw [List.mem_toFinset, mem_classIdx, getD_residList, TriangleInstance.residueClass,
      Finset.mem_filter, ← resid_eq_iff hp _ ϱ.isLt, and_iff_right (Finset.mem_univ q)]
    exact and_iff_right (Nat.mul_add_lt_mul q.1.isLt q.2.isLt)
  rw [← List.toFinset_card_of_nodup hnodup]
  refine (Finset.card_bij (fun q _ => pairIndex q) (fun q hq => (hmem q).2 hq)
    (fun q _ q' _ h => ?_) fun x hx => ?_).symm
  · obtain ⟨hrow, hcol⟩ := Nat.mul_add_inj_of_lt q.2.isLt q'.2.isLt h
    exact Prod.ext (Fin.ext hrow) (Fin.ext hcol)
  · obtain ⟨a, ha, b, hb, rfl⟩ :=
    Nat.exists_eq_mul_add_of_lt_mul (mem_classIdx.1 (List.mem_toFinset.1 hx)).1
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), (hmem _).1 hx, rfl⟩










end ThreeSumApsp.Spec

end


theorem solution : ∀ (n : Nat) {p : Nat} (AB BC AC : List.{0} Int),
  @Ne.{1} Nat p (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    ∀ (ϱ : Fin p),
      @Eq.{1} Nat
        (@List.length.{0} Nat (ThreeSumApsp.Spec.classIdx n (ThreeSumApsp.Spec.residList p AB) (@Fin.val p ϱ)))
        (@Finset.card.{0} (Prod.{0, 0} (Fin n) (Fin n))
          (@ThreeSumApsp.TriangleInstance.residueClass n (ThreeSumApsp.Spec.triOf n AB BC AC) p ϱ)) := by
  exact @ThreeSumApsp.Spec.length_classIdx_eq_card_sourceProof

#print axioms solution
