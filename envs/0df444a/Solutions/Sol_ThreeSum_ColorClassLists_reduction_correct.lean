-- Prove2me | solution 1 for ThreeSum.ColorClassLists.reduction_correct
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:11:22.35637+00:00
-- url     : https://prove2.me/submissions/ea648f2b-8a39-449b-96d3-76a6770cdeba

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle06
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSum_Coloring_two_coordinates_separate


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.LightClassFilter
end ThreeSum.LightClassFilter

section


/-!
# Stable extraction of one color class from the original signed array

The program reads stored colors and original values. It writes a length
header followed by exactly the selected values, optionally negated. Repeated
values are preserved; deduplication belongs to the later normalization pass.
-/

namespace ThreeSum.LightClassFilter

open Light

set_option maxHeartbeats 1200000

















theorem mem_items (x : ℕ → ℤ) (color : ℕ → ℕ) (want : ℕ) (scale : ℤ) (n : ℕ) (z : ℤ) :
    z ∈ items x color want scale n ↔ ∃ i, i < n ∧ color i = want ∧ scale*x i = z := by
  simp [items,and_assoc]





















variable {lim : Limits} {P : Program} {d : ℕ}























































































end ThreeSum.LightClassFilter

end

section


/-!
# A finite, deterministic three-color reduction

The family below enumerates two positions of the binary representation of an
array index and all 81 maps from their four patterns to three colors.  Its
parameter count is exactly `81 * d^2`.  In particular it never enumerates all
three-colorings of the input.  The final equivalence allows repeated input
values and deduplicates each color class into a finite set.
-/

namespace ThreeSum.Coloring

variable {α : Type*}









































/-- Enumeration of the small parameter space separates the words in the
specified order, so no permutation of the three-set equation is needed. -/
theorem exists_separating_parameter {d : ℕ} {s t u : Fin d → Bool}
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) :
    ∃ p : Parameter d, applyColor p s = 0 ∧ applyColor p t = 1 ∧
      applyColor p u = 2 := by
  obtain ⟨i, j, hst', hsu', htu'⟩ := two_coordinates_separate hst hsu htu
  let f : (Bool × Bool) → Fin 3 := fun x =>
    if x = (s i, s j) then 0 else if x = (t i, t j) then 1 else 2
  refine ⟨((i, j), f), ?_, ?_, ?_⟩
  · simp [applyColor, f]
  · simp [applyColor, f, Ne.symm hst']
  · simp [applyColor, f, Ne.symm hsu', Ne.symm htu']









































































theorem mem_values {n : ℕ} (x : Fin n → ℤ) (c : Fin n → Fin 3)
    (color : Fin 3) (v : ℤ) :
    v ∈ values x c color ↔ ∃ i, c i = color ∧ x i = v := by
  simp [values]

theorem mem_negValues {n : ℕ} (x : Fin n → ℤ) (c : Fin n → Fin 3) (v : ℤ) :
    v ∈ negValues x c ↔ ∃ i, c i = 2 ∧ -x i = v := by
  simp [negValues, mem_values]

























































end ThreeSum.Coloring

end

section


/-!
# Exact original-position semantics of the constructed color-class lists

The machine keeps repeated values within a class and negates the third
class. The list membership witnesses are original positions. Any binary
width large enough for the indices suffices for the deterministic family.
-/

namespace ThreeSum.ColorClassLists

open LightClassFilter



@[simp] theorem value_fin {n : ℕ} (x : Fin n → ℤ) (i : Fin n) : value x i.val = x i := by
  simp [value,i.isLt]








theorem mem_classList {n W : ℕ} (p : Coloring.Parameter W) (x : Fin n → ℤ)
    (c : Fin 3) (z : ℤ) :
    z ∈ classList p x c.val 1 ↔ z ∈ Coloring.values x (indexColor p) c := by
  rw [classList,mem_items,Coloring.mem_values]
  simp only [one_mul]
  constructor
  · rintro ⟨i,hi,hc,hx⟩
    refine ⟨⟨i,hi⟩,Fin.ext hc,?_⟩
    simpa only [← value_fin x ⟨i,hi⟩] using hx
  · rintro ⟨i,hc,hx⟩
    exact ⟨i.val,i.isLt,congrArg Fin.val hc,by simpa using hx⟩

theorem mem_negClassList {n W : ℕ} (p : Coloring.Parameter W) (x : Fin n → ℤ) (z : ℤ) :
    z ∈ classList p x 2 (-1) ↔ z ∈ Coloring.negValues x (indexColor p) := by
  rw [classList,mem_items,Coloring.mem_negValues]
  simp only [neg_one_mul]
  constructor
  · rintro ⟨i,hi,hc,hx⟩
    refine ⟨⟨i,hi⟩,Fin.ext hc,?_⟩
    simpa only [← value_fin x ⟨i,hi⟩] using hx
  · rintro ⟨i,hc,hx⟩
    exact ⟨i.val,i.isLt,congrArg Fin.val hc,by simpa using hx⟩

























theorem witness_iff {n W : ℕ} (p : Coloring.Parameter W) (x : Fin n → ℤ) :
    witness p x ↔ Coloring.ThreeSetWitness
      (Coloring.values x (indexColor p) 0) (Coloring.values x (indexColor p) 1)
      (Coloring.negValues x (indexColor p)) := by
  unfold witness Coloring.ThreeSetWitness
  have h0 (z : ℤ) : z ∈ classList p x 0 1 ↔ z ∈ Coloring.values x (indexColor p) 0 :=
    mem_classList p x (0 : Fin 3) z
  have h1 (z : ℤ) : z ∈ classList p x 1 1 ↔ z ∈ Coloring.values x (indexColor p) 1 :=
    mem_classList p x (1 : Fin 3) z
  simp only [h0,h1,mem_negClassList]

theorem bits_injective {n W : ℕ} (hn : n ≤ 2^W) :
    Function.Injective (fun i : Fin n => fun j : Fin W => i.val.testBit j.val) := by
  intro i j he
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < W
  · exact congrFun he ⟨k,hk⟩
  · have hp : 2^W ≤ 2^k := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_eq_false_of_lt (i.isLt.trans_le (hn.trans hp)),
      Nat.testBit_eq_false_of_lt (j.isLt.trans_le (hn.trans hp))]

/-- Every original distinct-position zero sum appears in one of the actual
list triples, for any machine-computed sufficient width. -/
theorem reduction_correct_sourceProof {n W : ℕ} (x : Fin n → ℤ) (hn : n ≤ 2^W) :
    Coloring.DistinctZeroSum x ↔ ∃ p : Coloring.Parameter W, witness p x := by
  constructor
  · rintro ⟨i,j,k,hij,hik,hjk,hsum⟩
    obtain ⟨p,hi,hj,hk⟩ := Coloring.exists_separating_parameter
      (fun he => hij (bits_injective hn he)) (fun he => hik (bits_injective hn he))
      (fun he => hjk (bits_injective hn he))
    refine ⟨p,(witness_iff p x).mpr ?_⟩
    refine ⟨x i,(Coloring.mem_values x (indexColor p) 0 _).mpr ⟨i,hi,rfl⟩,
      x j,(Coloring.mem_values x (indexColor p) 1 _).mpr ⟨j,hj,rfl⟩,
      -x k,(Coloring.mem_negValues x (indexColor p) _).mpr ⟨k,hk,rfl⟩,?_⟩
    omega
  · rintro ⟨p,hp⟩
    obtain ⟨a,ha,b,hb,c,hc,he⟩ := (witness_iff p x).mp hp
    obtain ⟨i,hi,rfl⟩ := (Coloring.mem_values x (indexColor p) 0 a).mp ha
    obtain ⟨j,hj,rfl⟩ := (Coloring.mem_values x (indexColor p) 1 b).mp hb
    obtain ⟨k,hk,rfl⟩ := (Coloring.mem_negValues x (indexColor p) c).mp hc
    exact ⟨i,j,k,by intro heq; subst j; simp_all,
      by intro heq; subst k; simp_all,
      by intro heq; subst k; simp_all,by omega⟩

end ThreeSum.ColorClassLists

end


theorem solution : ∀ {n W : Nat} (x : Fin n → Int),
  @LE.le.{0} Nat instLENat n
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) W) →
    Iff (@ThreeSum.Coloring.DistinctZeroSum n x)
      (∃ (p : ThreeSum.Coloring.Parameter W), @ThreeSum.ColorClassLists.witness n W p x) := by
  exact @ThreeSum.ColorClassLists.reduction_correct_sourceProof

#print axioms solution
