-- Prove2me | solution 1 for Paley11987Verified.Sensitivity2075.tolerant_repair_cases
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-23T04:36:41.468098+00:00
-- url     : https://prove2.me/submissions/6d9421db-7379-47f9-91b7-f6a001b329b8

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Paley11987Support_036
import Definitions.Def_Paley11987Support_055

set_option autoImplicit false
set_option Elab.async false
section z29

set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
noncomputable section
open scoped Classical BigOperators
namespace OAI.Paper320













namespace Tournament
variable {k : ℕ} (T : Tournament k)









end Tournament



















end OAI.Paper320
namespace Sensitivity205
open OAI.Paper320







end Sensitivity205
namespace Sensitivity2075
open OAI.Paper320 Sensitivity205













@[simp] theorem mem_missingTargets {n k r : ℕ} {I : Type}
    (F : Fin n → (I → Bool) → Bool) (A : Fin n)
    (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) (c : Fin r) :
    c ∈ missingTargets F A x i ↔ F A (recursiveChild x i c) = false := by
  simp [missingTargets]

@[simp] theorem mem_failedGuards {n k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (G : Fin n) (x : ((Fin k × Fin r) × I) → Bool) (i j : Fin k) :
    j ∈ failedGuards T label F G x i ↔
      T.Adj i j ∧ F G (recursiveChild x j (label i j)) = true := by
  simp [failedGuards]

theorem missingTargets_empty {n k r : ℕ} {I : Type}
    (F : Fin n → (I → Bool) → Bool) (A : Fin n)
    (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) :
    missingTargets F A x i = ∅ ↔ ∀ c, F A (recursiveChild x i c) = true := by
  simp [missingTargets, Finset.filter_eq_empty_iff]







section Flips
variable {n k r : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
  (G : Fin n) (x : ((Fin k × Fin r) × I) → Bool)
  (i j : Fin k) (c : Fin r) (a : I)

theorem guard_mem_flip_iff {v : Fin k} (hne : (v, label i v) ≠ (j,c)) :
    v ∈ failedGuards T label F G (flip x {((j,c),a)}) i ↔
      v ∈ failedGuards T label F G x i := by
  simp only [mem_failedGuards, recursiveChild_flip_other x j v c (label i v) a hne]



theorem guards_subset_flip :
    failedGuards T label F G x i ⊆
      insert j (failedGuards T label F G (flip x {((j,c),a)}) i) := by
  intro v hv
  by_cases he : v = j
  · exact Finset.mem_insert.mpr (Or.inl he)
  · exact Finset.mem_insert.mpr (Or.inr
      ((guard_mem_flip_iff T label F G x i j c a (by
        intro hh; exact he (congrArg Prod.fst hh))).mpr hv))



theorem guards_card_le_flip :
    (failedGuards T label F G x i).card ≤
      (failedGuards T label F G (flip x {((j,c),a)}) i).card + 1 :=
  (Finset.card_le_card (guards_subset_flip T label F G x i j c a)).trans
    (Finset.card_insert_le _ _)

theorem guards_flip_own :
    failedGuards T label F G (flip x {((i,c),a)}) i =
      failedGuards T label F G x i := by
  ext v
  by_cases hv : T.Adj i v
  · exact guard_mem_flip_iff T label F G x i i c a (by
      intro hh; exact T.ne_of_adj hv (congrArg Prod.fst hh).symm)
  · simp only [mem_failedGuards, hv, false_and]

theorem guard_decrease_location
    (hdec : (failedGuards T label F G (flip x {((j,c),a)}) i).card <
      (failedGuards T label F G x i).card) :
    T.Adj i j ∧ c = label i j ∧ F G (recursiveChild x j c) = true ∧
      F G (flip (recursiveChild x j c) {a}) = false := by
  obtain ⟨v, hv, hv'⟩ := Finset.exists_mem_notMem_of_card_lt_card hdec
  have hloc : (v, label i v) = (j,c) := by
    by_contra hh
    exact hv' ((guard_mem_flip_iff T label F G x i j c a hh).mpr hv)
  have hvj : v = j := congrArg Prod.fst hloc
  subst v
  have hcl : c = label i j := (congrArg Prod.snd hloc).symm
  subst c
  obtain ⟨hij, hon⟩ := (mem_failedGuards T label F G x i j).mp hv
  refine ⟨hij, rfl, hon, ?_⟩
  have hoff : F G (recursiveChild (flip x {((j,label i j),a)}) j (label i j)) = false := by
    simpa only [mem_failedGuards, hij, true_and, Bool.not_eq_true] using hv'
  simpa only [recursiveChild_flip_same] using hoff



end Flips

section RowFlips
variable {n k r : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
  (A G : Fin n) (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool)
  (i j : Fin k) (c : Fin r) (a : I)

theorem _root_.solution
    (hoff : tolerantRow T label F A G q x i = false)
    (hon : tolerantRow T label F A G q (flip x {((j,c),a)}) i = true) :
    (i ∈ tolerantTargets T label F A G q x ∧ j = i ∧
      F A (recursiveChild x j c) = false ∧
      F A (flip (recursiveChild x j c) {a}) = true) ∨
    (i ∈ tolerantGuards T label F A G q x ∧ T.Adj i j ∧ c = label i j ∧
      F G (recursiveChild x j c) = true ∧
      F G (flip (recursiveChild x j c) {a}) = false) := by
  obtain ⟨ht, hg⟩ := (tolerantRow_true T label F A G q _ i).mp hon
  by_cases hji : j = i
  · subst j
    rw [guards_flip_own] at hg
    have hton : F A (flip (recursiveChild x i c) {a}) = true := by
      simpa only [recursiveChild_flip_same] using ht c
    have hother : ∀ d, d ≠ c → F A (recursiveChild x i d) = true := by
      intro d hdc
      simpa only [recursiveChild_flip_other x i i c d a (by
        intro he; exact hdc (congrArg Prod.snd he))] using ht d
    have htoff : F A (recursiveChild x i c) = false := by
      cases hc : F A (recursiveChild x i c)
      · rfl
      · have hrow := (tolerantRow_true T label F A G q x i).mpr ⟨?_, hg⟩
        · simp [hoff] at hrow
        · intro d
          by_cases hd : d = c
          · simpa only [hd] using hc
          · exact hother d hd
    have hmissing : missingTargets F A x i = {c} := by
      ext d
      simp only [mem_missingTargets, Finset.mem_singleton]
      constructor
      · intro hd
        by_contra hne
        have hh := hother d hne
        simp [hd] at hh
      · rintro rfl
        exact htoff
    exact Or.inl ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hmissing], hg⟩,
      rfl, htoff, hton⟩
  · have htargets : ∀ d, F A (recursiveChild x i d) = true := by
      intro d
      simpa only [recursiveChild_flip_other x j i c d a (by
        intro he; exact hji (congrArg Prod.fst he).symm)] using ht d
    have hcount : q < (failedGuards T label F G x i).card := by
      by_contra hn
      have hh := (tolerantRow_true T label F A G q x i).mpr
        ⟨htargets, by omega⟩
      simp [hoff] at hh
    have hupper := guards_card_le_flip T label F G x i j c a
    have hexact : (failedGuards T label F G x i).card = q+1 := by omega
    have hl := guard_decrease_location T label F G x i j c a (by omega)
    exact Or.inr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (missingTargets_empty F A x i).mpr htargets, hexact⟩, hl⟩



end RowFlips

section Nesting






end Nesting











section JointCandidates








end JointCandidates





end Sensitivity2075
end
end z29
