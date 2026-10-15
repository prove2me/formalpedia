-- Prove2me | solution 1 for ThreeSum.LocalHashMoments.hitCount_cap
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:54:50.225634+00:00
-- url     : https://prove2.me/submissions/22a85614-caa8-4b48-af96-e0b494a01abe

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Pi
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.LayerCounts
end ThreeSum.LayerCounts
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph

section


/-!
# The concrete local subset graph and its binary words

A left vertex has ones exactly on its `h`-subset.  A right vertex has zeros
exactly on its `h`-subset.  The endpoint maps, their separation, and the
equality mask are proved directly from finite-set membership.
-/

namespace ThreeSum.LocalGraph

variable {α : Type*} [DecidableEq α]





theorem leftWord_injective : Function.Injective (@leftWord α _) := by
  intro s t he
  ext i
  simpa only [leftWord, decide_eq_decide] using congrFun he i

theorem rightWord_injective : Function.Injective (@rightWord α _) := by
  intro s t he
  ext i
  have hi := congrFun he i
  simpa only [rightWord, decide_eq_decide, not_iff_not] using hi









































section ConcreteGraph

open LayerCounts




variable {L h : ℕ}


















theorem endpoint_injective :
    Function.Injective (fun e : Edge L h => (left e, right e)) := by
  intro e f he
  apply Subtype.ext
  exact Prod.ext (leftWord_injective (congrArg Prod.fst he))
    (rightWord_injective (congrArg Prod.snd he))

























theorem left_mem_vertices (e : Edge L h) : left e ∈ leftVertices L h :=
  Finset.mem_image.mpr ⟨e.val.1, mem_vertices.mpr (edge_data e).1, rfl⟩

theorem right_mem_vertices (e : Edge L h) : right e ∈ rightVertices L h :=
  Finset.mem_image.mpr ⟨e.val.2, mem_vertices.mpr (edge_data e).2.1, rfl⟩
































































end ConcreteGraph

end ThreeSum.LocalGraph

end

section


/-!
# Actual local one-hot covers

This module instantiates the hash moment and separable trimming proofs with
the disjoint-subset graph. The sample space consists of all assignments to
the two actual symbols at every coordinate. The resulting deterministic
greedy schedule covers every ordered field target, including equal targets.
-/

namespace ThreeSum.LocalHashMoments

open Finset
open scoped BigOperators

open LocalGraph LocalCoverBounds

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {L h : ℕ}









































































































































/-- Each retained target has at most `B^2` graph representations. This is an
actual endpoint injection into two light buckets, not a moment bound. -/
theorem hitCount_cap_sourceProof (B : ℕ) (w : Weight L K) (target : K × K) :
    hitCount L h B w target ≤ B ^ 2 := by
  classical
  let F : Finset (Edge L h) := univ.filter (fun e => w ∈
    HashFamily.trimmedPairEvent (left e) (right e) target.1 target.2
      (leftVertices L h) (rightVertices L h) B)
  change F.card ≤ B ^ 2
  by_cases hz : F.card = 0
  · simp only [hz, Nat.zero_le]
  have hn : F.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero hz)
  obtain ⟨e, he⟩ := hn
  have hlight : HashFamily.bucketSize (leftVertices L h) w target.1 ≤ B ∧
      HashFamily.bucketSize (rightVertices L h) w target.2 ≤ B :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp he).2).2
  let VL := (leftVertices L h).filter (fun s => HashFamily.hashValue w s = target.1)
  let VR := (rightVertices L h).filter (fun s => HashFamily.hashValue w s = target.2)
  have hcount : F.card ≤ (VL ×ˢ VR).card := by
    apply Finset.card_le_card_of_injOn (fun e : Edge L h => (left e, right e))
    · intro f hf
      have hh := (Finset.mem_filter.mp (Finset.mem_filter.mp hf).2).1
      have hv : HashFamily.hashValue w (left f) = target.1 ∧
          HashFamily.hashValue w (right f) = target.2 := (Finset.mem_filter.mp hh).2
      exact Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨left_mem_vertices f, hv.1⟩,
         Finset.mem_filter.mpr ⟨right_mem_vertices f, hv.2⟩⟩
    · intro e he f hf hef
      exact endpoint_injective hef
  calc
    F.card ≤ VL.card * VR.card := by simpa only [Finset.card_product] using hcount
    _ ≤ B * B := Nat.mul_le_mul hlight.1 hlight.2
    _ = B ^ 2 := by rw [pow_two]




































































/-! ## The selected local prime and its actual finite schedule -/




































































end ThreeSum.LocalHashMoments

end

universe u_1

theorem solution : ∀ {K : Type u_1} [inst : Field.{u_1} K] [inst_1 : Fintype.{u_1} K] [inst_2 : DecidableEq.{u_1 + 1} K] {L h : Nat}
  (B : Nat) (w : ThreeSum.LocalHashMoments.Weight.{u_1} L K) (target : Prod.{u_1, u_1} K K),
  @LE.le.{0} Nat instLENat (@ThreeSum.LocalHashMoments.hitCount.{u_1} K inst inst_1 inst_2 L h B w target)
    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) B
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) := by
  exact @ThreeSum.LocalHashMoments.hitCount_cap_sourceProof

#print axioms solution
