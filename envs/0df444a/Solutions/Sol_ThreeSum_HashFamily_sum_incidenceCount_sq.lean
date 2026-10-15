-- Prove2me | solution 1 for ThreeSum.HashFamily.sum_incidenceCount_sq
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:46:14.811951+00:00
-- url     : https://prove2.me/submissions/7da57fde-4716-4275-9a0a-0eac7a2b4ef3

import Definitions.Def_ThreeSum1962Source_Bundle01
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

section


/-!
# The actual one-hot hash family

This file develops the dependence classification of the binary one-hot hash
vectors used in the local cover. Hash weights are independent field elements
at coordinate/symbol pairs. The independence statements concern this concrete
family, not an assumed random oracle.
-/

namespace ThreeSum.HashFamily

open scoped BigOperators

variable {α K : Type*}











section Relations

variable [Ring K]



























































end Relations

section LinearIndependence

variable [Field K]

































end LinearIndependence

section UniformFibers

variable {σ ι : Type*} [Fintype σ] [Fintype ι] [Field K]































































end UniformFibers

section ActualHashes

variable {ι : Type*} [Fintype α] [Field K]
















end ActualHashes

section WordEvents

variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]












































































































































end WordEvents

section IncidenceCounting

variable {Ω E : Type*} [Fintype Ω] [Fintype E] [DecidableEq Ω]





theorem incidenceCount_eq_sum (events : E → Finset Ω) (w : Ω) :
    incidenceCount events w = ∑ e, if w ∈ events e then (1 : ℕ) else 0 := by
  unfold incidenceCount
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

















/-- Exact second-moment expansion over edge pairs, with no independence
assumption and no probabilistic approximation. -/
theorem sum_incidenceCount_sq_sourceProof (events : E → Finset Ω) :
    (∑ w, incidenceCount events w ^ 2) =
      ∑ e, ∑ f, (events e ∩ events f).card := by
  calc
    (∑ w, incidenceCount events w ^ 2) =
        ∑ w, ∑ e, ∑ f,
          if w ∈ events e ∧ w ∈ events f then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [incidenceCount_eq_sum, pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e he
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f hf
      by_cases he : w ∈ events e <;> by_cases hf : w ∈ events f <;> simp [he, hf]
    _ = ∑ e, ∑ f, ∑ w,
          if w ∈ events e ∧ w ∈ events f then (1 : ℕ) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e he
      exact Finset.sum_comm
    _ = ∑ e, ∑ f, (events e ∩ events f).card := by
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro f hf
      simp [← Finset.mem_inter]

end IncidenceCounting

section GraphMoments

variable {E : Type*} [Fintype E] [DecidableEq E]
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]






















































































































































end GraphMoments

section SeparableTrimming

variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]





















































































































































end SeparableTrimming

section TrimmedGraphMoments

variable {E : Type*} [Fintype E] [DecidableEq E]
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]
































end TrimmedGraphMoments

end ThreeSum.HashFamily

end

universe u_3 u_4

theorem solution : ∀ {Ω : Type u_3} {E : Type u_4} [inst : Fintype.{u_3} Ω] [inst_1 : Fintype.{u_4} E] [inst_2 : DecidableEq.{u_3 + 1} Ω]
  (events : E → Finset.{u_3} Ω),
  @Eq.{1} Nat
    (∑ w : Ω,
      @HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@ThreeSum.HashFamily.incidenceCount.{u_3, u_4} Ω E inst_1 inst_2 events w)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (∑ e : E,
      ∑ f : E,
        @Finset.card.{u_3} Ω
          (@Inter.inter.{u_3} (Finset.{u_3} Ω) (@Finset.instInter.{u_3} Ω inst_2) (events e) (events f))) := by
  exact @ThreeSum.HashFamily.sum_incidenceCount_sq_sourceProof

#print axioms solution
