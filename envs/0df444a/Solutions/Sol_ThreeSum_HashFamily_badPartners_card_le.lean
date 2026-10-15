-- Prove2me | solution 1 for ThreeSum.HashFamily.badPartners_card_le
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:45:42.289103+00:00
-- url     : https://prove2.me/submissions/ee93b2b9-5f44-44bf-b821-03a68932a694

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

























































end IncidenceCounting

section GraphMoments

variable {E : Type*} [Fintype E] [DecidableEq E]
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]








theorem badPartners_card_le_sourceProof (left right : E → α → Bool) (e : E) (Delta G : ℕ)
    (hL : (Finset.univ.filter (fun f => left e = left f)).card ≤ Delta)
    (hR : (Finset.univ.filter (fun f => right e = right f)).card ≤ Delta)
    (hG : (Finset.univ.filter (fun f =>
      outputMask left right e = outputMask left right f)).card ≤ G) :
    (badPartners left right e).card ≤ 2 * Delta + G := by
  have he : badPartners left right e =
      ((Finset.univ.filter (fun f => left e = left f)) ∪
        (Finset.univ.filter (fun f => right e = right f))) ∪
          (Finset.univ.filter (fun f => outputMask left right e = outputMask left right f)) := by
    ext f
    simp [badPartners, or_assoc]
  rw [he]
  have hu := Finset.card_union_le
    ((Finset.univ.filter (fun f => left e = left f)) ∪
      (Finset.univ.filter (fun f => right e = right f)))
    (Finset.univ.filter (fun f => outputMask left right e = outputMask left right f))
  have hv := Finset.card_union_le (Finset.univ.filter (fun f => left e = left f))
    (Finset.univ.filter (fun f => right e = right f))
  omega


























































































































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

universe u_1 u_3

theorem solution : ∀ {α : Type u_1} {E : Type u_3} [inst : Fintype.{u_3} E] [DecidableEq.{u_3 + 1} E] [inst_2 : Fintype.{u_1} α]
  [DecidableEq.{u_1 + 1} α] (left right : E → α → Bool) (e : E) (Delta G : Nat),
  @LE.le.{0} Nat instLENat (@Finset.card.{u_3} E {f : E | @Eq.{u_1 + 1} (α → Bool) (left e) (left f)}) Delta →
    @LE.le.{0} Nat instLENat (@Finset.card.{u_3} E {f : E | @Eq.{u_1 + 1} (α → Bool) (right e) (right f)}) Delta →
      @LE.le.{0} Nat instLENat
          (@Finset.card.{u_3} E
            {f : E |
              @Eq.{u_1 + 1} (α → Bool) (@ThreeSum.HashFamily.outputMask.{u_1, u_3} α E left right e)
                (@ThreeSum.HashFamily.outputMask.{u_1, u_3} α E left right f)})
          G →
        @LE.le.{0} Nat instLENat
          (@Finset.card.{u_3} E (@ThreeSum.HashFamily.badPartners.{u_1, u_3} α E inst inst_2 left right e))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) Delta)
            G) := by
  exact @ThreeSum.HashFamily.badPartners_card_le_sourceProof

#print axioms solution
