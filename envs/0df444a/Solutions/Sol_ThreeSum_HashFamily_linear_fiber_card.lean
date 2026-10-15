-- Prove2me | solution 1 for ThreeSum.HashFamily.linear_fiber_card
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:46:09.778159+00:00
-- url     : https://prove2.me/submissions/9f6e6c58-380d-4b7a-a273-c4f0e4c3373a

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































/-- Equal-sized fibers of a surjective linear map, with the full sample
space cardinality on the right. This exact integer equality is the finite
uniform-distribution statement used in the hash moments. -/
theorem linear_fiber_card_sourceProof {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Fintype V] [Fintype W] [DecidableEq W]
    (f : V →ₗ[K] W) (hf : Function.Surjective f) (target : W) :
    Fintype.card W * (Finset.univ.filter (fun x => f x = target)).card =
      Fintype.card V := by
  classical
  have heq : ∀ y : W, (Finset.univ.filter (fun x => f x = y)).card =
      (Finset.univ.filter (fun x => f x = target)).card := by
    intro y
    exact AddMonoidHom.card_fiber_eq_of_mem_range f (hf y) (hf target)
  calc
    Fintype.card W * (Finset.univ.filter (fun x => f x = target)).card =
        ∑ y : W, (Finset.univ.filter (fun x => f x = y)).card := by
      simp [heq]
    _ = ∑ y : W, ∑ x : V, if f x = y then (1 : ℕ) else 0 := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ x : V, ∑ y : W, if f x = y then (1 : ℕ) else 0 := Finset.sum_comm
    _ = Fintype.card V := by simp











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

universe u_2 u_5 u_6

theorem solution : ∀ {K : Type u_2} [inst : Field.{u_2} K] {V : Type u_5} {W : Type u_6} [inst_1 : AddCommGroup.{u_5} V]
  [inst_2 :
    @_root_.Module.{u_2, u_5} K V
      (@DivisionSemiring.toSemiring.{u_2} K (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst)))
      (@AddCommGroup.toAddCommMonoid.{u_5} V inst_1)]
  [inst_3 : AddCommGroup.{u_6} W]
  [inst_4 :
    @_root_.Module.{u_2, u_6} K W
      (@DivisionSemiring.toSemiring.{u_2} K (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst)))
      (@AddCommGroup.toAddCommMonoid.{u_6} W inst_3)]
  [inst_5 : Fintype.{u_5} V] [inst_6 : Fintype.{u_6} W] [inst_7 : DecidableEq.{u_6 + 1} W]
  (f :
    @LinearMap.{u_2, u_2, u_5, u_6} K K
      (@DivisionSemiring.toSemiring.{u_2} K (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst)))
      (@DivisionSemiring.toSemiring.{u_2} K (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst)))
      (@RingHom.id.{u_2} K
        (@Semiring.toNonAssocSemiring.{u_2} K
          (@DivisionSemiring.toSemiring.{u_2} K
            (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst)))))
      V W (@AddCommGroup.toAddCommMonoid.{u_5} V inst_1) (@AddCommGroup.toAddCommMonoid.{u_6} W inst_3) inst_2 inst_4),
  @Function.Surjective.{u_5 + 1, u_6 + 1} V W
      (@DFunLike.coe.{max (u_5 + 1) (u_6 + 1), u_5 + 1, u_6 + 1}
        (@LinearMap.{u_2, u_2, u_5, u_6} K K
          (@DivisionSemiring.toSemiring.{u_2} K
            (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst)))
          (@DivisionSemiring.toSemiring.{u_2} K
            (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst)))
          (@RingHom.id.{u_2} K
            (@Semiring.toNonAssocSemiring.{u_2} K
              (@DivisionSemiring.toSemiring.{u_2} K
                (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst)))))
          V W (@AddCommGroup.toAddCommMonoid.{u_5} V inst_1) (@AddCommGroup.toAddCommMonoid.{u_6} W inst_3) inst_2
          inst_4)
        V (fun (x : V) => W)
        (@LinearMap.instFunLike.{u_2, u_2, u_5, u_6} K K V W
          (@DivisionSemiring.toSemiring.{u_2} K
            (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst)))
          (@DivisionSemiring.toSemiring.{u_2} K
            (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst)))
          (@AddCommGroup.toAddCommMonoid.{u_5} V inst_1) (@AddCommGroup.toAddCommMonoid.{u_6} W inst_3) inst_2 inst_4
          (@RingHom.id.{u_2} K
            (@Semiring.toNonAssocSemiring.{u_2} K
              (@DivisionSemiring.toSemiring.{u_2} K
                (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst))))))
        f) →
    ∀ (target : W),
      @Eq.{1} Nat
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Fintype.card.{u_6} W inst_6)
          (@Finset.card.{u_5} V
            {x : V |
              @Eq.{u_6 + 1} W
                (@DFunLike.coe.{max (u_5 + 1) (u_6 + 1), u_5 + 1, u_6 + 1}
                  (@LinearMap.{u_2, u_2, u_5, u_6} K K
                    (@DivisionSemiring.toSemiring.{u_2} K
                      (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst)))
                    (@DivisionSemiring.toSemiring.{u_2} K
                      (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst)))
                    (@RingHom.id.{u_2} K
                      (@Semiring.toNonAssocSemiring.{u_2} K
                        (@DivisionSemiring.toSemiring.{u_2} K
                          (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst)))))
                    V W (@AddCommGroup.toAddCommMonoid.{u_5} V inst_1) (@AddCommGroup.toAddCommMonoid.{u_6} W inst_3)
                    inst_2 inst_4)
                  V (fun (x : V) => W)
                  (@LinearMap.instFunLike.{u_2, u_2, u_5, u_6} K K V W
                    (@DivisionSemiring.toSemiring.{u_2} K
                      (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst)))
                    (@DivisionSemiring.toSemiring.{u_2} K
                      (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst)))
                    (@AddCommGroup.toAddCommMonoid.{u_5} V inst_1) (@AddCommGroup.toAddCommMonoid.{u_6} W inst_3) inst_2
                    inst_4
                    (@RingHom.id.{u_2} K
                      (@Semiring.toNonAssocSemiring.{u_2} K
                        (@DivisionSemiring.toSemiring.{u_2} K
                          (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst))))))
                  f x)
                target}))
        (@Fintype.card.{u_5} V inst_5) := by
  exact @ThreeSum.HashFamily.linear_fiber_card_sourceProof

#print axioms solution
