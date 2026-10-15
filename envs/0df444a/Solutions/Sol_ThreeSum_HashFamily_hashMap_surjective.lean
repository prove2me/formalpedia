-- Prove2me | solution 1 for ThreeSum.HashFamily.hashMap_surjective
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:46:05.020873+00:00
-- url     : https://prove2.me/submissions/ec2e4348-1a52-4834-a882-a70f1307ae74

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












/-- Independent concrete coefficient rows give a surjective hash map.
This supplies every target vector; it is not an assumed uniformity property. -/
theorem hashMap_surjective_sourceProof {v : ι → σ → K} (hv : LinearIndependent K v) :
    Function.Surjective (hashMap v) := by
  classical
  let f := Fintype.linearCombination K v
  let B : (ι → K) →ₗ[K] (σ → K) →ₗ[K] K :=
    (dotProductEquiv K σ).toLinearMap.comp f
  have hi : Function.Injective B :=
    (dotProductEquiv K σ).injective.comp hv.fintypeLinearCombination_injective
  have hs : Function.Surjective B.flip := (LinearMap.flip_surjective_iff₁).mpr hi
  intro target
  obtain ⟨w, hw⟩ := hs (dotProductEquiv K ι target)
  refine ⟨w, ?_⟩
  funext i
  have he := congrArg (fun φ : Module.Dual K (ι → K) => φ (Pi.single i 1)) hw
  change dotProduct (v i) w = target i
  simpa [B, f, Fintype.linearCombination_apply] using he

































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

universe u_2 u_3 u_4

theorem solution : ∀ {K : Type u_2} {σ : Type u_3} {ι : Type u_4} [inst : Fintype.{u_3} σ] [Fintype.{u_4} ι] [inst_2 : Field.{u_2} K]
  {v : ι → σ → K},
  @LinearIndependent.{u_4, u_2, max u_2 u_3} ι K (σ → K) v
      (@DivisionSemiring.toSemiring.{u_2} K (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2)))
      (@Pi.addCommMonoid.{u_3, u_2} σ (fun (a : σ) => K) fun (i : σ) =>
        @Semiring.toAddCommMonoid.{u_2} K
          (@DivisionSemiring.toSemiring.{u_2} K
            (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2))))
      (@Pi.Function.module.{u_3, u_2, u_2} σ K K
        (@DivisionSemiring.toSemiring.{u_2} K
          (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2)))
        (@Semiring.toAddCommMonoid.{u_2} K
          (@DivisionSemiring.toSemiring.{u_2} K
            (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2))))
        (@Semiring.toModule.{u_2} K
          (@DivisionSemiring.toSemiring.{u_2} K
            (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2))))) →
    @Function.Surjective.{max (u_2 + 1) (u_3 + 1), max (u_2 + 1) (u_4 + 1)} (σ → K) (ι → K)
      (@DFunLike.coe.{max (max (u_2 + 1) (u_3 + 1)) (u_4 + 1), max (u_2 + 1) (u_3 + 1), max (u_2 + 1) (u_4 + 1)}
        (@LinearMap.{u_2, u_2, max u_2 u_3, max u_2 u_4} K K
          (@DivisionSemiring.toSemiring.{u_2} K
            (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2)))
          (@DivisionSemiring.toSemiring.{u_2} K
            (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2)))
          (@RingHom.id.{u_2} K
            (@Semiring.toNonAssocSemiring.{u_2} K
              (@DivisionSemiring.toSemiring.{u_2} K
                (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2)))))
          (σ → K) (ι → K)
          (@Pi.addCommMonoid.{u_3, u_2} σ (fun (a : σ) => K) fun (i : σ) =>
            @Semiring.toAddCommMonoid.{u_2} K
              (@DivisionSemiring.toSemiring.{u_2} K
                (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2))))
          (@Pi.addCommMonoid.{u_4, u_2} ι (fun (a : ι) => K) fun (i : ι) =>
            @Semiring.toAddCommMonoid.{u_2} K
              (@DivisionSemiring.toSemiring.{u_2} K
                (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2))))
          (@Pi.Function.module.{u_3, u_2, u_2} σ K K
            (@DivisionSemiring.toSemiring.{u_2} K
              (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2)))
            (@Semiring.toAddCommMonoid.{u_2} K
              (@DivisionSemiring.toSemiring.{u_2} K
                (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2))))
            (@Semiring.toModule.{u_2} K
              (@DivisionSemiring.toSemiring.{u_2} K
                (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2)))))
          (@Pi.Function.module.{u_4, u_2, u_2} ι K K
            (@DivisionSemiring.toSemiring.{u_2} K
              (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2)))
            (@Semiring.toAddCommMonoid.{u_2} K
              (@DivisionSemiring.toSemiring.{u_2} K
                (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2))))
            (@Semiring.toModule.{u_2} K
              (@DivisionSemiring.toSemiring.{u_2} K
                (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2))))))
        (σ → K) (fun (x : σ → K) => ι → K)
        (@LinearMap.instFunLike.{u_2, u_2, max u_2 u_3, max u_2 u_4} K K (σ → K) (ι → K)
          (@DivisionSemiring.toSemiring.{u_2} K
            (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2)))
          (@DivisionSemiring.toSemiring.{u_2} K
            (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2)))
          (@Pi.addCommMonoid.{u_3, u_2} σ (fun (a : σ) => K) fun (i : σ) =>
            @Semiring.toAddCommMonoid.{u_2} K
              (@DivisionSemiring.toSemiring.{u_2} K
                (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2))))
          (@Pi.addCommMonoid.{u_4, u_2} ι (fun (a : ι) => K) fun (i : ι) =>
            @Semiring.toAddCommMonoid.{u_2} K
              (@DivisionSemiring.toSemiring.{u_2} K
                (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2))))
          (@Pi.Function.module.{u_3, u_2, u_2} σ K K
            (@DivisionSemiring.toSemiring.{u_2} K
              (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2)))
            (@Semiring.toAddCommMonoid.{u_2} K
              (@DivisionSemiring.toSemiring.{u_2} K
                (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2))))
            (@Semiring.toModule.{u_2} K
              (@DivisionSemiring.toSemiring.{u_2} K
                (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2)))))
          (@Pi.Function.module.{u_4, u_2, u_2} ι K K
            (@DivisionSemiring.toSemiring.{u_2} K
              (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2)))
            (@Semiring.toAddCommMonoid.{u_2} K
              (@DivisionSemiring.toSemiring.{u_2} K
                (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2))))
            (@Semiring.toModule.{u_2} K
              (@DivisionSemiring.toSemiring.{u_2} K
                (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2)))))
          (@RingHom.id.{u_2} K
            (@Semiring.toNonAssocSemiring.{u_2} K
              (@DivisionSemiring.toSemiring.{u_2} K
                (@Semifield.toDivisionSemiring.{u_2} K (@Field.toSemifield.{u_2} K inst_2))))))
        (@ThreeSum.HashFamily.hashMap.{u_2, u_3, u_4} K σ ι inst inst_2 v)) := by
  exact @ThreeSum.HashFamily.hashMap_surjective_sourceProof

#print axioms solution
