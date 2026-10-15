-- Prove2me | solution 1 for ThreeSum.HashFamily.heavyPairEvent_bound
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:37:49.610898+00:00
-- url     : https://prove2.me/submissions/da95b713-6003-4595-b8de-b01b3d65457c

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
import Theorems.Thm_ThreeSum_HashFamily_loadedPairMass_bound


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






















































































































































end GraphMoments

section SeparableTrimming

variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]



































































/-- Finite Markov counting, with the actual bucket cardinality. -/
theorem heavyPairEvent_markov (s t : α → Bool) (a b : K)
    (vertices : Finset (α → Bool)) (B : ℕ) :
    B * (heavyPairEvent s t a b vertices B).card ≤ loadedPairMass s t a b vertices := by
  calc
    _ = ∑ _w ∈ heavyPairEvent s t a b vertices B, B := by simp [Nat.mul_comm]
    _ ≤ ∑ w ∈ heavyPairEvent s t a b vertices B, bucketSize vertices w a := by
      apply Finset.sum_le_sum
      intro w hw
      exact (Finset.mem_filter.mp hw).2.le
    _ ≤ loadedPairMass s t a b vertices := by
      unfold loadedPairMass
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..)
        (fun w hw hnot => Nat.zero_le _)

/-- Discarding a bucket above the prescribed threshold loses at most a
quarter of each pair's raw representation mass, uniformly in the targets. -/
theorem heavyPairEvent_bound_sourceProof {s t : α → Bool} (hst : s ≠ t) (a b : K)
    (vertices : Finset (α → Bool)) (hcross : ∀ u ∈ vertices, u ≠ t)
    (B : ℕ) (hB : 4 * (Fintype.card K + vertices.card) ≤ B * Fintype.card K) :
    4 * Fintype.card K ^ 2 * (heavyPairEvent s t a b vertices B).card ≤
      Fintype.card (α × Bool → K) := by
  have hm := heavyPairEvent_markov s t a b vertices B
  have hl := loadedPairMass_bound hst a b vertices hcross
  have hp : 0 < Fintype.card K := Fintype.card_pos
  have hpos : 0 < B * Fintype.card K := lt_of_lt_of_le (by omega) hB
  apply Nat.le_of_mul_le_mul_left (c := B * Fintype.card K) ?_ hpos
  calc
    _ = 4 * (Fintype.card K ^ 3 *
        (B * (heavyPairEvent s t a b vertices B).card)) := by ring
    _ ≤ 4 * (Fintype.card K ^ 3 * loadedPairMass s t a b vertices) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hm)
    _ ≤ 4 * ((Fintype.card K + vertices.card) * Fintype.card (α × Bool → K)) :=
      Nat.mul_le_mul_left _ hl
    _ ≤ _ := by
      simpa only [Nat.mul_assoc] using
        Nat.mul_le_mul_right (Fintype.card (α × Bool → K)) hB













































end SeparableTrimming

section TrimmedGraphMoments

variable {E : Type*} [Fintype E] [DecidableEq E]
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]
































end TrimmedGraphMoments

end ThreeSum.HashFamily

end

universe u_1 u_2

theorem solution : ∀ {α : Type u_1} {K : Type u_2} [inst : Fintype.{u_1} α] [inst_1 : DecidableEq.{u_1 + 1} α] [inst_2 : Field.{u_2} K]
  [inst_3 : Fintype.{u_2} K] [inst_4 : DecidableEq.{u_2 + 1} K] {s t : α → Bool},
  @Ne.{u_1 + 1} (α → Bool) s t →
    ∀ (a b : K) (vertices : Finset.{u_1} (α → Bool)),
      (∀ (u : α → Bool),
          @Membership.mem.{u_1, u_1} (α → Bool) (Finset.{u_1} (α → Bool))
              (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} (α → Bool)) (α → Bool)
                (@Finset.instSetLike.{u_1} (α → Bool)))
              vertices u →
            @Ne.{u_1 + 1} (α → Bool) u t) →
        ∀ (B : Nat),
          @LE.le.{0} Nat instLENat
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fintype.card.{u_2} K inst_3)
                  (@Finset.card.{u_1} (α → Bool) vertices)))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) B (@Fintype.card.{u_2} K inst_3)) →
            @LE.le.{0} Nat instLENat
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                    (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                    (@Fintype.card.{u_2} K inst_3) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (@Finset.card.{max u_1 u_2} (Prod.{u_1, 0} α Bool → K)
                  (@ThreeSum.HashFamily.heavyPairEvent.{u_1, u_2} α K inst inst_1 inst_2 inst_3 inst_4 s t a b vertices
                    B)))
              (@Fintype.card.{max u_1 u_2} (Prod.{u_1, 0} α Bool → K)
                (@Pi.instFintype.{u_1, u_2} (Prod.{u_1, 0} α Bool) (fun (a : Prod.{u_1, 0} α Bool) => K)
                  (fun (a b : Prod.{u_1, 0} α Bool) =>
                    @instDecidableEqProd.{u_1, 0} α Bool inst_1 instDecidableEqBool a b)
                  (@instFintypeProd.{u_1, 0} α Bool inst Bool.fintype) fun (a : Prod.{u_1, 0} α Bool) => inst_3)) := by
  exact @ThreeSum.HashFamily.heavyPairEvent_bound_sourceProof

#print axioms solution
