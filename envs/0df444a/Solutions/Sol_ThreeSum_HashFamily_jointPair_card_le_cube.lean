-- Prove2me | solution 1 for ThreeSum.HashFamily.jointPair_card_le_cube
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:12:48.264918+00:00
-- url     : https://prove2.me/submissions/c8bfabe6-b175-45b2-a6dd-02d5dcb242c1

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
import Theorems.Thm_ThreeSum_HashFamily_hashMap_surjective
import Theorems.Thm_ThreeSum_HashFamily_linear_fiber_card
import Theorems.Thm_ThreeSum_HashFamily_three_relation


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










theorem oneHot_three_independent {s t u : α → Bool}
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) :
    LinearIndependent K ![oneHot (K := K) s, oneHot t, oneHot u] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hr := three_relation hst hsu htu (a := g 0) (b := g 1) (c := g 2) (fun p => by
    have hp := congrFun hg p
    simpa [Fin.sum_univ_succ, add_assoc] using hp)
  fin_cases i <;> simp_all














end LinearIndependence

section UniformFibers

variable {σ ι : Type*} [Fintype σ] [Fintype ι] [Field K]





















































/-- The exact joint-output count for independent hash coefficient rows. -/
theorem hash_fiber_card [Fintype K] [DecidableEq K] [DecidableEq σ] [DecidableEq ι]
    {v : ι → σ → K}
    (hv : LinearIndependent K v) (target : ι → K) :
    Fintype.card K ^ Fintype.card ι *
        (Finset.univ.filter (fun w : σ → K => hashMap v w = target)).card =
      Fintype.card K ^ Fintype.card σ := by
  classical
  simpa using linear_fiber_card (hashMap v) (hashMap_surjective hv) target

end UniformFibers

section ActualHashes

variable {ι : Type*} [Fintype α] [Field K]





theorem hashValue_eq_dotProduct (w : α × Bool → K) (s : α → Bool) :
    hashValue w s = ∑ p, oneHot (K := K) s p * w p := by
  classical
  simp [hashValue, oneHot, Fintype.sum_prod_type]

theorem hashValue_family (v : ι → α → Bool) (w : α × Bool → K)
    [Fintype ι] :
    (fun i => hashValue w (v i)) = hashMap (fun i => oneHot (K := K) (v i)) w := by
  funext i
  exact hashValue_eq_dotProduct w (v i)

end ActualHashes

section WordEvents

variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]










theorem wordEvent_eq_linear_fiber {r : ℕ}
    (words : Fin r → α → Bool) (target : Fin r → K) :
    wordEvent words target =
      Finset.univ.filter (fun w => hashMap (fun i => oneHot (K := K) (words i)) w = target) := by
  ext w
  simp only [wordEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← hashValue_family]
  exact funext_iff.symm

/-- Exact uniform joint count, instantiated with the actual one-hot family. -/
theorem wordEvent_card {r : ℕ} (words : Fin r → α → Bool) (target : Fin r → K)
    (hwords : LinearIndependent K (fun i => oneHot (K := K) (words i))) :
    Fintype.card K ^ r * (wordEvent words target).card =
      Fintype.card (α × Bool → K) := by
  rw [wordEvent_eq_linear_fiber]
  simpa using hash_fiber_card hwords target







































theorem tripleEvent_card {s t u : α → Bool}
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) (a b c : K) :
    Fintype.card K ^ 3 * (wordEvent ![s, t, u] ![a, b, c]).card =
      Fintype.card (α × Bool → K) := by
  apply wordEvent_card
  convert oneHot_three_independent (K := K) hst hsu htu using 1
  funext i
  fin_cases i <;> rfl

/-- Two distinct edges always impose at least three independent hash tests
when the left and right vertex classes are disjoint. -/
theorem jointPair_card_le_cube_sourceProof {s t u v : α → Bool}
    (hst : s ≠ t) (hsv : s ≠ v) (htu : t ≠ u) (huv : u ≠ v)
    (hpair : (s, t) ≠ (u, v)) (a b : K) :
    Fintype.card K ^ 3 * (pairEvent s t a b ∩ pairEvent u v a b).card ≤
      Fintype.card (α × Bool → K) := by
  by_cases hsu : s = u
  · have htv : t ≠ v := by
      intro htv
      exact hpair (Prod.ext hsu htv)
    have hsub : pairEvent s t a b ∩ pairEvent u v a b ⊆
        wordEvent ![s, t, v] ![a, b, b] := by
      intro w hw
      simpa [wordEvent, Fin.forall_fin_succ] using
        And.intro ((Finset.mem_filter.mp (Finset.mem_inter.mp hw).1).2).1
          (And.intro ((Finset.mem_filter.mp (Finset.mem_inter.mp hw).1).2).2
            ((Finset.mem_filter.mp (Finset.mem_inter.mp hw).2).2).2)
    exact (Nat.mul_le_mul_left _ (Finset.card_le_card hsub)).trans_eq
      (tripleEvent_card hst hsv htv a b b)
  · have hsub : pairEvent s t a b ∩ pairEvent u v a b ⊆
        wordEvent ![s, t, u] ![a, b, a] := by
      intro w hw
      simpa [wordEvent, Fin.forall_fin_succ] using
        And.intro ((Finset.mem_filter.mp (Finset.mem_inter.mp hw).1).2).1
          (And.intro ((Finset.mem_filter.mp (Finset.mem_inter.mp hw).1).2).2
            ((Finset.mem_filter.mp (Finset.mem_inter.mp hw).2).2).1)
    exact (Nat.mul_le_mul_left _ (Finset.card_le_card hsub)).trans_eq
      (tripleEvent_card hst hsu htu a b a)





































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

universe u_1 u_2

theorem solution : ∀ {α : Type u_1} {K : Type u_2} [inst : Fintype.{u_1} α] [inst_1 : DecidableEq.{u_1 + 1} α] [inst_2 : Field.{u_2} K]
  [inst_3 : Fintype.{u_2} K] [inst_4 : DecidableEq.{u_2 + 1} K] {s t u v : α → Bool},
  @Ne.{u_1 + 1} (α → Bool) s t →
    @Ne.{u_1 + 1} (α → Bool) s v →
      @Ne.{u_1 + 1} (α → Bool) t u →
        @Ne.{u_1 + 1} (α → Bool) u v →
          @Ne.{u_1 + 1} (Prod.{u_1, u_1} (α → Bool) (α → Bool)) (@Prod.mk.{u_1, u_1} (α → Bool) (α → Bool) s t)
              (@Prod.mk.{u_1, u_1} (α → Bool) (α → Bool) u v) →
            ∀ (a b : K),
              @LE.le.{0} Nat instLENat
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                    (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                    (@Fintype.card.{u_2} K inst_3) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                  (@Finset.card.{max u_1 u_2} (Prod.{u_1, 0} α Bool → K)
                    (@Inter.inter.{max u_2 u_1} (Finset.{max u_1 u_2} (Prod.{u_1, 0} α Bool → K))
                      (@Finset.instInter.{max u_1 u_2} (Prod.{u_1, 0} α Bool → K)
                        fun (a b : Prod.{u_1, 0} α Bool → K) =>
                        @Fintype.decidablePiFintype.{u_2, u_1} (Prod.{u_1, 0} α Bool)
                          (fun (a : Prod.{u_1, 0} α Bool) => K) (fun (a : Prod.{u_1, 0} α Bool) => inst_4)
                          (@instFintypeProd.{u_1, 0} α Bool inst Bool.fintype) a b)
                      (@ThreeSum.HashFamily.pairEvent.{u_1, u_2} α K inst inst_1 inst_2 inst_3 inst_4 s t a b)
                      (@ThreeSum.HashFamily.pairEvent.{u_1, u_2} α K inst inst_1 inst_2 inst_3 inst_4 u v a b))))
                (@Fintype.card.{max u_1 u_2} (Prod.{u_1, 0} α Bool → K)
                  (@Pi.instFintype.{u_1, u_2} (Prod.{u_1, 0} α Bool) (fun (a : Prod.{u_1, 0} α Bool) => K)
                    (fun (a b : Prod.{u_1, 0} α Bool) =>
                      @instDecidableEqProd.{u_1, 0} α Bool inst_1 instDecidableEqBool a b)
                    (@instFintypeProd.{u_1, 0} α Bool inst Bool.fintype) fun (a : Prod.{u_1, 0} α Bool) => inst_3)) := by
  exact @ThreeSum.HashFamily.jointPair_card_le_cube_sourceProof

#print axioms solution
