-- Prove2me | solution 1 for ThreeSum.HashFamily.loadedPairMass_bound
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:12:53.71855+00:00
-- url     : https://prove2.me/submissions/604ef5cf-3235-4029-8ff3-57ac1514b5df

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




theorem exists_coordinate_ne {s t : α → Bool} (hst : s ≠ t) :
    ∃ i, s i ≠ t i := by
  classical
  by_contra h
  push Not at h
  exact hst (funext h)

section Relations

variable [Ring K]

/-- Two distinct one-hot words have no nontrivial linear relation. -/
theorem two_relation {s t : α → Bool} (hst : s ≠ t) {a b : K}
    (h : ∀ p, a * oneHot s p + b * oneHot t p = 0) : a = 0 ∧ b = 0 := by
  obtain ⟨i, hi⟩ := exists_coordinate_ne hst
  have ha := h (i, s i)
  have hb := h (i, t i)
  simpa [oneHot, hi, Ne.symm hi] using And.intro ha hb



















































end Relations

section LinearIndependence

variable [Field K]

theorem oneHot_two_independent {s t : α → Bool} (hst : s ≠ t) :
    LinearIndependent K ![oneHot (K := K) s, oneHot t] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hr := two_relation hst (a := g 0) (b := g 1) (fun p => by
    have hp := congrFun hg p
    simpa [Fin.sum_univ_succ] using hp)
  fin_cases i <;> simp_all

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















theorem pairEvent_eq (s t : α → Bool) (a b : K) :
    pairEvent s t a b = wordEvent ![s, t] ![a, b] := by
  ext w
  simp [pairEvent, wordEvent, Fin.forall_fin_succ]











theorem pairEvent_card {s t : α → Bool} (hst : s ≠ t) (a b : K) :
    Fintype.card K ^ 2 * (pairEvent s t a b).card =
      Fintype.card (α × Bool → K) := by
  rw [pairEvent_eq]
  apply wordEvent_card
  convert oneHot_two_independent (K := K) hst using 1
  funext i
  fin_cases i <;> rfl

theorem tripleEvent_card {s t u : α → Bool}
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) (a b c : K) :
    Fintype.card K ^ 3 * (wordEvent ![s, t, u] ![a, b, c]).card =
      Fintype.card (α × Bool → K) := by
  apply wordEvent_card
  convert oneHot_three_independent (K := K) hst hsu htu using 1
  funext i
  fin_cases i <;> rfl



































































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







theorem sum_filtered_cards {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (A : Finset X) (B : Finset Y) (P : X → Y → Prop) [DecidableRel P] :
    (∑ x ∈ A, (B.filter (P x)).card) =
      ∑ y ∈ B, (A.filter (fun x => P x y)).card := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

/-- Conditional bucket-load bound proved from actual three-word uniformity.
The right endpoint must be outside the entire left vertex class. -/
theorem loadedPairMass_bound_sourceProof {s t : α → Bool} (hst : s ≠ t) (a b : K)
    (vertices : Finset (α → Bool)) (hcross : ∀ u ∈ vertices, u ≠ t) :
    Fintype.card K ^ 3 * loadedPairMass s t a b vertices ≤
      (Fintype.card K + vertices.card) * Fintype.card (α × Bool → K) := by
  unfold loadedPairMass bucketSize
  rw [sum_filtered_cards, Finset.mul_sum]
  have hterm : ∀ u ∈ vertices, Fintype.card K ^ 3 *
      ((pairEvent s t a b).filter (fun w => hashValue w u = a)).card ≤
        Fintype.card (α × Bool → K) * (1 + if u = s then Fintype.card K else 0) := by
    intro u hu
    by_cases he : u = s
    · subst u
      have hfilter : (pairEvent s t a b).filter (fun w => hashValue w s = a) =
          pairEvent s t a b := by
        ext w
        constructor
        · intro hw
          exact (Finset.mem_filter.mp hw).1
        · intro hw
          exact Finset.mem_filter.mpr ⟨hw, (Finset.mem_filter.mp hw).2.1⟩
      rw [hfilter]
      have hc := pairEvent_card hst a b
      calc
        _ = Fintype.card K * (Fintype.card K ^ 2 * (pairEvent s t a b).card) := by ring
        _ = Fintype.card K * Fintype.card (α × Bool → K) := by rw [hc]
        _ ≤ _ := by
          simp only [ite_true]
          rw [Nat.mul_comm (Fintype.card K)]
          exact Nat.mul_le_mul_left _ (by omega)
    · have hfilter : (pairEvent s t a b).filter (fun w => hashValue w u = a) =
          wordEvent ![s, t, u] ![a, b, a] := by
        ext w
        simp [pairEvent, wordEvent, Fin.forall_fin_succ, and_assoc]
      rw [hfilter, tripleEvent_card hst (Ne.symm he) (Ne.symm (hcross u hu)) a b a]
      simp [he]
  calc
    _ ≤ ∑ u ∈ vertices, Fintype.card (α × Bool → K) *
        (1 + if u = s then Fintype.card K else 0) := Finset.sum_le_sum hterm
    _ ≤ _ := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
      by_cases hs : s ∈ vertices
      · simp [hs, Nat.mul_comm, Nat.add_comm]
      · simp only [Finset.sum_const, smul_eq_mul, mul_one,
          Finset.sum_ite_eq', if_neg hs, add_zero]
        rw [Nat.mul_comm (Fintype.card (α × Bool → K))]
        exact Nat.mul_le_mul_right _ (by omega)























































































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
        @LE.le.{0} Nat instLENat
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (@Fintype.card.{u_2} K inst_3) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (@ThreeSum.HashFamily.loadedPairMass.{u_1, u_2} α K inst inst_1 inst_2 inst_3 inst_4 s t a b vertices))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fintype.card.{u_2} K inst_3)
              (@Finset.card.{u_1} (α → Bool) vertices))
            (@Fintype.card.{max u_1 u_2} (Prod.{u_1, 0} α Bool → K)
              (@Pi.instFintype.{u_1, u_2} (Prod.{u_1, 0} α Bool) (fun (a : Prod.{u_1, 0} α Bool) => K)
                (fun (a b : Prod.{u_1, 0} α Bool) =>
                  @instDecidableEqProd.{u_1, 0} α Bool inst_1 instDecidableEqBool a b)
                (@instFintypeProd.{u_1, 0} α Bool inst Bool.fintype) fun (a : Prod.{u_1, 0} α Bool) => inst_3))) := by
  exact @ThreeSum.HashFamily.loadedPairMass_bound_sourceProof

#print axioms solution
