-- Prove2me | solution 1 for ThreeSum.HashFamily.raw_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:37:44.496881+00:00
-- url     : https://prove2.me/submissions/ec7d4496-d35d-44c4-912e-99ca3857e31f

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
import Theorems.Thm_ThreeSum_HashFamily_four_relation_of_mask_ne
import Theorems.Thm_ThreeSum_HashFamily_hashMap_surjective
import Theorems.Thm_ThreeSum_HashFamily_jointPair_card_le_cube
import Theorems.Thm_ThreeSum_HashFamily_linear_fiber_card
import Theorems.Thm_ThreeSum_HashFamily_sum_incidenceCount_sq


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











theorem oneHot_four_independent {s t u v : α → Bool}
    (hst : s ≠ t) (hsu : s ≠ u) (hsv : s ≠ v)
    (htu : t ≠ u) (htv : t ≠ v) (huv : u ≠ v)
    (hm : ∃ i, (s i == t i) ≠ (u i == v i)) :
    LinearIndependent K ![oneHot (K := K) s, oneHot t, oneHot u, oneHot v] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hr := four_relation_of_mask_ne hst hsu hsv htu htv huv hm
    (a := g 0) (b := g 1) (c := g 2) (d := g 3) (fun p => by
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








































theorem jointPair_card_four {s t u v : α → Bool}
    (hst : s ≠ t) (hsu : s ≠ u) (hsv : s ≠ v)
    (htu : t ≠ u) (htv : t ≠ v) (huv : u ≠ v)
    (hm : ∃ i, (s i == t i) ≠ (u i == v i)) (a b : K) :
    Fintype.card K ^ 4 * (pairEvent s t a b ∩ pairEvent u v a b).card =
      Fintype.card (α × Bool → K) := by
  have he : pairEvent s t a b ∩ pairEvent u v a b =
      wordEvent ![s, t, u, v] ![a, b, a, b] := by
    ext w
    simp [pairEvent, wordEvent, Fin.forall_fin_succ, and_assoc]
  rw [he]
  apply wordEvent_card
  convert oneHot_four_independent (K := K) hst hsu hsv htu htv huv hm using 1
  funext i
  fin_cases i <;> rfl





















end WordEvents

section IncidenceCounting

variable {Ω E : Type*} [Fintype Ω] [Fintype E] [DecidableEq Ω]

























































end IncidenceCounting

section GraphMoments

variable {E : Type*} [Fintype E] [DecidableEq E]
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]







































theorem joint_pair_charge (left right : E → α → Bool)
    (hinj : Function.Injective (fun e => (left e, right e)))
    (hcross : ∀ e f, left e ≠ right f) (a b : K) (e f : E) :
    Fintype.card K ^ 4 *
        (pairEvent (left e) (right e) a b ∩ pairEvent (left f) (right f) a b).card ≤
      Fintype.card (α × Bool → K) *
        (1 + (if e = f then Fintype.card K ^ 2 else 0) +
          (if f ∈ badPartners left right e then Fintype.card K else 0)) := by
  by_cases hef : e = f
  · subst f
    have hc := pairEvent_card (hcross e e) a b
    have heq : Fintype.card K ^ 4 * (pairEvent (left e) (right e) a b).card =
        Fintype.card (α × Bool → K) * Fintype.card K ^ 2 := by
      calc
        _ = Fintype.card K ^ 2 *
            (Fintype.card K ^ 2 * (pairEvent (left e) (right e) a b).card) := by ring
        _ = _ := by rw [hc]; ring
    simp only [Finset.inter_self, ite_true, heq]
    apply Nat.mul_le_mul_left
    omega
  · have hpair : (left e, right e) ≠ (left f, right f) := fun h => hef (hinj h)
    by_cases hbad : f ∈ badPartners left right e
    · have hc := jointPair_card_le_cube (hcross e e) (hcross e f)
        (Ne.symm (hcross f e)) (hcross f f) hpair a b
      calc
        _ = Fintype.card K * (Fintype.card K ^ 3 *
            (pairEvent (left e) (right e) a b ∩ pairEvent (left f) (right f) a b).card) := by ring
        _ ≤ Fintype.card K * Fintype.card (α × Bool → K) := Nat.mul_le_mul_left _ hc
        _ ≤ _ := by
          simp only [if_neg hef, if_pos hbad, add_zero]
          rw [Nat.mul_comm (Fintype.card K)]
          exact Nat.mul_le_mul_left _ (by omega)
    · have hn : left e ≠ left f ∧ right e ≠ right f ∧
          outputMask left right e ≠ outputMask left right f := by
        simpa [badPartners, not_or] using hbad
      have hm : ∃ i, (left e i == right e i) ≠ (left f i == right f i) :=
        exists_coordinate_ne hn.2.2
      have hc := jointPair_card_four (hcross e e) hn.1 (hcross e f)
        (Ne.symm (hcross f e)) hn.2.1 (hcross f f) hm a b
      simp only [if_neg hef, if_neg hbad, add_zero, mul_one, hc]
      rfl

/-- Full second moment, derived by counting the exceptional partner classes.
`B` bounds the number of shared-endpoint or same-output partners per edge;
the local graph instantiation takes `B = 2*Delta + G`. -/
theorem raw_second_moment_sourceProof (left right : E → α → Bool)
    (hinj : Function.Injective (fun e => (left e, right e)))
    (hcross : ∀ e f, left e ≠ right f)
    (B : ℕ) (hB : ∀ e, (badPartners left right e).card ≤ B) (a b : K) :
    Fintype.card K ^ 4 *
        (∑ w, incidenceCount (fun e => pairEvent (left e) (right e) a b) w ^ 2) ≤
      Fintype.card (α × Bool → K) *
        (Fintype.card E * Fintype.card K ^ 2 + Fintype.card E ^ 2 +
          Fintype.card E * B * Fintype.card K) := by
  have hrow : ∀ e : E, (∑ f : E, Fintype.card K ^ 4 *
      (pairEvent (left e) (right e) a b ∩ pairEvent (left f) (right f) a b).card) ≤
      Fintype.card (α × Bool → K) * (Fintype.card E + Fintype.card K ^ 2 + B * Fintype.card K) := by
    intro e
    calc
      _ ≤ ∑ f : E, Fintype.card (α × Bool → K) *
          (1 + (if e = f then Fintype.card K ^ 2 else 0) +
            (if f ∈ badPartners left right e then Fintype.card K else 0)) :=
        Finset.sum_le_sum (fun f hf => joint_pair_charge left right hinj hcross a b e f)
      _ = Fintype.card (α × Bool → K) *
          (Fintype.card E + Fintype.card K ^ 2 + (badPartners left right e).card * Fintype.card K) := by
        rw [← Finset.mul_sum]
        congr 1
        simp [Finset.sum_add_distrib]
      _ ≤ _ := by
        apply Nat.mul_le_mul_left
        exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (hB e)) _
  calc
    _ = ∑ e : E, ∑ f : E, Fintype.card K ^ 4 *
        (pairEvent (left e) (right e) a b ∩ pairEvent (left f) (right f) a b).card := by
      rw [sum_incidenceCount_sq, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      exact Finset.mul_sum ..
    _ ≤ ∑ _e : E, Fintype.card (α × Bool → K) *
        (Fintype.card E + Fintype.card K ^ 2 + B * Fintype.card K) :=
      Finset.sum_le_sum (fun e he => hrow e)
    _ = _ := by simp; ring





























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

universe u_1 u_2 u_3

theorem solution : ∀ {α : Type u_1} {K : Type u_2} {E : Type u_3} [inst : Fintype.{u_3} E] [DecidableEq.{u_3 + 1} E]
  [inst_2 : Fintype.{u_1} α] [inst_3 : DecidableEq.{u_1 + 1} α] [inst_4 : Field.{u_2} K] [inst_5 : Fintype.{u_2} K]
  [inst_6 : DecidableEq.{u_2 + 1} K] (left right : E → α → Bool),
  (@Function.Injective.{u_3 + 1, u_1 + 1} E (Prod.{u_1, u_1} (α → Bool) (α → Bool)) fun (e : E) =>
      @Prod.mk.{u_1, u_1} (α → Bool) (α → Bool) (left e) (right e)) →
    (∀ (e f : E), @Ne.{u_1 + 1} (α → Bool) (left e) (right f)) →
      ∀ (B : Nat),
        (∀ (e : E),
            @LE.le.{0} Nat instLENat
              (@Finset.card.{u_3} E (@ThreeSum.HashFamily.badPartners.{u_1, u_3} α E inst inst_2 left right e)) B) →
          ∀ (a b : K),
            @LE.le.{0} Nat instLENat
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                  (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                  (@Fintype.card.{u_2} K inst_5) (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                (∑ w : Prod.{u_1, 0} α Bool → K,
                  @HPow.hPow.{0, 0, 0} Nat Nat Nat
                    (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                    (@ThreeSum.HashFamily.incidenceCount.{max u_2 u_1, u_3} (Prod.{u_1, 0} α Bool → K) E inst
                      (fun (a b : Prod.{u_1, 0} α Bool → K) =>
                        @Fintype.decidablePiFintype.{u_2, u_1} (Prod.{u_1, 0} α Bool)
                          (fun (a : Prod.{u_1, 0} α Bool) => K) (fun (a : Prod.{u_1, 0} α Bool) => inst_6)
                          (@instFintypeProd.{u_1, 0} α Bool inst_2 Bool.fintype) a b)
                      (fun (e : E) =>
                        @ThreeSum.HashFamily.pairEvent.{u_1, u_2} α K inst_2 inst_3 inst_4 inst_5 inst_6 (left e)
                          (right e) a b)
                      w)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@Fintype.card.{max u_1 u_2} (Prod.{u_1, 0} α Bool → K)
                  (@Pi.instFintype.{u_1, u_2} (Prod.{u_1, 0} α Bool) (fun (a : Prod.{u_1, 0} α Bool) => K)
                    (fun (a b : Prod.{u_1, 0} α Bool) =>
                      @instDecidableEqProd.{u_1, 0} α Bool inst_3 instDecidableEqBool a b)
                    (@instFintypeProd.{u_1, 0} α Bool inst_2 Bool.fintype) fun (a : Prod.{u_1, 0} α Bool) => inst_5))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Fintype.card.{u_3} E inst)
                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                        (@Fintype.card.{u_2} K inst_5) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                      (@Fintype.card.{u_3} E inst) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Fintype.card.{u_3} E inst) B)
                    (@Fintype.card.{u_2} K inst_5)))) := by
  exact @ThreeSum.HashFamily.raw_second_moment_sourceProof

#print axioms solution
