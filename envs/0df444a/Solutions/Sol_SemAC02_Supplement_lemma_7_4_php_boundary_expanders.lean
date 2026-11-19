-- Prove2me | solution 1 for SemAC02.Supplement.lemma_7_4_php_boundary_expanders
-- status  : ACCEPTED   (prove)
-- author  : @Henry Yuen
-- created : 2026-11-18T14:49:21.697272+00:00
-- url     : https://prove2.me/submissions/9277114a-b606-47e4-9638-def1f0f37a5b

import Definitions.Def_SemAC02_bernProb
import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_PCNonBool_boundaryOn
import Definitions.Def_PCNonBool_nbrOn
import Definitions.Def_SemAC02_Supplement_expansionRank
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_SemAC02_Supplement_phpG
open _root_.SemAC02 _root_.SemAC02.Supplement
open _root_.AC02Frege
namespace P2MRandomGraphProof
section
-- Inlined Solutions.P2MBernoulliAlgebra

open Finset

namespace SemAC02.P2MBernoulliAlgebra

noncomputable def bitWeight (p : ℝ) (b : Bool) : ℝ := if b then p else 1-p

noncomputable def weight {I : Type*} [Fintype I] (p : ℝ) (x : I → Bool) : ℝ :=
  ∏ i, bitWeight p (x i)

theorem bitWeight_nonneg {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (b : Bool) : 0 ≤ bitWeight p b := by
  cases b
  · simpa [bitWeight] using sub_nonneg.mpr hp'
  · simpa [bitWeight] using hp

theorem weight_nonneg {I : Type*} [Fintype I] {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (x : I → Bool) :
    0 ≤ weight p x := prod_nonneg (fun _ _ => bitWeight_nonneg hp hp' _)

@[simp] theorem bitWeight_sum (p : ℝ) : ∑ b : Bool, bitWeight p b = 1 := by
  simp [bitWeight]

@[simp] theorem weight_sum (I : Type*) [Fintype I] [DecidableEq I] (p : ℝ) : ∑ x : I → Bool, weight p x = 1 := by
  simp only [weight]
  rw [← Fintype.prod_sum]
  simp only [bitWeight_sum,prod_const_one]

theorem bernProb_eq_weight (p : ℝ) {m : ℕ} (E : (Fin m → Bool) → Bool) :
    bernProb p E = ∑ x, if E x then weight p x else 0 := rfl

@[simp] theorem prob_true (p : ℝ) (m : ℕ) : bernProb p (fun _ : Fin m → Bool => true) = 1 := by
  simp [bernProb_eq_weight]

@[simp] theorem prob_false (p : ℝ) (m : ℕ) : bernProb p (fun _ : Fin m → Bool => false) = 0 := by
  simp [bernProb_eq_weight]

theorem prob_nonneg {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) {m : ℕ} (E : (Fin m → Bool) → Bool) :
    0 ≤ bernProb p E := by
  rw [bernProb_eq_weight]
  apply sum_nonneg
  intro x _
  split_ifs
  · exact weight_nonneg hp hp' x
  · exact le_rfl

theorem prob_le_one {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) {m : ℕ} (E : (Fin m → Bool) → Bool) :
    bernProb p E ≤ 1 := by
  rw [bernProb_eq_weight,← weight_sum (Fin m) p]
  apply sum_le_sum
  intro x _
  split_ifs
  · exact le_rfl
  · exact weight_nonneg hp hp' x

theorem prob_add_compl (p : ℝ) {m : ℕ} (E : (Fin m → Bool) → Bool) :
    bernProb p E + bernProb p (fun x => !E x) = 1 := by
  rw [bernProb_eq_weight,bernProb_eq_weight,← sum_add_distrib,← weight_sum (Fin m) p]
  apply sum_congr rfl
  intro x _
  cases he : E x <;> simp [he]

theorem prob_compl (p : ℝ) {m : ℕ} (E : (Fin m → Bool) → Bool) :
    bernProb p (fun x => !E x) = 1-bernProb p E := by
  linarith [prob_add_compl p E]

def complementEquiv (I : Type*) : (I → Bool) ≃ (I → Bool) where
  toFun x i := !x i
  invFun x i := !x i
  left_inv x := by funext i; simp only [Bool.not_not]
  right_inv x := by funext i; simp only [Bool.not_not]

theorem bitWeight_compl (p : ℝ) (b : Bool) : bitWeight p (!b) = bitWeight (1-p) b := by
  cases b <;> simp [bitWeight]

theorem weight_compl {I : Type*} [Fintype I] (p : ℝ) (x : I → Bool) :
    weight p (complementEquiv I x) = weight (1-p) x := by
  unfold weight
  apply prod_congr rfl
  intro i _
  exact bitWeight_compl p (x i)

theorem prob_complement_inputs (p : ℝ) {m : ℕ} (E : (Fin m → Bool) → Bool) :
    bernProb p (fun x => E (fun i => !x i)) = bernProb (1-p) E := by
  rw [bernProb_eq_weight,bernProb_eq_weight]
  have he := Equiv.sum_comp (complementEquiv (Fin m))
    (fun x => if E (fun i => !x i) then weight p x else 0)
  rw [← he]
  apply sum_congr rfl
  intro x _
  simp only [complementEquiv,Equiv.coe_fn_mk,Bool.not_not]
  exact congrArg (fun w : ℝ => if E x then w else 0) (weight_compl p x)

end SemAC02.P2MBernoulliAlgebra
end

section
-- Inlined Solutions.P2MBernoulliProduct

set_option maxHeartbeats 1000000

open Finset SemAC02.P2MBernoulliAlgebra

namespace SemAC02.P2MBernoulliProduct

/-- The same finite product probability on an arbitrary finite coordinate type. -/
noncomputable def prob {I : Type*} [Fintype I] [DecidableEq I] (p : ℝ) (E : (I → Bool) → Bool) : ℝ :=
  ∑ x, if E x then weight p x else 0

theorem prob_complement {I : Type*} [Fintype I] [DecidableEq I] (p : ℝ) (E : (I → Bool) → Bool) :
    prob p (fun x => !E x) = 1-prob p E := by
  classical
  have h : prob p E + prob p (fun x => !E x) = 1 := by
    rw [prob,prob,← sum_add_distrib,← weight_sum I p]
    apply sum_congr rfl
    intro x _
    cases he : E x <;> simp [he]
  linarith

theorem prob_all_coordinates {I : Type*} [Fintype I] [DecidableEq I] (p : ℝ) :
    prob p (fun x : I → Bool => decide (∀ i, x i = true)) = p ^ Fintype.card I := by
  classical
  unfold prob
  have he : (fun x : I → Bool => if decide (∀ i, x i = true) then weight p x else 0) =
      (fun x => if x = (fun _ => true) then weight p x else 0) := by
    funext x
    congr 1
    simp only [decide_eq_true_eq,funext_iff]
  rw [he]
  simp [weight,bitWeight]

theorem prob_fin {m : ℕ} (p : ℝ) (E : (Fin m → Bool) → Bool) :
    prob p E = bernProb p E := rfl

def assignmentEquiv {I J : Type*} (e : I ≃ J) : (I → Bool) ≃ (J → Bool) where
  toFun x j := x (e.symm j)
  invFun y i := y (e i)
  left_inv x := by funext i; simp
  right_inv y := by funext j; simp

theorem weight_equiv {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (p : ℝ) (x : I → Bool) : weight p (assignmentEquiv e x) = weight p x := by
  unfold weight
  exact Fintype.prod_equiv e.symm _ _ (fun j => rfl)

theorem prob_equiv {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : I ≃ J) (p : ℝ) (E : (I → Bool) → Bool) :
    prob p (fun y : J → Bool => E (fun i => y (e i))) = prob p E := by
  classical
  unfold prob
  rw [← Equiv.sum_comp (assignmentEquiv e)]
  apply sum_congr rfl
  intro x _
  have he : (fun i => assignmentEquiv e x (e i)) = x := by funext i; simp [assignmentEquiv]
  change (if E (fun i => assignmentEquiv e x (e i)) then weight p (assignmentEquiv e x) else 0) = _
  rw [he,weight_equiv]

theorem weight_product {I J : Type*} [Fintype I] [Fintype J]
    (p : ℝ) (x : I × J → Bool) :
    weight p x = ∏ i, weight p (fun j => x (i,j)) := by
  simp only [weight,Fintype.prod_prod_type]

theorem indicator_all {I : Type*} [Fintype I] (E : I → Bool) (w : I → ℝ) :
    (if (decide (∀ i, E i = true)) then ∏ i, w i else 0) =
      ∏ i, if E i then w i else 0 := by
  classical
  by_cases h : ∀ i, E i = true
  · simp [h]
  · have hz : ∃ i, E i = false := by simpa only [not_forall,Bool.not_eq_true] using h
    obtain ⟨i,hi⟩ := hz
    rw [if_neg (by simpa using h)]
    symm
    exact prod_eq_zero (mem_univ i) (by simp [hi])

/-- Disjoint blocks have independent acceptance events under product bias. -/
theorem prob_all_blocks {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (p : ℝ) (E : I → (J → Bool) → Bool) :
    prob p (fun x : I × J → Bool => decide (∀ i, E i (fun j => x (i,j)) = true)) =
      ∏ i, prob p (E i) := by
  classical
  unfold prob
  simp_rw [weight_product,indicator_all]
  rw [Fintype.sum_equiv (Equiv.curry I J Bool)
    (fun x : I × J → Bool => ∏ i, if E i (fun j => x (i,j)) then weight p (fun j => x (i,j)) else 0)
    (fun x : I → J → Bool => ∏ i, if E i (x i) then weight p (x i) else 0) (fun _ => rfl)]
  exact (Fintype.prod_sum (fun i : I => fun x : J → Bool => if E i x then weight p x else 0)).symm

theorem prob_all_copies {t m : ℕ} (p : ℝ) (E : (Fin m → Bool) → Bool) :
    prob p (fun x : Fin t × Fin m → Bool => decide (∀ i, E (fun j => x (i,j)) = true)) =
      bernProb p E ^ t := by
  convert (prob_all_blocks p (fun _ : Fin t => E)) using 1
  · congr 1
    funext x
    apply Bool.eq_iff_iff.mpr
    simp
  · simp only [prob_fin,prod_const,card_univ,Fintype.card_fin]

end SemAC02.P2MBernoulliProduct
end

section
-- Inlined Solutions.P2MFiniteProductPushforward

open Finset

namespace ProofComplexity.P2MFiniteProductPushforward

theorem prod_fiber_indicator {I A B : Type*} [Fintype I] [DecidableEq I] [DecidableEq B] (g : A → B)
    (w : I → A → ℝ) (x : I → A) (y : I → B) :
    (if (fun i => g (x i)) = y then ∏ i, w i (x i) else 0) =
      ∏ i, if g (x i) = y i then w i (x i) else 0 := by
  classical
  by_cases he : (fun i => g (x i)) = y
  · rw [if_pos he]
    apply prod_congr rfl
    intro i _
    rw [if_pos (congrFun he i)]
  · rw [if_neg he]
    obtain ⟨i,hi⟩ : ∃ i, g (x i) ≠ y i := by
      by_contra! h
      exact he (funext h)
    symm
    exact prod_eq_zero (mem_univ i) (if_neg hi)

theorem fiber_weight {I A B : Type*} [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq B] (g : A → B)
    (w : I → A → ℝ) (y : I → B) :
    (∑ x : I → A, if (fun i => g (x i)) = y then ∏ i, w i (x i) else 0) =
      ∏ i, ∑ a : A, if g a = y i then w i a else 0 := by
  classical
  simp_rw [prod_fiber_indicator]
  exact (Fintype.prod_sum (fun i : I => fun a : A => if g a = y i then w i a else 0)).symm

/-- Independent finite coordinates remain independent under a coordinatewise map. -/
theorem sum_pushforward {I A B : Type*} [Fintype I] [DecidableEq I] [Fintype A] [Fintype B] [DecidableEq B]
    (g : A → B) (w : I → A → ℝ) (F : (I → B) → ℝ) :
    (∑ x : I → A, (∏ i, w i (x i))*F (fun i => g (x i))) =
      ∑ y : I → B, (∏ i, ∑ a : A, if g a = y i then w i a else 0)*F y := by
  classical
  calc
    _ = ∑ x : I → A, ∑ y : I → B,
        (if (fun i => g (x i)) = y then ∏ i, w i (x i) else 0)*F y := by
      apply sum_congr rfl
      intro x _
      simp only [ite_mul,zero_mul]
      simp
    _ = ∑ y : I → B, ∑ x : I → A,
        (if (fun i => g (x i)) = y then ∏ i, w i (x i) else 0)*F y := sum_comm
    _ = ∑ y : I → B,
        (∑ x : I → A, if (fun i => g (x i)) = y then ∏ i, w i (x i) else 0)*F y := by
      simp only [sum_mul]
    _ = _ := by simp only [fiber_weight]

end ProofComplexity.P2MFiniteProductPushforward
end

section
-- Inlined Solutions.P2MBernoulliProductBounds

set_option maxHeartbeats 2000000

namespace SemAC02.P2MBernoulliProductBounds

open Finset P2MBernoulliAlgebra P2MBernoulliProduct

variable {I : Type} [Fintype I] [DecidableEq I]

 theorem nonneg (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (E : (I → Bool) → Bool) : 0 ≤ prob p E := by
  unfold prob
  apply sum_nonneg
  intro x hx
  split_ifs
  · exact weight_nonneg hp hp1 x
  · rfl

 theorem mono (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (E F : (I → Bool) → Bool)
    (h : ∀ x, E x=true → F x=true) : prob p E ≤ prob p F := by
  unfold prob
  apply sum_le_sum
  intro x hx
  cases he : E x
  · simp only [he,Bool.false_eq_true,↓reduceIte]
    split_ifs
    · exact weight_nonneg hp hp1 x
    · rfl
  · simp only [he,h x he,↓reduceIte,le_refl]

 theorem le_one (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (E : (I → Bool) → Bool) : prob p E ≤ 1 := by
  have hh := mono p hp hp1 E (fun _ => true) (fun _ _ => rfl)
  simpa only [prob,↓reduceIte,weight_sum] using hh

 theorem union_bound {J : Type} (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset J)
    (E : (I → Bool) → Bool) (F : J → (I → Bool) → Bool)
    (h : ∀ x, E x=true → ∃ j∈S, F j x=true) : prob p E ≤ ∑ j∈S, prob p (F j) := by
  classical
  unfold prob
  rw [sum_comm]
  apply sum_le_sum
  intro x hx
  cases he : E x
  · simp only [he,Bool.false_eq_true,↓reduceIte]
    apply sum_nonneg
    intro j hj
    split_ifs
    · exact weight_nonneg hp hp1 x
    · rfl
  · obtain ⟨j,hj,hF⟩ := h x he
    simp only [he,↓reduceIte]
    apply le_trans _ (single_le_sum (fun k hk => ?_) hj)
    · simpa only [hF,↓reduceIte] using (le_refl (weight p x))
    · split_ifs
      · exact weight_nonneg hp hp1 x
      · rfl

 theorem positive_exists (p : ℝ) (E : (I → Bool) → Bool) (h : 0 < prob p E) : ∃ x, E x=true := by
  classical
  by_contra! hh
  have hz : prob p E=0 := by unfold prob; simp [hh]
  linarith

 theorem independent (p : ℝ) (E : I → Bool → Bool) :
    prob p (fun x : I → Bool => decide (∀ i, E i (x i)=true))=
      ∏ i, ∑ b : Bool, if E i b then bitWeight p b else 0 := by
  classical
  unfold prob
  simp_rw [weight,indicator_all]
  exact (Fintype.prod_sum (fun i : I => fun b : Bool => if E i b then bitWeight p b else 0)).symm

 theorem all_on_subset (p : ℝ) (S : Finset I) :
    prob p (fun x : I → Bool => decide (∀ i∈S, x i=true))=p^S.card := by
  classical
  have hh := independent p (fun i b => decide (i∈S → b=true))
  have he (i : I) : (∑ b : Bool, if decide (i∈S → b=true) then bitWeight p b else 0)=if i∈S then p else 1 := by
    by_cases hi : i∈S <;> simp [hi,bitWeight]
  simp only [he] at hh
  rw [←prod_filter] at hh
  have hf : (univ : Finset I).filter (· ∈ S)=S := by ext i; simp
  rw [hf,prod_const] at hh
  have hEvent : (fun x : I → Bool => decide (∀ i∈S, x i=true))=
      (fun x => decide (∀ i, decide (i∈S → x i=true)=true)) := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
  rw [hEvent]
  exact hh

 theorem transform_blocks {J : Type} [Fintype J] [DecidableEq J]
    (p : ℝ) (g : (J → Bool) → Bool) (E : (I → Bool) → Bool) :
    prob p (fun x : I×J → Bool => E (fun i => g (fun j => x (i,j))))=
      prob (prob p g) E := by
  classical
  let q := prob p g
  have hf (b : Bool) : (∑ z : J → Bool, if g z=b then weight p z else 0)=bitWeight q b := by
    cases b
    · have hh := prob_complement p g
      simpa [prob,bitWeight,q] using hh
    · simp [bitWeight,q,prob]
  have hh := ProofComplexity.P2MFiniteProductPushforward.sum_pushforward g (fun _ : I => weight p)
    (fun x : I → Bool => if E x then (1 : ℝ) else 0)
  have he := Fintype.sum_equiv (Equiv.curry I J Bool)
    (fun x : I×J → Bool => weight p x*(if E (fun i => g (fun j => x (i,j))) then (1 : ℝ) else 0))
    (fun x : I → J → Bool => (∏ i,weight p (x i))*(if E (fun i => g (x i)) then (1 : ℝ) else 0))
    (fun x => by rw [weight_product]; rfl)
  change (∑ x : I×J → Bool, if E (fun i => g (fun j => x (i,j))) then weight p x else 0)=
    ∑ x : I → Bool, if E x then weight q x else 0
  simp only [mul_ite,mul_one,mul_zero] at he hh
  rw [he,hh]
  simp_rw [hf]
  rfl

end SemAC02.P2MBernoulliProductBounds
end

section
-- Inlined Solutions.P2MBernoulliPatternProbability

set_option maxHeartbeats 2000000

namespace SemAC02.P2MBernoulliPatternProbability

open Finset P2MBernoulliAlgebra P2MBernoulliProduct P2MBernoulliProductBounds

variable {I : Type} [Fintype I] [DecidableEq I]

 theorem pattern (p : ℝ) (S : Finset I) (β : I → Bool) :
    prob p (fun x : I → Bool => decide (∀ i∈S, x i=β i))=∏ i∈S, bitWeight p (β i) := by
  classical
  have hh := independent p (fun i b => decide (i∈S → b=β i))
  have he (i : I) : (∑ b : Bool, if decide (i∈S → b=β i) then bitWeight p b else 0)=
      if i∈S then bitWeight p (β i) else 1 := by
    by_cases hi : i∈S <;> cases hb : β i <;> simp [hi,hb,bitWeight]
  simp only [he] at hh
  rw [←prod_filter] at hh
  have hf : (univ : Finset I).filter (· ∈ S)=S := by ext i; simp
  rw [hf] at hh
  have hEvent : (fun x : I → Bool => decide (∀ i∈S, x i=β i))=
      (fun x => decide (∀ i, decide (i∈S → x i=β i)=true)) := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
  rw [hEvent]
  exact hh

 theorem disjoint_union {J : Type} (p : ℝ) (S : Finset J)
    (E : (I → Bool) → Bool) (F : J → (I → Bool) → Bool)
    (hcover : ∀ x, E x=true ↔ ∃ j∈S, F j x=true)
    (hdisj : ∀ x, ∀ j∈S, ∀ k∈S, F j x=true → F k x=true → j=k) :
    prob p E=∑ j∈S, prob p (F j) := by
  classical
  unfold prob
  rw [sum_comm]
  apply sum_congr rfl
  intro x hx
  by_cases he : E x=true
  · obtain ⟨j,hj,hF⟩ := (hcover x).mp he
    rw [if_pos he]
    symm
    rw [sum_eq_single j]
    · simp [hF]
    · intro k hk hkj
      have hn : F k x≠true := fun hf => hkj (hdisj x k hk j hj hf hF)
      simp [hn]
    · exact fun hn => (hn hj).elim
  · rw [if_neg he]
    symm
    apply sum_eq_zero
    intro j hj
    have hn : F j x≠true := fun hf => he ((hcover x).mpr ⟨j,hj,hf⟩)
    simp [hn]

 theorem one_pattern (p : ℝ) (S : Finset I) (j : I) (hj : j∈S) :
    prob p (fun x : I → Bool => decide (∀ i∈S, x i=decide (i=j)))=
      p*(1-p)^(S.card-1) := by
  classical
  rw [pattern,←mul_prod_erase S (fun i => bitWeight p (decide (i=j))) hj]
  have he : (∏ i∈S.erase j, bitWeight p (decide (i=j)))=(1-p)^(S.card-1) := by
    have hh : (∏ i∈S.erase j, bitWeight p (decide (i=j)))=∏ _i∈S.erase j, (1-p) := by
      apply prod_congr rfl
      intro i hi
      simp [bitWeight,(mem_erase.mp hi).1]
    rw [hh,prod_const,card_erase_of_mem hj]
  rw [he]
  simp [bitWeight]

 theorem exactly_one (p : ℝ) (S : Finset I) :
    prob p (fun x : I → Bool => decide ((S.filter (fun i => x i=true)).card=1))=
      (S.card : ℝ)*p*(1-p)^(S.card-1) := by
  classical
  let F := fun j (x : I → Bool) => decide (∀ i∈S, x i=decide (i=j))
  have hcover : ∀ x : I → Bool,
      decide ((S.filter (fun i => x i=true)).card=1)=true ↔ ∃ j∈S, F j x=true := by
    intro x
    simp only [decide_eq_true_eq]
    constructor
    · intro hc
      obtain ⟨j,hj⟩ := card_eq_one.mp hc
      have hjFilt : j∈S.filter (fun i => x i=true) := by rw [hj]; simp
      have hjS : j∈S := (mem_filter.mp hjFilt).1
      refine ⟨j,hjS,?_⟩
      apply decide_eq_true
      intro i hi
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      constructor
      · intro hxi
        have hm : i∈S.filter (fun a => x a=true) := mem_filter.mpr ⟨hi,hxi⟩
        rw [hj] at hm
        exact mem_singleton.mp hm
      · intro hij
        subst i
        exact (mem_filter.mp hjFilt).2
    · rintro ⟨j,hj,hF⟩
      have hF' : ∀ i∈S, x i=decide (i=j) := of_decide_eq_true hF
      have he : S.filter (fun i => x i=true)={j} := by
        ext i
        simp only [mem_filter,mem_singleton]
        constructor
        · rintro ⟨hi,hxi⟩
          have hh := hF' i hi
          rw [hxi] at hh
          exact of_decide_eq_true hh.symm
        · intro hij
          subst i
          exact ⟨hj,by simpa using hF' j hj⟩
      rw [he,card_singleton]
  have hdisj : ∀ x, ∀ j∈S, ∀ k∈S, F j x=true → F k x=true → j=k := by
    intro x j hj k hk hFj hFk
    have hJ := of_decide_eq_true hFj j hj
    have hK := of_decide_eq_true hFk j hj
    have hxj : x j=true := by simpa using hJ
    rw [hxj] at hK
    exact of_decide_eq_true hK.symm
  rw [disjoint_union p S _ F hcover hdisj]
  have he (j : I) (hj : j∈S) : prob p (F j)=p*(1-p)^(S.card-1) := one_pattern p S j hj
  rw [sum_congr rfl he,sum_const,nsmul_eq_mul]
  ring

end SemAC02.P2MBernoulliPatternProbability
end

section
-- Inlined Solutions.P2MBernoulliTail

set_option maxHeartbeats 2000000

open Finset SemAC02.P2MBernoulliAlgebra

namespace SemAC02.P2MBernoulliTail

def bitValue (b : Bool) : ℝ := if b then 1 else 0

theorem weight_eq_sum {m : ℕ} (x : Fin m → Bool) :
    (hammingWeight x : ℝ) = ∑ i, bitValue (x i) := by
  simp [hammingWeight,bitValue]

theorem exp_weight {m : ℕ} (θ : ℝ) (x : Fin m → Bool) :
    Real.exp (θ*(hammingWeight x : ℝ)) = ∏ i, Real.exp (θ*bitValue (x i)) := by
  rw [weight_eq_sum,mul_sum,Real.exp_sum]

theorem moment_formula {m : ℕ} (p θ : ℝ) :
    (∑ x : Fin m → Bool, weight p x*Real.exp (θ*(hammingWeight x : ℝ))) =
      (1-p+p*Real.exp θ)^m := by
  simp_rw [exp_weight,weight,← prod_mul_distrib]
  rw [← Fintype.prod_sum (fun _ : Fin m => fun b : Bool => bitWeight p b*Real.exp (θ*bitValue b))]
  simp [bitWeight,bitValue,add_comm]

theorem moment_markov {m : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) {θ : ℝ} (hθ : 0 ≤ θ)
    (t : ℝ) (E : (Fin m → Bool) → Bool)
    (hE : ∀ x, E x = true → t ≤ (hammingWeight x : ℝ)) :
    bernProb p E ≤ Real.exp (-θ*t)*(1-p+p*Real.exp θ)^m := by
  have hs : bernProb p E*Real.exp (θ*t) ≤ (1-p+p*Real.exp θ)^m := by
    rw [bernProb_eq_weight,sum_mul,← moment_formula]
    apply sum_le_sum
    intro x _
    cases he : E x
    · simp only [he,Bool.false_eq_true,↓reduceIte,zero_mul]
      exact mul_nonneg (weight_nonneg hp hp' x) (Real.exp_pos _).le
    · simp only [he,↓reduceIte]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (hE x he) hθ)) (weight_nonneg hp hp' x)
  calc
    _ = (bernProb p E*Real.exp (θ*t))*Real.exp (-θ*t) := by
      rw [mul_assoc,← Real.exp_add,show θ*t+(-θ*t) = 0 by ring,Real.exp_zero,mul_one]
    _ ≤ (1-p+p*Real.exp θ)^m*Real.exp (-θ*t) :=
      mul_le_mul_of_nonneg_right hs (Real.exp_pos _).le
    _ = _ := mul_comm _ _

theorem exp_quadratic_bound {θ : ℝ} (hθ : 0 ≤ θ) (hθ' : θ ≤ 1/2) :
    Real.exp θ ≤ 1+θ+2*θ^2 := by
  apply (Real.exp_bound_div_one_sub_of_interval hθ (by linarith : θ < 1)).trans
  apply (div_le_iff₀ (by linarith : 0 < 1-θ)).mpr
  nlinarith [mul_nonneg (sq_nonneg θ) (by linarith : 0 ≤ 1-2*θ)]

theorem moment_bound {m : ℕ} {p θ : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hθ : 0 ≤ θ) (hθ' : θ ≤ 1/2) :
    (1-p+p*Real.exp θ)^m ≤ Real.exp ((m : ℝ)*(p*θ+2*p*θ^2)) := by
  have hb : 1-p+p*Real.exp θ ≤ Real.exp (p*θ+2*p*θ^2) := by
    have he := mul_le_mul_of_nonneg_left (exp_quadratic_bound hθ hθ') hp
    linarith [Real.add_one_le_exp (p*θ+2*p*θ^2)]
  calc
    _ ≤ Real.exp (p*θ+2*p*θ^2)^m := pow_le_pow_left₀
      (add_nonneg (sub_nonneg.mpr hp') (mul_nonneg hp (Real.exp_pos _).le)) hb m
    _ = _ := (Real.exp_nat_mul _ _).symm

/-- A finite-sum Chernoff estimate; its constant suffices for the covering-gadget construction. -/
theorem upper_tail {m : ℕ} {p δ : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1/2)
    (hδ : 0 < δ) (hδ' : δ ≤ 1) (E : (Fin m → Bool) → Bool)
    (hE : ∀ x, E x = true → (p+δ)*(m : ℝ) ≤ (hammingWeight x : ℝ)) :
    bernProb p E ≤ Real.exp (-((m : ℝ)*δ^2/4)) := by
  let θ := δ/2
  have hθ : 0 ≤ θ := by dsimp [θ]; positivity
  have hθ' : θ ≤ 1/2 := by dsimp [θ]; linarith
  calc
    _ ≤ Real.exp (-θ*((p+δ)*(m : ℝ)))*(1-p+p*Real.exp θ)^m :=
      moment_markov hp (by linarith : p ≤ 1) hθ _ E hE
    _ ≤ Real.exp (-θ*((p+δ)*(m : ℝ)))*Real.exp ((m : ℝ)*(p*θ+2*p*θ^2)) :=
      mul_le_mul_of_nonneg_left (moment_bound hp (by linarith : p ≤ 1) hθ hθ') (Real.exp_pos _).le
    _ = Real.exp ((m : ℝ)*(2*p*θ^2-θ*δ)) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hsmall : 2*p*θ^2-θ*δ ≤ -δ^2/4 := by
        dsimp [θ]
        nlinarith [mul_nonneg (by linarith : 0 ≤ 1-2*p) (sq_nonneg δ)]
      have h := mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg m)
      nlinarith

theorem covering_tail {m : ℕ} {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1/2) :
    bernProb (1/2-ε)
      (fun x : Fin m → Bool => decide ((1/2-3*ε/4)*(m : ℝ) < (hammingWeight x : ℝ))) ≤
      Real.exp (-((m : ℝ)*ε^2/64)) := by
  have h := upper_tail (p := 1/2-ε) (δ := ε/4) (by linarith) (by linarith)
    (by positivity) (by linarith) (fun x : Fin m → Bool =>
      decide ((1/2-3*ε/4)*(m : ℝ) < (hammingWeight x : ℝ))) (by
        intro x hx
        have ht := of_decide_eq_true hx
        nlinarith)
  convert h using 1 <;> congr 1 <;> ring

end SemAC02.P2MBernoulliTail
end

section
-- Inlined Solutions.P2MBernoulliMultiplicativeTail

set_option maxHeartbeats 2000000

namespace SemAC02.P2MBernoulliMultiplicativeTail

open Finset P2MBernoulliAlgebra P2MBernoulliTail

 theorem poisson_moment {m : ℕ} (p θ : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (1-p+p*Real.exp θ)^m ≤ Real.exp ((m : ℝ)*p*(Real.exp θ-1)) := by
  have hb : 1-p+p*Real.exp θ ≤ Real.exp (p*(Real.exp θ-1)) := by
    have hh := Real.add_one_le_exp (p*(Real.exp θ-1))
    nlinarith
  have hbase : 0 ≤ 1-p+p*Real.exp θ := by positivity
  calc
    _ ≤ Real.exp (p*(Real.exp θ-1))^m := pow_le_pow_left₀ hbase hb m
    _ = _ := by rw [←Real.exp_nat_mul]; congr 1; ring

 theorem upper_twice {m : ℕ} (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (E : (Fin m → Bool) → Bool) (hE : ∀ x, E x=true → 2*p*m ≤ (hammingWeight x : ℝ)) :
    bernProb p E ≤ Real.exp (-((m : ℝ)*p)/3) := by
  have hθ : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hh := (moment_markov hp hp1 hθ (2*p*m) E hE).trans
    (mul_le_mul_of_nonneg_left (poisson_moment p (Real.log 2) hp hp1) (Real.exp_pos _).le)
  rw [←Real.exp_add,Real.exp_log (by norm_num : (0 : ℝ)<2)] at hh
  apply hh.trans
  apply Real.exp_le_exp.mpr
  have hl : (2/3 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hm : (0 : ℝ) ≤ (m : ℝ)*p := by positivity
  nlinarith [mul_nonneg hm (sub_nonneg.mpr hl)]

 theorem moment_markov_lower {m : ℕ} (p θ : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hθ : θ ≤ 0)
    (t : ℝ) (E : (Fin m → Bool) → Bool) (hE : ∀ x, E x=true → (hammingWeight x : ℝ) ≤ t) :
    bernProb p E ≤ Real.exp (-θ*t)*(1-p+p*Real.exp θ)^m := by
  have hs : bernProb p E*Real.exp (θ*t) ≤ (1-p+p*Real.exp θ)^m := by
    rw [bernProb_eq_weight,sum_mul,←moment_formula]
    apply sum_le_sum
    intro x hx
    cases he : E x
    · simp only [he,Bool.false_eq_true,↓reduceIte,zero_mul]
      exact mul_nonneg (weight_nonneg hp hp1 x) (Real.exp_pos _).le
    · simp only [he,↓reduceIte]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonpos_left (hE x he) hθ)) (weight_nonneg hp hp1 x)
  calc
    _ = (bernProb p E*Real.exp (θ*t))*Real.exp (-θ*t) := by
      rw [mul_assoc,←Real.exp_add,show θ*t+(-θ*t)=0 by ring,Real.exp_zero,mul_one]
    _ ≤ (1-p+p*Real.exp θ)^m*Real.exp (-θ*t) := mul_le_mul_of_nonneg_right hs (Real.exp_pos _).le
    _ = _ := mul_comm _ _

 theorem lower_third {m : ℕ} (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (E : (Fin m → Bool) → Bool) (hE : ∀ x, E x=true → (hammingWeight x : ℝ) ≤ (m : ℝ)*p/3) :
    bernProb p E ≤ Real.exp (-2*((m : ℝ)*p)/9) := by
  have hθ : -Real.log 2 ≤ 0 := neg_nonpos.mpr (Real.log_nonneg (by norm_num))
  have hh := (moment_markov_lower p (-Real.log 2) hp hp1 hθ ((m : ℝ)*p/3) E hE).trans
    (mul_le_mul_of_nonneg_left (poisson_moment p (-Real.log 2) hp hp1) (Real.exp_pos _).le)
  have hexp : Real.exp (-Real.log 2)=(1/2 : ℝ) := by rw [Real.exp_neg,Real.exp_log (by norm_num : (0 : ℝ)<2)]; norm_num
  rw [←Real.exp_add,hexp] at hh
  apply hh.trans
  apply Real.exp_le_exp.mpr
  have hl : Real.log 2 ≤ (5/6 : ℝ) := by linarith [Real.log_two_lt_d9]
  have hm : (0 : ℝ) ≤ (m : ℝ)*p := by positivity
  nlinarith [mul_nonneg hm (sub_nonneg.mpr hl)]

end SemAC02.P2MBernoulliMultiplicativeTail
end

section
-- Inlined Solutions.P2MRandomGraphFixedBoundary

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MRandomGraphFixedBoundary

open Finset P2MBernoulliAlgebra P2MBernoulliProduct P2MBernoulliProductBounds

noncomputable def graph (n : ℕ) (x : Fin n×Fin (2*n) → Bool) :
    PCNonBool.BipGraph (Fin (2*n)) (Fin n) where
  Adj u v := x (v,u)=true

noncomputable def oneNeighbor {I : Type} [DecidableEq I] (S : Finset I) (x : I → Bool) : Bool :=
  decide ((S.filter (fun i => x i=true)).card=1)

 theorem one_neighbor_lower {I : Type} [Fintype I] [DecidableEq I]
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset I) (hSmall : (S.card : ℝ)*p ≤ 1/4) :
    3/4*(S.card : ℝ)*p ≤ prob p (oneNeighbor S) := by
  rw [show oneNeighbor S=(fun x : I → Bool => decide ((S.filter (fun i => x i=true)).card=1)) from rfl,
    P2MBernoulliPatternProbability.exactly_one]
  have hh := one_add_mul_le_pow (a := -p) (by linarith : -2 ≤ -p) (S.card-1)
  have hc : ((S.card-1 : ℕ) : ℝ) ≤ S.card := by exact_mod_cast Nat.sub_le S.card 1
  have hpow : (3/4 : ℝ) ≤ (1-p)^(S.card-1) := by
    have hh' : 1-((S.card-1 : ℕ) : ℝ)*p ≤ (1-p)^(S.card-1) := by simpa only [mul_neg,←sub_eq_add_neg] using hh
    nlinarith [mul_le_mul_of_nonneg_right hc hp]
  have hmult := mul_le_mul_of_nonneg_left hpow (show 0 ≤ (S.card : ℝ)*p by positivity)
  nlinarith

 theorem boundary_card (n : ℕ) (S : Finset (Fin (2*n))) (x : Fin n×Fin (2*n) → Bool) :
    (PCNonBool.boundaryOn (graph n x) univ S).card=
      hammingWeight (fun v : Fin n => oneNeighbor S (fun u => x (v,u))) := by
  unfold PCNonBool.boundaryOn hammingWeight
  congr 1
  apply filter_congr
  intro v hv
  simp only [graph,oneNeighbor,decide_eq_true_eq]
  apply Iff.of_eq
  congr 1

 theorem failure_bound (n Δ : ℕ) (hn : 1 ≤ n) (hΔ : 1 ≤ Δ) (hΔn : Δ ≤ n)
    (S : Finset (Fin (2*n))) (hS : (S.card : ℝ)*(Δ : ℝ)/n ≤ 1/4) :
    prob ((Δ : ℝ)/n) (fun x : Fin n×Fin (2*n) → Bool =>
      decide (((PCNonBool.boundaryOn (graph n x) univ S).card : ℝ)<(S.card : ℝ)*Δ/4)) ≤
        Real.exp (-((S.card : ℝ)*Δ)/6) := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast (show 0 < n by omega)
  let p := (Δ : ℝ)/n
  let q := prob p (oneNeighbor S)
  let E := fun z : Fin n → Bool => decide ((hammingWeight z : ℝ)<(S.card : ℝ)*Δ/4)
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hp1 : p ≤ 1 := (div_le_one hnR).mpr (by exact_mod_cast hΔn)
  have hq : 0 ≤ q := nonneg p hp hp1 _
  have hq1 : q ≤ 1 := le_one p hp hp1 _
  have hSmall : (S.card : ℝ)*p ≤ 1/4 := by simpa only [p,mul_div_assoc] using hS
  have hqL : 3/4*(S.card : ℝ)*p ≤ q := one_neighbor_lower p hp hp1 S hSmall
  have hMu : 3/4*(S.card : ℝ)*Δ ≤ (n : ℝ)*q := by
    have hh := mul_le_mul_of_nonneg_left hqL hnR.le
    have he : (n : ℝ)*(3/4*(S.card : ℝ)*p)=3/4*(S.card : ℝ)*Δ := by dsimp [p]; field_simp
    rwa [he] at hh
  have he : prob p (fun x : Fin n×Fin (2*n) → Bool =>
      decide (((PCNonBool.boundaryOn (graph n x) univ S).card : ℝ)<(S.card : ℝ)*Δ/4))=bernProb q E := by
    have hh := transform_blocks p (oneNeighbor S) E
    convert hh using 1
    congr 1
    funext x
    rw [boundary_card]
    rfl
  rw [he]
  have hh := P2MBernoulliMultiplicativeTail.lower_third q hq hq1 E (by
    intro z hz
    have ht := of_decide_eq_true hz
    linarith)
  apply hh.trans
  apply Real.exp_le_exp.mpr
  linarith

end SemAC02.Supplement.P2MRandomGraphFixedBoundary
end

section
-- Inlined Solutions.P2MRandomGraphBoundaryExpansion

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MRandomGraphBoundaryExpansion

open Finset P2MBernoulliAlgebra P2MBernoulliProduct P2MBernoulliProductBounds P2MRandomGraphFixedBoundary

 theorem single_size (n Δ s t : ℕ) (hn : 1 ≤ n) (hΔ : 1 ≤ Δ) (hΔn : Δ ≤ n)
    (hBudget : (4 : ℝ)*Δ*s ≤ n) (ht : t ≤ s) :
    prob ((Δ : ℝ)/n) (fun x : Fin n×Fin (2*n) → Bool => decide (∃ S : Finset (Fin (2*n)),
      S.card=t ∧ ((PCNonBool.boundaryOn (graph n x) univ S).card : ℝ)<(t : ℝ)*Δ/4)) ≤
      ((2*n).choose t : ℝ)*Real.exp (-((t : ℝ)*Δ)/6) := by
  classical
  have hnR : (0 : ℝ)<n := by exact_mod_cast (show 0 < n by omega)
  have hp0 : (0 : ℝ) ≤ (Δ : ℝ)/n := by positivity
  have hp1 : (Δ : ℝ)/n ≤ 1 := (div_le_one hnR).mpr (by exact_mod_cast hΔn)
  let A := (univ : Finset (Fin (2*n))).powersetCard t
  have hc : A.card=(2*n).choose t := by simp [A]
  have hb := union_bound ((Δ : ℝ)/n) hp0 hp1 A
    (fun x : Fin n×Fin (2*n) → Bool => decide (∃ S : Finset (Fin (2*n)),
      S.card=t ∧ ((PCNonBool.boundaryOn (graph n x) univ S).card : ℝ)<(t : ℝ)*Δ/4))
    (fun S x => decide (((PCNonBool.boundaryOn (graph n x) univ S).card : ℝ)<(S.card : ℝ)*Δ/4)) (by
      intro x hx
      obtain ⟨S,hSc,hbad⟩ := of_decide_eq_true hx
      exact ⟨S,by simp [A,hSc],by simpa only [hSc] using (decide_eq_true hbad)⟩)
  apply hb.trans
  calc
    _ ≤ ∑ _S∈A, Real.exp (-((t : ℝ)*Δ)/6) := by
      apply sum_le_sum
      intro S hS
      have hSc : S.card=t := (mem_powersetCard.mp hS).2
      have hSmall : (S.card : ℝ)*(Δ : ℝ)/n ≤ 1/4 := by
        rw [hSc]
        apply (div_le_iff₀ hnR).mpr
        have htR : (t : ℝ) ≤ s := by exact_mod_cast ht
        nlinarith [mul_le_mul_of_nonneg_left htR (Nat.cast_nonneg (α:=ℝ) Δ)]
      simpa only [hSc] using failure_bound n Δ hn hΔ hΔn S hSmall
    _ = _ := by rw [sum_const,nsmul_eq_mul,hc]

 theorem geometric_bound (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (s : ℕ) :
    (∑ j∈range s, q^(j+1)) ≤ q/(1-q) := by
  have hp : (∑ j∈range s, q^j) ≤ 1/(1-q) := by
    apply (le_div_iff₀ (by linarith : 0 < 1-q)).mpr
    have he := geom_sum_mul q s
    have hpow := pow_nonneg hq0 s
    nlinarith
  calc
    _ = q*(∑ j∈range s, q^j) := by rw [mul_sum]; simp only [pow_succ',mul_comm]
    _ ≤ q*(1/(1-q)) := mul_le_mul_of_nonneg_left hp hq0
    _ = _ := by ring

 theorem failure_probability (n Δ s : ℕ) (hn : 1 ≤ n) (hΔ : 1 ≤ Δ) (hΔn : Δ ≤ n)
    (hBudget : (4 : ℝ)*Δ*s ≤ n) (hSmall : (2*(n : ℝ))*Real.exp (-(Δ : ℝ)/6)<1) :
    prob ((Δ : ℝ)/n) (fun x : Fin n×Fin (2*n) → Bool => decide (∃ S : Finset (Fin (2*n)),
      S.Nonempty ∧ S.card ≤ s ∧ ((PCNonBool.boundaryOn (graph n x) univ S).card : ℝ)<(S.card : ℝ)*Δ/4)) ≤
        ((2*(n : ℝ))*Real.exp (-(Δ : ℝ)/6))/(1-(2*(n : ℝ))*Real.exp (-(Δ : ℝ)/6)) := by
  classical
  have hnR : (0 : ℝ)<n := by exact_mod_cast (show 0 < n by omega)
  have hp0 : (0 : ℝ) ≤ (Δ : ℝ)/n := by positivity
  have hp1 : (Δ : ℝ)/n ≤ 1 := (div_le_one hnR).mpr (by exact_mod_cast hΔn)
  have hb := union_bound ((Δ : ℝ)/n) hp0 hp1 (range s)
    (fun x : Fin n×Fin (2*n) → Bool => decide (∃ S : Finset (Fin (2*n)),
      S.Nonempty ∧ S.card ≤ s ∧ ((PCNonBool.boundaryOn (graph n x) univ S).card : ℝ)<(S.card : ℝ)*Δ/4))
    (fun j x => decide (∃ S : Finset (Fin (2*n)), S.card=j+1 ∧
      ((PCNonBool.boundaryOn (graph n x) univ S).card : ℝ)<((j+1 : ℕ) : ℝ)*Δ/4)) (by
      intro x hx
      obtain ⟨S,hS,hSs,hbad⟩ := of_decide_eq_true hx
      have hSc := card_pos.mpr hS
      refine ⟨S.card-1,mem_range.mpr (by omega),?_⟩
      apply decide_eq_true
      refine ⟨S,by omega,?_⟩
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ S.card)] using hbad)
  apply hb.trans
  apply le_trans _ (geometric_bound ((2*(n : ℝ))*Real.exp (-(Δ : ℝ)/6)) (by positivity) hSmall s)
  apply sum_le_sum
  intro j hj
  have hjs : j+1 ≤ s := by have hh := mem_range.mp hj; omega
  apply (single_size n Δ s (j+1) hn hΔ hΔn hBudget hjs).trans
  have hchoose : ((2*n).choose (j+1) : ℝ) ≤ (2*(n : ℝ))^(j+1) := by
    exact_mod_cast Nat.choose_le_pow (2*n) (j+1)
  calc
    _ ≤ (2*(n : ℝ))^(j+1)*Real.exp (-(((j+1 : ℕ) : ℝ)*Δ)/6) :=
      mul_le_mul_of_nonneg_right hchoose (Real.exp_pos _).le
    _ = _ := by
      conv_rhs => rw [mul_pow,←Real.exp_nat_mul]
      congr 1
      congr 1
      push_cast
      ring

end SemAC02.Supplement.P2MRandomGraphBoundaryExpansion
end

section
-- Inlined Solutions.P2MBernoulliCoordinates

set_option maxHeartbeats 1000000

namespace SemAC02.P2MBernoulliCoordinates

open P2MBernoulliAlgebra P2MBernoulliProduct P2MBernoulliProductBounds

 theorem bit_probability {J : Type} [Fintype J] [DecidableEq J] (p : ℝ) (j : J) :
    prob p (fun x : J → Bool => x j)=p := by
  have hh := all_on_subset p ({j} : Finset J)
  simpa using hh

 theorem marginal {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (p : ℝ) (j : J) (E : (I → Bool) → Bool) :
    prob p (fun x : I×J → Bool => E (fun i => x (i,j)))=prob p E := by
  have hh := transform_blocks p (fun z : J → Bool => z j) E
  rwa [bit_probability] at hh

 theorem other_marginal {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (p : ℝ) (i : I) (E : (J → Bool) → Bool) :
    prob p (fun x : I×J → Bool => E (fun j => x (i,j)))=prob p E := by
  have hh := marginal p i E
  have he := prob_equiv (Equiv.prodComm J I) p
    (fun x : J×I → Bool => E (fun j => x (j,i)))
  exact he.trans hh

end SemAC02.P2MBernoulliCoordinates
end

section
-- Inlined Solutions.P2MRandomGraphDegreeBounds

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MRandomGraphDegreeBounds

open Finset P2MBernoulliAlgebra P2MBernoulliProduct P2MBernoulliProductBounds P2MRandomGraphFixedBoundary

 theorem pigeon_tail (n Δ : ℕ) (hn : 1 ≤ n) (hΔn : Δ ≤ n) (u : Fin (2*n)) :
    prob ((Δ : ℝ)/n) (fun x : Fin n×Fin (2*n) → Bool =>
      decide (2*Δ<(PCNonBool.nbrOn (graph n x) univ u).card)) ≤ Real.exp (-(Δ : ℝ)/3) := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast (show 0 < n by omega)
  let p := (Δ : ℝ)/n
  let E := fun z : Fin n → Bool => decide (2*Δ<hammingWeight z)
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hp1 : p ≤ 1 := (div_le_one hnR).mpr (by exact_mod_cast hΔn)
  have hmean : (n : ℝ)*p=Δ := by dsimp [p]; field_simp
  change prob p (fun x : Fin n×Fin (2*n) → Bool => E (fun v => x (v,u))) ≤ _
  rw [P2MBernoulliCoordinates.marginal,prob_fin]
  have hb := P2MBernoulliMultiplicativeTail.upper_twice p hp0 hp1 E (by
    intro z hz
    have ht : (2 : ℝ)*Δ<(hammingWeight z : ℝ) := by exact_mod_cast of_decide_eq_true hz
    have he : 2*p*(n : ℝ)=2*Δ := by nlinarith [hmean]
    rw [he]
    exact ht.le)
  rwa [hmean] at hb

 theorem hole_tail (n Δ : ℕ) (hn : 1 ≤ n) (hΔn : Δ ≤ n) (v : Fin n) :
    prob ((Δ : ℝ)/n) (fun x : Fin n×Fin (2*n) → Bool =>
      decide (4*Δ<(univ.filter (fun u => (graph n x).Adj u v)).card)) ≤ Real.exp (-(2*(Δ : ℝ))/3) := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast (show 0 < n by omega)
  let p := (Δ : ℝ)/n
  let E := fun z : Fin (2*n) → Bool => decide (4*Δ<hammingWeight z)
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hp1 : p ≤ 1 := (div_le_one hnR).mpr (by exact_mod_cast hΔn)
  have hmean : ((2*n : ℕ) : ℝ)*p=2*Δ := by push_cast; dsimp [p]; field_simp
  change prob p (fun x : Fin n×Fin (2*n) → Bool => E (fun u => x (v,u))) ≤ _
  rw [P2MBernoulliCoordinates.other_marginal,prob_fin]
  have hb := P2MBernoulliMultiplicativeTail.upper_twice p hp0 hp1 E (by
    intro z hz
    have ht : (4 : ℝ)*Δ<(hammingWeight z : ℝ) := by exact_mod_cast of_decide_eq_true hz
    have he : 2*p*((2*n : ℕ) : ℝ)=4*Δ := by nlinarith [hmean]
    rw [he]
    exact ht.le)
  rwa [hmean] at hb

 theorem pigeons_failure (n Δ : ℕ) (hn : 1 ≤ n) (hΔn : Δ ≤ n) :
    prob ((Δ : ℝ)/n) (fun x : Fin n×Fin (2*n) → Bool =>
      decide (∃ u, 2*Δ<(PCNonBool.nbrOn (graph n x) univ u).card)) ≤
        (2*(n : ℝ))*Real.exp (-(Δ : ℝ)/3) := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast (show 0 < n by omega)
  have hb := union_bound ((Δ : ℝ)/n) (by positivity) ((div_le_one hnR).mpr (by exact_mod_cast hΔn))
    (univ : Finset (Fin (2*n)))
    (fun x : Fin n×Fin (2*n) → Bool => decide (∃ u, 2*Δ<(PCNonBool.nbrOn (graph n x) univ u).card))
    (fun u x => decide (2*Δ<(PCNonBool.nbrOn (graph n x) univ u).card)) (by
      intro x hx
      obtain ⟨u,hu⟩ := of_decide_eq_true hx
      exact ⟨u,mem_univ _,decide_eq_true hu⟩)
  apply hb.trans
  calc
    _ ≤ ∑ _u : Fin (2*n), Real.exp (-(Δ : ℝ)/3) := sum_le_sum (fun u hu => pigeon_tail n Δ hn hΔn u)
    _ = _ := by simp

 theorem holes_failure (n Δ : ℕ) (hn : 1 ≤ n) (hΔn : Δ ≤ n) :
    prob ((Δ : ℝ)/n) (fun x : Fin n×Fin (2*n) → Bool =>
      decide (∃ v, 4*Δ<(univ.filter (fun u => (graph n x).Adj u v)).card)) ≤
        (n : ℝ)*Real.exp (-(2*(Δ : ℝ))/3) := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast (show 0 < n by omega)
  have hb := union_bound ((Δ : ℝ)/n) (by positivity) ((div_le_one hnR).mpr (by exact_mod_cast hΔn))
    (univ : Finset (Fin n))
    (fun x : Fin n×Fin (2*n) → Bool => decide (∃ v, 4*Δ<(univ.filter (fun u => (graph n x).Adj u v)).card))
    (fun v x => decide (4*Δ<(univ.filter (fun u => (graph n x).Adj u v)).card)) (by
      intro x hx
      obtain ⟨v,hv⟩ := of_decide_eq_true hx
      exact ⟨v,mem_univ _,decide_eq_true hv⟩)
  apply hb.trans
  calc
    _ ≤ ∑ _v : Fin n, Real.exp (-(2*(Δ : ℝ))/3) := sum_le_sum (fun v hv => hole_tail n Δ hn hΔn v)
    _ = _ := by simp

end SemAC02.Supplement.P2MRandomGraphDegreeBounds
end

section
-- Inlined Solutions.P2MGraphPHPParameters

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MGraphPHPParameters

noncomputable def degree (n Δ : ℕ) : ℕ := ⌊(n : ℝ)/(4096*Δ)⌋₊
noncomputable def supportSize (n Δ : ℕ) : ℕ := ⌊(n : ℝ)/(4*Δ)⌋₊

 theorem finite_data (n Δ : ℕ) (hn : 128 ≤ n) (hΔ : 1 ≤ Δ)
    (hlarge : 32768*(Δ : ℝ)^2 ≤ n) :
    Δ ≤ n ∧ 1 ≤ degree n Δ ∧ 2*Δ ≤ degree n Δ ∧ 6*degree n Δ ≤ n ∧
      1 ≤ supportSize n Δ ∧ ((6*degree n Δ : ℕ) : ℝ)+2 ≤ (Δ : ℝ)*(supportSize n Δ)/8 ∧
      (n : ℝ)/(8192*Δ) ≤ degree n Δ ∧ (degree n Δ : ℝ)/n ≤ 1/64 := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast (show 0 < n by omega)
  have hΔR : (0 : ℝ)<Δ := by exact_mod_cast (show 0 < Δ by omega)
  have hΔ1 : (1 : ℝ) ≤ Δ := by exact_mod_cast hΔ
  have hn128 : (128 : ℝ) ≤ n := by exact_mod_cast hn
  have hΔSmall : (Δ : ℝ) ≤ (n : ℝ)/128 := by nlinarith [sq_nonneg ((Δ : ℝ)-1)]
  have hDiv : 4*(Δ : ℝ) ≤ (n : ℝ)/(8192*Δ) :=
    (le_div_iff₀ (by positivity : (0 : ℝ)<8192*Δ)).mpr (by nlinarith)
  have hkU : (degree n Δ : ℝ) ≤ (n : ℝ)/(4096*Δ) := Nat.floor_le (by positivity)
  have hkf : (n : ℝ)/(4096*Δ)-1 < (degree n Δ : ℝ) := Nat.sub_one_lt_floor _
  have he : (n : ℝ)/(4096*Δ)=2*((n : ℝ)/(8192*Δ)) := by ring
  have hkL : (n : ℝ)/(8192*Δ) ≤ degree n Δ := by rw [he] at hkf; nlinarith
  have hk2Δ : 2*Δ ≤ degree n Δ := by
    have hh : (2 : ℝ)*Δ ≤ degree n Δ := by linarith
    exact_mod_cast hh
  have hk1 : 1 ≤ degree n Δ := by omega
  have hkMult := (le_div_iff₀ (show (0 : ℝ)<4096*Δ by positivity)).mp hkU
  have hΔk : (degree n Δ : ℝ) ≤ (Δ : ℝ)*(degree n Δ : ℝ) := by
    nlinarith [mul_nonneg (show 0 ≤ (Δ : ℝ)-1 by linarith) (Nat.cast_nonneg (α:=ℝ) (degree n Δ))]
  have hkUn : (degree n Δ : ℝ) ≤ (n : ℝ)/4096 := by nlinarith
  have hk6 : 6*degree n Δ ≤ n := by
    have hh : (6 : ℝ)*(degree n Δ : ℝ) ≤ n := by nlinarith
    exact_mod_cast hh
  have hsL : (n : ℝ)/4-Δ ≤ (Δ : ℝ)*supportSize n Δ := by
    have hf : (n : ℝ)/(4*Δ)-1 < (supportSize n Δ : ℝ) := Nat.sub_one_lt_floor _
    have hh := mul_lt_mul_of_pos_left hf hΔR
    have he : (Δ : ℝ)*((n : ℝ)/(4*Δ)-1)=(n : ℝ)/4-Δ := by field_simp <;> ring
    rw [he] at hh
    exact hh.le
  have hbudget : ((6*degree n Δ : ℕ) : ℝ)+2 ≤ (Δ : ℝ)*(supportSize n Δ)/8 := by
    push_cast
    nlinarith
  have hs1 : 1 ≤ supportSize n Δ := by
    by_contra hh
    have hz : supportSize n Δ=0 := by omega
    rw [hz,Nat.cast_zero,mul_zero,zero_div] at hbudget
    have hk0 := Nat.cast_nonneg (α:=ℝ) (6*degree n Δ)
    linarith
  have hDn : Δ ≤ n := by
    have hh : (Δ : ℝ) ≤ n := by linarith
    exact_mod_cast hh
  have hp : (degree n Δ : ℝ)/n ≤ 1/64 := (div_le_iff₀ hnR).mpr (by nlinarith)
  exact ⟨hDn,hk1,hk2Δ,hk6,hs1,hbudget,hkL,hp⟩

end SemAC02.Supplement.P2MGraphPHPParameters
end

section
-- Inlined Solutions.P2MRandomGraphGoodEvent

set_option maxHeartbeats 3000000

namespace SemAC02.Supplement.P2MRandomGraphGoodEvent

open Finset P2MBernoulliAlgebra P2MBernoulliProduct P2MBernoulliProductBounds P2MRandomGraphFixedBoundary

attribute [local instance] Classical.propDecidable

noncomputable def Good (n Δ : ℕ) (x : Fin n×Fin (2*n) → Bool) : Prop :=
  IsBdryExp (graph n x) (P2MGraphPHPParameters.supportSize n Δ) ((Δ : ℝ)/4) ∧
    (∀ u, (PCNonBool.nbrOn (graph n x) univ u).card ≤ 2*Δ) ∧
    (∀ v, (univ.filter (fun u => (graph n x).Adj u v)).card ≤ 4*Δ)

 theorem probability_lower (n Δ : ℕ) (hn : 1 ≤ n) (hΔ : 1 ≤ Δ) (hΔn : Δ ≤ n)
    (hSmall : (2*(n : ℝ))*Real.exp (-(Δ : ℝ)/6)<1) :
    1-(((2*(n : ℝ))*Real.exp (-(Δ : ℝ)/6))/(1-(2*(n : ℝ))*Real.exp (-(Δ : ℝ)/6))+
      (2*(n : ℝ))*Real.exp (-(Δ : ℝ)/3)+(n : ℝ)*Real.exp (-(2*(Δ : ℝ))/3)) ≤
      prob ((Δ : ℝ)/n) (fun x : Fin n×Fin (2*n) → Bool => decide (Good n Δ x)) := by
  classical
  have hnR : (0 : ℝ)<n := by exact_mod_cast (show 0 < n by omega)
  have hΔR : (0 : ℝ)<Δ := by exact_mod_cast (show 0 < Δ by omega)
  let s := P2MGraphPHPParameters.supportSize n Δ
  let F : Fin 3 → (Fin n×Fin (2*n) → Bool) → Bool := fun i x =>
    if i=0 then decide (∃ S : Finset (Fin (2*n)), S.Nonempty ∧ S.card ≤ s ∧
      ((PCNonBool.boundaryOn (graph n x) univ S).card : ℝ)<(S.card : ℝ)*Δ/4)
    else if i=1 then decide (∃ u, 2*Δ<(PCNonBool.nbrOn (graph n x) univ u).card)
    else decide (∃ v, 4*Δ<(univ.filter (fun u => (graph n x).Adj u v)).card)
  have hcover : ∀ x : Fin n×Fin (2*n) → Bool, decide (¬ Good n Δ x)=true →
      ∃ i∈(univ : Finset (Fin 3)), F i x=true := by
    intro x hx
    have hbad := of_decide_eq_true hx
    by_cases hExp : IsBdryExp (graph n x) s ((Δ : ℝ)/4)
    · by_cases hL : ∀ u, (PCNonBool.nbrOn (graph n x) univ u).card ≤ 2*Δ
      · have hR : ¬ ∀ v, (univ.filter (fun u => (graph n x).Adj u v)).card ≤ 4*Δ :=
          fun hR => hbad ⟨hExp,hL,hR⟩
        push_neg at hR
        exact ⟨2,mem_univ _,by simpa [F] using hR⟩
      · push_neg at hL
        exact ⟨1,mem_univ _,by simpa [F] using hL⟩
    · unfold IsBdryExp at hExp
      push_neg at hExp
      obtain ⟨S,hSs,hSbad⟩ := hExp
      have hS : S.Nonempty := by
        by_contra hh
        have he : S=∅ := not_nonempty_iff_eq_empty.mp hh
        subst S
        simp [PCNonBool.boundaryOn] at hSbad
      refine ⟨0,mem_univ _,?_⟩
      simp only [F,ite_true]
      apply decide_eq_true
      exact ⟨S,hS,by exact_mod_cast hSs,by nlinarith⟩
  have hb := union_bound ((Δ : ℝ)/n) (by positivity) ((div_le_one hnR).mpr (by exact_mod_cast hΔn))
    (univ : Finset (Fin 3)) (fun x : Fin n×Fin (2*n) → Bool => decide (¬ Good n Δ x)) F hcover
  have hBudget : (4 : ℝ)*Δ*s ≤ n := by
    have hs : (s : ℝ) ≤ (n : ℝ)/(4*Δ) := Nat.floor_le (by positivity)
    have hh := (le_div_iff₀ (by positivity : (0 : ℝ)<4*Δ)).mp hs
    nlinarith
  have hB := P2MRandomGraphBoundaryExpansion.failure_probability n Δ s hn hΔ hΔn hBudget hSmall
  have hL := P2MRandomGraphDegreeBounds.pigeons_failure n Δ hn hΔn
  have hR := P2MRandomGraphDegreeBounds.holes_failure n Δ hn hΔn
  have hSum : (∑ i : Fin 3, prob ((Δ : ℝ)/n) (F i)) ≤
      ((2*(n : ℝ))*Real.exp (-(Δ : ℝ)/6))/(1-(2*(n : ℝ))*Real.exp (-(Δ : ℝ)/6))+
      (2*(n : ℝ))*Real.exp (-(Δ : ℝ)/3)+(n : ℝ)*Real.exp (-(2*(Δ : ℝ))/3) := by
    simpa [Fin.sum_univ_succ,F,add_assoc] using add_le_add (add_le_add hB hL) hR
  have hComp : prob ((Δ : ℝ)/n) (fun x : Fin n×Fin (2*n) → Bool => decide (¬ Good n Δ x))=
      1-prob ((Δ : ℝ)/n) (fun x : Fin n×Fin (2*n) → Bool => decide (Good n Δ x)) := by
    convert prob_complement ((Δ : ℝ)/n) (fun x : Fin n×Fin (2*n) → Bool => decide (Good n Δ x)) using 1
    congr 1
    funext x
    simp
  linarith [hb.trans hSum]

end SemAC02.Supplement.P2MRandomGraphGoodEvent
end

section
-- Inlined Solutions.P2MRandomGraphErrorBounds

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MRandomGraphErrorBounds

open P2MBernoulliProduct P2MRandomGraphGoodEvent

attribute [local instance] Classical.propDecidable

 theorem exp_neg_nat_log (n k : ℕ) (hn : 1 ≤ n) :
    Real.exp (-((k : ℝ)*Real.log (n : ℝ)))=1/(n : ℝ)^k := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast (show 0 < n by omega)
  rw [Real.exp_neg,Real.exp_nat_mul,Real.exp_log hnR,one_div]

 theorem tail_base (n Δ : ℕ) (hn : 1 ≤ n) (hΔ : 24*Real.log n ≤ (Δ : ℝ)) :
    (2*(n : ℝ))*Real.exp (-(Δ : ℝ)/6) ≤ 2/(n : ℝ)^3 := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast (show 0 < n by omega)
  have he : Real.exp (-(Δ : ℝ)/6) ≤ 1/(n : ℝ)^4 := by
    rw [←exp_neg_nat_log n 4 hn]
    apply Real.exp_le_exp.mpr
    norm_num only [Nat.cast_ofNat]
    linarith
  calc
    _ ≤ (2*(n : ℝ))*(1/(n : ℝ)^4) := mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by field_simp <;> ring

 theorem total_error (n Δ : ℕ) (hn : 2 ≤ n) (hΔ : 24*Real.log n ≤ (Δ : ℝ)) :
    (2*(n : ℝ))*Real.exp (-(Δ : ℝ)/6)<1 ∧
      ((2*(n : ℝ))*Real.exp (-(Δ : ℝ)/6))/(1-(2*(n : ℝ))*Real.exp (-(Δ : ℝ)/6))+
        (2*(n : ℝ))*Real.exp (-(Δ : ℝ)/3)+(n : ℝ)*Real.exp (-(2*(Δ : ℝ))/3) ≤ 7/(n : ℝ)^3 := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast (show 0 < n by omega)
  let q := (2*(n : ℝ))*Real.exp (-(Δ : ℝ)/6)
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq := tail_base n Δ (by omega) hΔ
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn3 : (8 : ℝ) ≤ (n : ℝ)^3 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hn2 3
    norm_num at hh
    exact hh
  have hqhalf : q ≤ 1/2 := by
    apply hq.trans
    exact (div_le_iff₀ (by positivity : (0 : ℝ)<(n : ℝ)^3)).mpr (by linarith)
  have hq1 : q < 1 := by linarith
  have hgeom : q/(1-q) ≤ 2*q := (div_le_iff₀ (by linarith : 0 < 1-q)).mpr (by nlinarith)
  have hD0 : (0 : ℝ) ≤ Δ := Nat.cast_nonneg _
  have hL : (2*(n : ℝ))*Real.exp (-(Δ : ℝ)/3) ≤ q :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (by positivity)
  have hR : (n : ℝ)*Real.exp (-(2*(Δ : ℝ))/3) ≤ q/2 := by
    have hh := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (show -(2*(Δ : ℝ))/3 ≤ -(Δ : ℝ)/6 by nlinarith)) hnR.le
    dsimp [q]
    nlinarith
  refine ⟨hq1,?_⟩
  change q/(1-q)+(2*(n : ℝ))*Real.exp (-(Δ : ℝ)/3)+(n : ℝ)*Real.exp (-(2*(Δ : ℝ))/3) ≤ _
  have hqr : q ≤ 2/(n : ℝ)^3 := hq
  simp only [div_eq_mul_inv] at hqr hgeom hL hR ⊢
  nlinarith

 theorem probability_lower (n Δ : ℕ) (hn : 2 ≤ n) (hΔ : 1 ≤ Δ) (hΔn : Δ ≤ n)
    (hΔlog : 24*Real.log n ≤ (Δ : ℝ)) :
    1-7/(n : ℝ)^3 ≤ prob ((Δ : ℝ)/n)
      (fun x : Fin n×Fin (2*n) → Bool => decide (P2MRandomGraphGoodEvent.Good n Δ x)) := by
  classical
  obtain ⟨hSmall,hErr⟩ := total_error n Δ hn hΔlog
  have hh := P2MRandomGraphGoodEvent.probability_lower n Δ (by omega) hΔ hΔn hSmall
  linarith

end SemAC02.Supplement.P2MRandomGraphErrorBounds
end

section
-- Inlined Solutions.P2MLogGrowth

open Filter Topology

namespace ProofComplexity.P2MLogGrowth

theorem eventually_log_large (b : ℝ) : ∀ᶠ n : ℕ in atTop, b ≤ Real.log (n : ℝ) :=
  (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop b

theorem eventually_log_power_le (A : ℝ) (k : ℕ) {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, A*(Real.log (n : ℝ))^k ≤ (n : ℝ)^C := by
  have h := (isLittleO_log_rpow_rpow_atTop (k : ℝ) hC).comp_tendsto
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hb := (h.const_mul_left A).bound (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hb] with n hn
  have he : |A*(Real.log (n : ℝ))^k| ≤ (n : ℝ)^C := by
    simpa only [Function.comp_apply,Real.rpow_natCast,Real.norm_eq_abs,one_mul,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) C)] using hn
  exact (le_abs_self _).trans he

theorem eventually_scaled_power_le (A p q : ℝ) (hpq : p < q) :
    ∀ᶠ n : ℕ in atTop, A*(n : ℝ)^p ≤ (n : ℝ)^q := by
  have hlarge := ((tendsto_rpow_atTop (by linarith : 0 < q-p)).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)).eventually_ge_atTop A
  filter_upwards [hlarge,eventually_ge_atTop 1] with n hn hn1
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  calc
    _ ≤ (n : ℝ)^(q-p)*(n : ℝ)^p := mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg hnp.le _)
    _ = (n : ℝ)^((q-p)+p) := (Real.rpow_add hnp _ _).symm
    _ = _ := by congr 1; ring

end ProofComplexity.P2MLogGrowth
end

section
-- Inlined Solutions.P2MGraphPHPAsymptoticParameters

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MGraphPHPAsymptoticParameters

open Filter

 theorem eventual_data : ∀ᶠ n : ℕ in atTop,
    128 ≤ n ∧ 1 ≤ php74Delta n ∧ 24*Real.log n ≤ (php74Delta n : ℝ) ∧
      1 ≤ Real.log n ∧ 1 ≤ Real.log (Real.log n) ∧
      php74Delta n ≤ n ∧ 1 ≤ P2MGraphPHPParameters.degree n (php74Delta n) ∧
      2*php74Delta n ≤ P2MGraphPHPParameters.degree n (php74Delta n) ∧
      6*P2MGraphPHPParameters.degree n (php74Delta n) ≤ n ∧
      1 ≤ P2MGraphPHPParameters.supportSize n (php74Delta n) ∧
      ((6*P2MGraphPHPParameters.degree n (php74Delta n) : ℕ) : ℝ)+2 ≤
        (php74Delta n : ℝ)*(P2MGraphPHPParameters.supportSize n (php74Delta n))/8 ∧
      (n : ℝ)/(8192*php74Delta n) ≤ P2MGraphPHPParameters.degree n (php74Delta n) ∧
      (P2MGraphPHPParameters.degree n (php74Delta n) : ℝ)/n ≤ 1/64 := by
  have hgrowth := ProofComplexity.P2MLogGrowth.eventually_log_power_le (32768*49^2) 2 (C:=1) (by norm_num)
  have hlog := ProofComplexity.P2MLogGrowth.eventually_log_large 1
  have hloglog := (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))).eventually_ge_atTop 1
  filter_upwards [hgrowth,hlog,hloglog,eventually_ge_atTop 128] with n hg hl hll hn
  have hnR : (0 : ℝ)<n := by exact_mod_cast (show 0 < n by omega)
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hl21 : Real.log 2 ≤ 1 := by have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2); linarith
  have hsum : Real.log (2*(n : ℝ))=Real.log 2+Real.log n := Real.log_mul (by norm_num) hnR.ne'
  have hLower : 24*Real.log n ≤ (php74Delta n : ℝ) := by
    have hh := Nat.le_ceil (24*Real.log (2*(n : ℝ)))
    rw [hsum] at hh
    change 24*Real.log n ≤ (⌈24*Real.log (2*(n : ℝ))⌉₊ : ℝ)
    rw [hsum]
    linarith
  have hD1 : 1 ≤ php74Delta n := by
    have hh : (1 : ℝ) ≤ php74Delta n := by linarith
    exact_mod_cast hh
  have hUpper : (php74Delta n : ℝ) ≤ 49*Real.log n := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ 24*Real.log (2*(n : ℝ)) by rw [hsum]; positivity)
    change (⌈24*Real.log (2*(n : ℝ))⌉₊ : ℝ) ≤ 49*Real.log n
    rw [hsum] at hh ⊢
    linarith
  have hlarge : 32768*(php74Delta n : ℝ)^2 ≤ n := by
    simp only [Real.rpow_one] at hg
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) (php74Delta n)) hUpper 2
    nlinarith
  rcases P2MGraphPHPParameters.finite_data n (php74Delta n) hn hD1 hlarge with
    ⟨hDn,hk,hDk,hkn,hs,hBudget,hkL,hp⟩
  exact ⟨hn,hD1,hLower,hl,hll,hDn,hk,hDk,hkn,hs,hBudget,hkL,hp⟩

 theorem width_bound (n w : ℕ) (hl : 1 ≤ Real.log n) (hll : 1 ≤ Real.log (Real.log n))
    (hD : 24*Real.log n ≤ (php74Delta n : ℝ))
    (hw : (w : ℝ) ≤ Real.log n/Real.log (Real.log n)) : w ≤ php74Delta n := by
  have hh : Real.log n/Real.log (Real.log n) ≤ Real.log n := div_le_self (by linarith) hll
  have hwr : (w : ℝ) ≤ php74Delta n := by linarith
  exact_mod_cast hwr

end SemAC02.Supplement.P2MGraphPHPAsymptoticParameters
end

section
-- Inlined Solutions.P2MRandomGraphExpansionTheorem

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.P2MRandomGraphExpansionTheorem

open Filter Topology P2MBernoulliProduct P2MBernoulliProductBounds P2MRandomGraphFixedBoundary

attribute [local instance] Classical.propDecidable

 theorem error_tends_zero : Tendsto (fun n : ℕ => 7/(n : ℝ)^3) atTop (𝓝 0) := by
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hh := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (7 : ℝ)) atTop (𝓝 7)).mul (hi.pow 3)
  simpa only [zero_pow (by decide : 3≠0),mul_zero,inv_pow,div_eq_mul_inv] using hh

 theorem full : Tendsto (fun n : ℕ =>
    prob ((php74Delta n : ℝ)/n) (fun x : Fin n×Fin (2*n) → Bool =>
      decide (Lemma74Concl (graph n x)))) atTop (𝓝 1) := by
  have hLower : Tendsto (fun n : ℕ => 1-7/(n : ℝ)^3) atTop (𝓝 1) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub error_tends_zero
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hLower tendsto_const_nhds
  · filter_upwards [P2MGraphPHPAsymptoticParameters.eventual_data] with n hn
    rcases hn with ⟨hn128,hΔ,hlog,hln,hll,hΔn,hRest⟩
    exact P2MRandomGraphErrorBounds.probability_lower n (php74Delta n) (by omega) hΔ hΔn hlog
  · filter_upwards [P2MGraphPHPAsymptoticParameters.eventual_data] with n hn
    rcases hn with ⟨hn128,hΔ,hlog,hln,hll,hΔn,hRest⟩
    apply le_one
    · positivity
    · apply (div_le_one (by exact_mod_cast (show 0 < n by omega) : (0 : ℝ)<n)).mpr
      exact_mod_cast hΔn

end SemAC02.Supplement.P2MRandomGraphExpansionTheorem
end

section
-- Inlined Theorems.Thm_SemAC02_Supplement_lemma_7_4_php_boundary_expanders
open Filter Topology
attribute [local instance] Classical.propDecidable
namespace SemAC02.Supplement

 theorem lemma_7_4_php_boundary_expanders :
    Tendsto (fun n : ℕ =>
      ∑ x : (Fin n × Fin (2*n) → Bool),
        if Lemma74Concl ({Adj := fun u v => x (v,u)=true} : PCNonBool.BipGraph (Fin (2*n)) (Fin n))
        then ∏ e : Fin n × Fin (2*n),
          (if x e then (php74Delta n : ℝ)/n else 1-(php74Delta n : ℝ)/n)
        else 0) atTop (𝓝 1) := by
  apply P2MRandomGraphExpansionTheorem.full.congr
  intro n
  unfold SemAC02.P2MBernoulliProduct.prob SemAC02.P2MBernoulliAlgebra.weight SemAC02.P2MBernoulliAlgebra.bitWeight
  apply Finset.sum_congr rfl
  intro x hx
  unfold P2MRandomGraphFixedBoundary.graph
  split_ifs <;> simp_all


end SemAC02.Supplement
end

end P2MRandomGraphProof
open SemAC02.Supplement Filter Topology
attribute [local instance] Classical.propDecidable
theorem solution :
    Tendsto (fun n : ℕ =>
      ∑ x : (Fin n × Fin (2*n) → Bool),
        if Lemma74Concl ({Adj := fun u v => x (v,u)=true} : PCNonBool.BipGraph (Fin (2*n)) (Fin n))
        then ∏ e : Fin n × Fin (2*n),
          (if x e then (php74Delta n : ℝ)/n else 1-(php74Delta n : ℝ)/n)
        else 0) atTop (𝓝 1)  := by
  exact P2MRandomGraphProof.SemAC02.Supplement.lemma_7_4_php_boundary_expanders
