-- Prove2me | solution 1 for Paley11987Verified.CompactLabeling.markedFamily_load_le
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-23T04:28:58.621653+00:00
-- url     : https://prove2.me/submissions/15ea7027-8638-4517-b8dc-2ae2ef74b06e

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Paley11987Support_036
import Definitions.Def_Paley11987Support_055
import Theorems.Thm_Paley11987Verified_CompactLabeling_card_internalEdges

set_option autoImplicit false
set_option Elab.async false
section z0

section

set_option maxHeartbeats 6000000
open scoped Classical BigOperators

namespace ZL

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]









theorem incidence_swap (R : V → V → Prop) (S T : Finset V) :
    ∑ x ∈ S, (outOn R T x).card = ∑ y ∈ T, (inOn R S y).card := by
  simp only [outOn, inOn, Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

theorem internalEdges_card_eq_sum (R : V → V → Prop) (S : Finset V) :
    (internalEdges R S).card = ∑ x ∈ S, (outOn R S x).card := by
  simp only [internalEdges, outOn, Finset.card_eq_sum_ones, Finset.sum_filter,
    Finset.sum_product]

theorem ordinary_degree_sum (R : V → V → Prop)
    (hloop : ∀ x, ¬ R x x)
    (htour : ∀ x y, x ≠ y → (R x y ↔ ¬ R y x)) (S : Finset V) :
    ∑ x ∈ S, (outOn R S x).card = S.card.choose 2 := by
  rw [← internalEdges_card_eq_sum, _root_.Paley11987Verified.CompactLabeling.card_internalEdges R hloop htour]

theorem first_moment_all (R : V → V → Prop) (D : ℕ)
    (hin : ∀ y, (inOn R Finset.univ y).card = D) (M : Finset V) :
    ∑ x : V, (outOn R M x).card = M.card * D := by
  rw [incidence_swap]
  simp_rw [hin]
  simp

theorem first_moment_external (R : V → V → Prop) (D : ℕ)
    (hloop : ∀ x, ¬ R x x)
    (htour : ∀ x y, x ≠ y → (R x y ↔ ¬ R y x))
    (hin : ∀ y, (inOn R Finset.univ y).card = D) (M : Finset V) :
    (∑ x ∈ Mᶜ, (outOn R M x).card) + M.card.choose 2 = M.card * D := by
  rw [← ordinary_degree_sum R hloop htour M]
  rw [Finset.sum_compl_add_sum]
  exact first_moment_all R D hin M

theorem powersetCard_outOn (R : V → V → Prop) (M : Finset V) (x : V) (k : ℕ) :
    (outOn R M x).powersetCard k =
      (M.powersetCard k).filter fun P => ∀ y ∈ P, R x y := by
  ext P
  simp only [Finset.mem_powersetCard, Finset.mem_filter]
  constructor
  · rintro ⟨hsub,hcard⟩
    exact ⟨⟨fun y hy => (Finset.mem_filter.mp (hsub hy)).1,hcard⟩,
      fun y hy => (Finset.mem_filter.mp (hsub hy)).2⟩
  · rintro ⟨⟨hsub,hcard⟩,hall⟩
    exact ⟨fun y hy => Finset.mem_filter.mpr ⟨hsub hy,hall y hy⟩,hcard⟩

theorem second_moment_all (R : V → V → Prop) (c : ℕ)
    (hcommon : ∀ x y, x ≠ y →
      (Finset.univ.filter fun z => R z x ∧ R z y).card = c)
    (M : Finset V) :
    ∑ x : V, ((outOn R M x).card.choose 2) = M.card.choose 2 * c := by
  have hpair (P : Finset V) (hP : P ∈ M.powersetCard 2) :
      (Finset.univ.filter fun z => ∀ y ∈ P, R z y).card = c := by
    have hcard := (Finset.mem_powersetCard.mp hP).2
    obtain ⟨x,y,hxy,rfl⟩ := Finset.card_eq_two.mp hcard
    simpa only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp,
      forall_eq] using hcommon x y hxy
  calc
    ∑ x : V, ((outOn R M x).card.choose 2) =
        ∑ x : V, ((M.powersetCard 2).filter fun P => ∀ y ∈ P, R x y).card := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [← Finset.card_powersetCard, powersetCard_outOn]
    _ = ∑ P ∈ M.powersetCard 2,
        (Finset.univ.filter fun z => ∀ y ∈ P, R z y).card := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
      exact Finset.sum_comm
    _ = ∑ _P ∈ M.powersetCard 2, c := Finset.sum_congr rfl hpair
    _ = M.card.choose 2 * c := by simp











end
end ZL
end
end z0

section z1

section

set_option maxHeartbeats 6000000
open scoped Classical BigOperators

namespace ZL.RowCounting
noncomputable section

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq Ω]





theorem smallSubsets_card_le (R : Finset Ω) (q : ℕ) :
    (smallSubsets R q).card ≤ rowPatterns q R.card := by
  let f : (smallSubsets R q) →
      (Σ j : Fin (q + 1), R.powersetCard j.val) := fun s =>
    ⟨⟨s.val.card, by
        have hs := (Finset.mem_filter.mp s.property).2
        omega⟩,
      ⟨s.val, Finset.mem_powersetCard.mpr
        ⟨Finset.mem_powerset.mp (Finset.mem_filter.mp s.property).1, rfl⟩⟩⟩
  have hf : Function.Injective f := by
    intro s t h
    apply Subtype.ext
    exact congrArg
      (fun z : (Σ j : Fin (q + 1), R.powersetCard j.val) =>
        (z.2 : Finset Ω)) h
  have hc := Fintype.card_le_of_injective f hf
  calc
    (smallSubsets R q).card ≤
        Fintype.card (Σ j : Fin (q + 1), R.powersetCard j.val) := by
      simpa only [Fintype.card_coe] using hc
    _ = ∑ j : Fin (q + 1), Fintype.card (R.powersetCard j.val) :=
      Fintype.card_sigma
    _ = rowPatterns q R.card := by
      simp only [rowPatterns, Fintype.card_coe, Finset.card_powersetCard]





theorem rowGood_card_le_smallSubsets
    (R : ι → Finset Ω) (q : ι → ℕ) (c : Ω → Fin 2) :
    (rowGood R q c).card ≤
      2 ^ (Fintype.card Ω - (rowUnion R).card) *
        ∏ i, (smallSubsets (R i) (q i)).card := by
  let S := rowUnion R
  let encode : (rowGood R q c) →
      ((Sᶜ : Finset Ω) → Fin 2) ×
        ((i : ι) → smallSubsets (R i) (q i)) := fun a =>
    ⟨fun e => a.val e.val,
      fun i =>
        ⟨(R i).filter (fun e => a.val e ≠ c e),
          Finset.mem_filter.mpr
            ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _),
              (Finset.mem_filter.mp a.property).2 i⟩⟩⟩
  have hencode : Function.Injective encode := by
    intro a b hab
    apply Subtype.ext
    funext e
    by_cases he : e ∈ S
    · obtain ⟨i, _, hei⟩ := Finset.mem_biUnion.mp he
      have hs := congrArg
        (fun z : ((Sᶜ : Finset Ω) → Fin 2) ×
            ((i : ι) → smallSubsets (R i) (q i)) =>
          (z.2 i : Finset Ω)) hab
      have hm := (Finset.ext_iff.mp hs) e
      simp only [encode, Finset.mem_filter, hei, true_and] at hm
      apply Fin.ext
      have ha := (a.val e).isLt
      have hb := (b.val e).isLt
      have hc := (c e).isLt
      have hm' : ((a.val e).val ≠ (c e).val) ↔
          ((b.val e).val ≠ (c e).val) := by
        simpa only [ne_eq, Fin.ext_iff] using hm
      omega
    · exact congrArg
        (fun z : ((Sᶜ : Finset Ω) → Fin 2) ×
            ((i : ι) → smallSubsets (R i) (q i)) =>
          z.1 ⟨e, Finset.mem_compl.mpr he⟩) hab
  have hc := Fintype.card_le_of_injective encode hencode
  simpa [S, Fintype.card_pi, Finset.card_compl] using hc

theorem rowGood_card_le
    (R : ι → Finset Ω) (q : ι → ℕ) (c : Ω → Fin 2) :
    (rowGood R q c).card ≤
      2 ^ (Fintype.card Ω - (rowUnion R).card) *
        ∏ i, rowPatterns (q i) (R i).card := by
  refine (rowGood_card_le_smallSubsets R q c).trans ?_
  apply Nat.mul_le_mul_left
  exact Finset.prod_le_prod' (fun i _ => smallSubsets_card_le (R i) (q i))





end
end ZL.RowCounting
end
end z1

section z9

section

set_option maxHeartbeats 8000000
open scoped Classical BigOperators

namespace ZL
noncomputable section

namespace SupportedFamily
variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]
variable (F : SupportedFamily V D)





theorem globalBad_card (d : D) :
    Fintype.card {ell : V → Fin 2 // F.bad d ell} =
      Fintype.card (F.LocalBad d) * 2 ^ (Fintype.card V - (F.support d).card) := by
  rw [Fintype.card_congr (F.globalBadEquiv d)]
  simp only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,
    Fintype.card_coe,Finset.card_compl]

theorem localBad_card_le_of_global (d : D) (B : ℕ)
    (h : Fintype.card {ell : V → Fin 2 // F.bad d ell} ≤
      B * 2 ^ (Fintype.card V - (F.support d).card)) :
    Fintype.card (F.LocalBad d) ≤ B := by
  rw [F.globalBad_card] at h
  exact Nat.le_of_mul_le_mul_right h (by positivity)

theorem localProbability_le_of_global (d : D) (B : ℕ)
    (h : Fintype.card {ell : V → Fin 2 // F.bad d ell} ≤
      B * 2 ^ (Fintype.card V - (F.support d).card)) :
    F.localProbability d ≤ (B : ℚ) / 2 ^ (F.support d).card := by
  exact div_le_div_of_nonneg_right (by exact_mod_cast F.localBad_card_le_of_global d B h)
    (by positivity)
end SupportedFamily

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (R : V → V → Prop)

open RowCounting



theorem outgoingRow_card (A : Finset V) (i : V) :
    (outgoingRow R A i).card = (outOn R A i).card := by
  apply Finset.card_image_of_injective
  intro x y h
  exact congrArg Prod.snd h

theorem outgoingRow_filter_card (A : Finset V) (i : V)
    (P : V × V → Prop) [DecidablePred P] :
    ((outgoingRow R A i).filter P).card =
      (A.filter (fun j => R i j ∧ P (i,j))).card := by
  rw [outgoingRow,Finset.filter_image,Finset.card_image_of_injective]
  · rw [outOn,Finset.filter_filter]
  · intro x y h
    exact congrArg Prod.snd h











end
end ZL
end
end z9

section z10

section

set_option maxHeartbeats 6000000
open scoped Classical BigOperators

namespace ZL
noncomputable section

variable {V : Type*} [DecidableEq V]





theorem weightedSubsets_insert (S : Finset V) (w : V → ℚ) (x : V)
    (hx : x ∉ S) (a : ℕ) :
    weightedSubsets (insert x S) w (a+1) =
      weightedSubsets S w (a+1) + w x * weightedSubsets S w a := by
  have hnot (A : Finset V) (hA : A ∈ S.powersetCard a) : x ∉ A :=
    fun h => hx ((Finset.mem_powersetCard.mp hA).1 h)
  have hdis : Disjoint (S.powersetCard (a+1))
      ((S.powersetCard a).image (insert x)) := by
    apply Finset.disjoint_left.mpr
    intro A hA hB
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hB
    exact hx ((Finset.mem_powersetCard.mp hA).1 (Finset.mem_insert_self x B))
  have hinj : Set.InjOn (fun A : Finset V => insert x A) (S.powersetCard a : Set (Finset V)) := by
    intro A hA B hB he
    have herase := congrArg (fun C : Finset V => C.erase x) he
    simpa only [Finset.erase_insert (hnot A hA),Finset.erase_insert (hnot B hB)] using herase
  unfold weightedSubsets
  rw [Finset.powersetCard_succ_insert hx, Finset.sum_union hdis, Finset.sum_image hinj]
  congr 1
  calc
    ∑ A ∈ S.powersetCard a, ∏ y ∈ insert x A, w y =
        ∑ A ∈ S.powersetCard a, w x * ∏ y ∈ A, w y :=
      Finset.sum_congr rfl fun A hA => Finset.prod_insert (hnot A hA)
    _ = w x * ∑ A ∈ S.powersetCard a, ∏ y ∈ A, w y := (Finset.mul_sum ..).symm

theorem factorial_mul_weightedSubsets_le (S : Finset V) (w : V → ℚ)
    (hw : ∀ x, 0 ≤ w x) : ∀ a : ℕ,
    (a.factorial : ℚ) * weightedSubsets S w a ≤ (∑ x ∈ S, w x)^a := by
  induction S using Finset.induction_on with
  | empty =>
    intro a
    cases a with
    | zero => simp [weightedSubsets]
    | succ a =>
      have he : (∅ : Finset V).powersetCard (a+1) = ∅ :=
        Finset.powersetCard_eq_empty.mpr (by simp)
      simp [weightedSubsets, he]
  | @insert x S hx ih =>
    intro a
    cases a with
    | zero => simp [weightedSubsets]
    | succ a =>
      have hsum : (0 : ℚ) ≤ ∑ y ∈ S, w y := Finset.sum_nonneg fun y _ => hw y
      have hfirst := ih (a+1)
      have hsecond := mul_le_mul_of_nonneg_left (ih a)
        (mul_nonneg (Nat.cast_nonneg (a+1)) (hw x))
      have hpower := pow_add_mul_le_add_pow hsum
        (add_nonneg (mul_nonneg (by norm_num) hsum) (hw x)) (a+1)
      rw [weightedSubsets_insert S w x hx, Finset.sum_insert hx]
      calc
        ((a+1).factorial : ℚ) *
            (weightedSubsets S w (a+1) + w x * weightedSubsets S w a) =
            ((a+1).factorial : ℚ) * weightedSubsets S w (a+1) +
              (a+1 : ℕ) * w x * ((a.factorial : ℚ) * weightedSubsets S w a) := by
          rw [Nat.factorial_succ]
          push_cast
          ring
        _ ≤ (∑ y ∈ S, w y)^(a+1) +
              (a+1 : ℕ) * w x * (∑ y ∈ S, w y)^a := add_le_add hfirst hsecond
        _ ≤ (w x + ∑ y ∈ S, w y)^(a+1) := by
          simpa only [Nat.add_sub_cancel, add_comm, mul_comm, mul_left_comm,
            mul_assoc] using hpower

theorem weightedSubsets_le (S : Finset V) (w : V → ℚ)
    (hw : ∀ x, 0 ≤ w x) (a : ℕ) (W : ℚ) (hW : ∑ x ∈ S, w x ≤ W) :
    weightedSubsets S w a ≤ W^a / a.factorial := by
  have hfac : (0 : ℚ) < a.factorial := by exact_mod_cast Nat.factorial_pos a
  apply (le_div_iff₀ hfac).mpr
  have hpow : (∑ x ∈ S, w x)^a ≤ W^a :=
    pow_le_pow_left₀ (Finset.sum_nonneg fun x _ => hw x) hW a
  simpa only [mul_comm] using (factorial_mul_weightedSubsets_le S w hw a).trans hpow

theorem quadratic_weight_sum_le (S : Finset V) (f : V → ℕ)
    (w : ℕ → ℚ) (α β γ W₁ W₂ : ℚ)
    (hw : ∀ x ∈ S, w (f x) ≤ α + β * f x + γ * (f x).choose 2)
    (hγ : 0 ≤ γ) (h₁ : ∑ x ∈ S, (f x : ℚ) = W₁)
    (h₂ : ∑ x ∈ S, ((f x).choose 2 : ℚ) ≤ W₂) :
    ∑ x ∈ S, w (f x) ≤ α * S.card + β * W₁ + γ * W₂ := by
  calc
    ∑ x ∈ S, w (f x) ≤ ∑ x ∈ S, (α + β * f x + γ * (f x).choose 2) :=
      Finset.sum_le_sum hw
    _ = α * S.card + β * W₁ + γ * (∑ x ∈ S, ((f x).choose 2 : ℚ)) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, h₁]
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ α * S.card + β * W₁ + γ * W₂ := by
      have h := mul_le_mul_of_nonneg_left h₂ hγ
      linarith

end
end ZL
end
end z10

section z11

section

set_option maxHeartbeats 8000000
open scoped Classical BigOperators

namespace ZL
noncomputable section
open RowCounting

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (R : V → V → Prop)



theorem markedRows_union (A M : Finset V) :
    rowUnion (markedRows R A M) = markedSupport R A M := by
  ext e
  simp only [rowUnion,Finset.mem_biUnion,Finset.mem_univ,true_and,
    markedSupport,Finset.mem_union,internalEdges,crossEdges,Finset.mem_filter,
    Finset.mem_product]
  constructor
  · rintro ⟨i,hi⟩
    cases i with
    | inl i =>
      obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hi
      subst e
      exact Or.inl ⟨⟨i.property,(Finset.mem_filter.mp hj).1⟩,(Finset.mem_filter.mp hj).2⟩
    | inr i =>
      obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hi
      subst e
      exact Or.inr ⟨⟨i.property,(Finset.mem_filter.mp hj).1⟩,(Finset.mem_filter.mp hj).2⟩
  · rintro (⟨⟨hi,hj⟩,hij⟩ | ⟨⟨hi,hj⟩,hij⟩)
    · refine ⟨Sum.inl ⟨e.1,hi⟩,?_⟩
      exact Finset.mem_image.mpr ⟨e.2,Finset.mem_filter.mpr ⟨hj,hij⟩,rfl⟩
    · refine ⟨Sum.inr ⟨e.1,hi⟩,?_⟩
      exact Finset.mem_image.mpr ⟨e.2,Finset.mem_filter.mpr ⟨hj,hij⟩,rfl⟩



theorem markedGood_row_bound (ell : V × V → Fin 2)
    (A M P : Finset V) (q B : ℕ) (color : V → Fin 2)
    (h : MarkedGood R ell A M P q B color) (i : A ⊕ M) :
    (((markedRows R A M i).filter (fun e => ell e ≠ color e.2)).card) ≤
      markedRowBudget R A M P q B i := by
  cases i with
  | inl i =>
    rw [markedRows,Sum.elim_inl,outgoingRow_filter_card]
    change (mismatch R ell A color i.val).card ≤ q - (outOn R M i.val).card
    exact Nat.le_sub_of_add_le (h.1 i.val i.property)
  | inr i =>
    rw [markedRows,Sum.elim_inr,outgoingRow_filter_card]
    change (mismatch R ell A color i.val).card ≤
      if B=0 then 0 else q+1
    by_cases hB : B=0
    · rw [if_pos hB]
      have hs : (mismatch R ell A color i.val).card ≤
          ∑ y ∈ M, (mismatch R ell A color y).card :=
        Finset.single_le_sum (f := fun y => (mismatch R ell A color y).card)
          (fun _ _ => Nat.zero_le _) i.property
      exact hs.trans (hB ▸ h.2.2)
    · rw [if_neg hB]
      have hh := h.2.1 i.val i.property
      split_ifs at hh <;> omega



theorem markedAssignments_count (A M P : Finset V) (q B : ℕ) :
    (markedAssignments R A M P q B).card ≤
      2 ^ A.card *
        (∏ i : A ⊕ M, rowPatterns (markedRowBudget R A M P q B i)
          (markedRows R A M i).card) *
        2 ^ (Fintype.card (V × V) - (markedSupport R A M).card) := by
  let encoded : Finset ((V × V) → Fin 2) :=
    Finset.univ.biUnion fun c : A → Fin 2 =>
      rowGood (markedRows R A M) (markedRowBudget R A M P q B) (headColor A c)
  have hsub : markedAssignments R A M P q B ⊆ encoded := by
    intro ell hell
    obtain ⟨c,hc⟩ := (Finset.mem_filter.mp hell).2
    apply Finset.mem_biUnion.mpr
    refine ⟨(fun x => c x.val),Finset.mem_univ _,?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    intro i
    have hh := markedGood_row_bound R ell A M P q B c hc i
    convert hh using 1
    congr 1
    apply Finset.filter_congr
    intro e he
    have hey : e.2 ∈ A := by
      cases i with
      | inl i =>
        obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp he
        exact (Finset.mem_filter.mp hj).1
      | inr i =>
        obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp he
        exact (Finset.mem_filter.mp hj).1
    simp only [headColor,dif_pos hey]
  have hg (c : A → Fin 2) :
      (rowGood (markedRows R A M) (markedRowBudget R A M P q B) (headColor A c)).card ≤
        2 ^ (Fintype.card (V × V) - (markedSupport R A M).card) *
          ∏ i : A ⊕ M, rowPatterns (markedRowBudget R A M P q B i)
            (markedRows R A M i).card := by
    simpa only [markedRows_union] using rowGood_card_le
      (markedRows R A M) (markedRowBudget R A M P q B) (headColor A c)
  apply (Finset.card_le_card hsub).trans
  apply Finset.card_biUnion_le.trans
  calc
    (∑ c : A → Fin 2,
      (rowGood (markedRows R A M) (markedRowBudget R A M P q B) (headColor A c)).card) ≤
      ∑ _c : A → Fin 2, 2 ^ (Fintype.card (V × V) - (markedSupport R A M).card) *
        ∏ i : A ⊕ M, rowPatterns (markedRowBudget R A M P q B i)
          (markedRows R A M i).card := Finset.sum_le_sum fun c _ => hg c
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_coe,
        Fintype.card_fin,Nat.nsmul_eq_mul]
      ring

theorem crossEdges_card (A M : Finset V) :
    (crossEdges R M A).card = ∑ x ∈ A, (inOn R M x).card := by
  calc
    (crossEdges R M A).card = ∑ y ∈ M, (outOn R A y).card := by
      simp only [crossEdges,outOn,Finset.card_eq_sum_ones,Finset.sum_filter,Finset.sum_product]
    _ = _ := incidence_swap R M A

theorem markedSupport_card_add
    (hloop : ∀ x, ¬ R x x)
    (htour : ∀ x y, x ≠ y → (R x y ↔ ¬ R y x))
    (A M : Finset V) (hdis : Disjoint A M) :
    (markedSupport R A M).card + ∑ x ∈ A, (outOn R M x).card =
      A.card.choose 2 + M.card * A.card := by
  have hedge : Disjoint (internalEdges R A) (crossEdges R M A) := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    exact Finset.disjoint_left.mp hdis
      (Finset.mem_product.mp (Finset.mem_filter.mp he).1).1
      (Finset.mem_product.mp (Finset.mem_filter.mp hf).1).1
  have hsum (x : V) (hx : x ∈ A) :
      (inOn R M x).card + (outOn R M x).card = M.card := by
    have hn : x ∉ M := Finset.disjoint_left.mp hdis hx
    have hd : Disjoint (inOn R M x) (outOn R M x) := by
      apply Finset.disjoint_left.mpr
      intro y hy hz
      have hne : x ≠ y := fun he => hn (he ▸ (Finset.mem_filter.mp hy).1)
      exact (htour y x hne.symm).mp (Finset.mem_filter.mp hy).2 (Finset.mem_filter.mp hz).2
    have hu : inOn R M x ∪ outOn R M x = M := by
      ext y
      simp only [Finset.mem_union,inOn,outOn,Finset.mem_filter]
      constructor
      · tauto
      · intro hy
        have hne : x ≠ y := fun he => hn (he ▸ hy)
        by_cases h : R x y
        · exact Or.inr ⟨hy,h⟩
        · exact Or.inl ⟨hy,(htour y x hne.symm).mpr h⟩
    rw [← Finset.card_union_of_disjoint hd,hu]
  rw [markedSupport,Finset.card_union_of_disjoint hedge,_root_.Paley11987Verified.CompactLabeling.card_internalEdges R hloop htour,
    crossEdges_card,add_assoc,← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl hsum]
  simp only [Finset.sum_const,Nat.nsmul_eq_mul]
  ring

end
end ZL
end
end z11

section z13

section

set_option maxHeartbeats 8000000
open scoped Classical BigOperators

namespace ZL
noncomputable section
open RowCounting
variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]



theorem marked_localProbability_le (F : SupportedFamily (V × V) D) (d : D)
    (R : V → V → Prop) (A M P : Finset V) (q B : ℕ)
    (hs : F.support d = markedSupport R A M)
    (hb : ∀ ell, F.bad d ell ↔ MarkedBad R ell A M P q B) :
    F.localProbability d ≤
      ((2 ^ A.card * ∏ i : A ⊕ M, rowPatterns (markedRowBudget R A M P q B i)
          (markedRows R A M i).card : ℕ) : ℚ) /
        2 ^ (markedSupport R A M).card := by
  rw [← hs]
  apply F.localProbability_le_of_global
  rw [Fintype.card_congr (Equiv.subtypeEquivRight hb),hs]
  simpa only [Fintype.card_subtype,markedAssignments] using markedAssignments_count R A M P q B



theorem rowPatterns_zero (d : ℕ) : rowPatterns 0 d = 1 := by
  simp [rowPatterns]

theorem rowPatterns_mono_degree (q d e : ℕ) (h : d ≤ e) :
    rowPatterns q d ≤ rowPatterns q e :=
  Finset.sum_le_sum fun i _ => Nat.choose_le_choose i.val h



theorem marked_pattern_product_le (R : V → V → Prop)
    (A M P : Finset V) (q B : ℕ) :
    (∏ i : A ⊕ M, rowPatterns (markedRowBudget R A M P q B i)
      (markedRows R A M i).card) ≤
      (∏ x : A, rowPatterns (q-(outOn R M x.val).card) (outOn R A x.val).card) *
        headErrorFactor q A.card M.card B := by
  rw [Fintype.prod_sum_type]
  simp only [markedRowBudget,markedRows,Sum.elim_inl,Sum.elim_inr,outgoingRow_card]
  apply Nat.mul_le_mul_left
  by_cases hB : B=0
  · simp only [headErrorFactor,if_pos hB,rowPatterns_zero,Finset.prod_const_one,le_refl]
  · simp only [headErrorFactor,if_neg hB]
    calc
      (∏ y : M, rowPatterns (q+1) (outOn R A y.val).card) ≤
          ∏ _y : M, rowPatterns (q+1) A.card :=
        Finset.prod_le_prod' fun y _ => rowPatterns_mono_degree _ _ _
          (Finset.card_le_card (Finset.filter_subset _ _))
      _ = (rowPatterns (q+1) A.card)^M.card := by simp

end
end ZL
end
end z13

section z14

section

set_option maxHeartbeats 6000000
open scoped Classical BigOperators

namespace ZL
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem orientation_weight_sum_le (R : V → V → Prop) (D c : ℕ)
    (hloop : ∀ x, ¬ R x x)
    (htour : ∀ x y, x ≠ y → (R x y ↔ ¬ R y x))
    (hin : ∀ y, (inOn R Finset.univ y).card = D)
    (hcommon : ∀ x y, x ≠ y →
      (Finset.univ.filter fun z => R z x ∧ R z y).card = c)
    (M : Finset V) (w : ℕ → ℚ) (α β γ : ℚ)
    (hγ : 0 ≤ γ)
    (hpoly : ∀ f ≤ M.card, w f ≤ α + β * f + γ * f.choose 2) :
    ∑ x ∈ Mᶜ, w (outOn R M x).card ≤
      α * (Fintype.card V - M.card) +
      β * ((M.card : ℚ) * D - M.card.choose 2) +
      γ * (M.card.choose 2 : ℚ) * c := by
  have h₁nat := first_moment_external R D hloop htour hin M
  have h₁ : ∑ x ∈ Mᶜ, ((outOn R M x).card : ℚ) =
      (M.card : ℚ) * D - M.card.choose 2 := by
    have hh : (∑ x ∈ Mᶜ, ((outOn R M x).card : ℚ)) + M.card.choose 2 =
        (M.card : ℚ) * D := by exact_mod_cast h₁nat
    linarith
  have h₂nat : ∑ x ∈ Mᶜ, (outOn R M x).card.choose 2 ≤ M.card.choose 2 * c := by
    have hs := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Mᶜ)
      (fun x _ _ => Nat.zero_le ((outOn R M x).card.choose 2))
    exact hs.trans_eq (second_moment_all R c hcommon M)
  have h₂ : ∑ x ∈ Mᶜ, ((outOn R M x).card.choose 2 : ℚ) ≤
      (M.card.choose 2 : ℚ) * c := by exact_mod_cast h₂nat
  have hh := quadratic_weight_sum_le Mᶜ (fun x => (outOn R M x).card) w α β γ
    ((M.card : ℚ)*D-M.card.choose 2) ((M.card.choose 2 : ℚ)*c)
    (fun x _ => hpoly _ (Finset.card_le_card (Finset.filter_subset _ _))) hγ h₁ h₂
  simpa only [Finset.card_compl,Nat.cast_sub (Finset.card_le_univ M),mul_assoc] using hh

end
end ZL
end
end z14

section z15

section

set_option maxHeartbeats 8000000
open scoped Classical BigOperators

namespace ZL
noncomputable section
open RowCounting
variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]



theorem orientationWeight_nonneg (q : ℕ) (C : ℕ → ℚ)
    (hC : ∀ t ≤ q, 0 ≤ C t) (f : ℕ) : 0 ≤ orientationWeight q C f := by
  unfold orientationWeight
  split_ifs with hf
  · exact mul_nonneg (by positivity) (hC _ (Nat.sub_le ..))
  · exact le_rfl

theorem ordinary_row_degree_lt (R : V → V → Prop) (hloop : ∀ x, ¬ R x x)
    (A : Finset V) (x : A) : (outOn R A x.val).card < A.card := by
  exact Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨x.val,x.property,hloop x.val⟩)

theorem tangent_ordinary_product (R : V → V → Prop)
    (hloop : ∀ x, ¬ R x x)
    (htour : ∀ x y, x ≠ y → (R x y ↔ ¬ R y x))
    (A M : Finset V) (q : ℕ) (u : ℚ) (C : ℕ → ℚ)
    (hu : 0 ≤ u) (hC : ∀ t ≤ q, 0 ≤ C t)
    (htan : ∀ d < A.card, ∀ t ≤ q, (rowPatterns t d : ℚ) ≤ C t * u^d) :
    (∏ x : A, (rowPatterns (q-(outOn R M x.val).card) (outOn R A x.val).card : ℚ)) ≤
      u^(A.card.choose 2) * ∏ x : A, C (q-(outOn R M x.val).card) := by
  have hsum : (∑ x : A, (outOn R A x.val).card) = A.card.choose 2 := by
    rw [Finset.sum_coe_sort (s := A) (f := fun x : V => (outOn R A x).card)]
    exact ordinary_degree_sum R hloop htour A
  calc
    (∏ x : A, (rowPatterns (q-(outOn R M x.val).card) (outOn R A x.val).card : ℚ)) ≤
        ∏ x : A, C (q-(outOn R M x.val).card) * u^(outOn R A x.val).card :=
      Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun x _ =>
        htan _ (ordinary_row_degree_lt R hloop A x) _ (Nat.sub_le ..))
    _ = _ := by
      rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,hsum,mul_comm]

theorem orientationWeight_product (R : V → V → Prop)
    (A M : Finset V) (q : ℕ) (C : ℕ → ℚ)
    (hadm : ∀ x ∈ A, (outOn R M x).card ≤ q) :
    (∏ x : A, orientationWeight q C (outOn R M x.val).card) =
      (2 : ℚ)^(∑ x ∈ A, (outOn R M x).card) *
        ∏ x : A, C (q-(outOn R M x.val).card) := by
  simp only [orientationWeight,if_pos (hadm _ (Subtype.property _)),
    Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
  rw [Finset.sum_coe_sort (s := A) (f := fun x : V => (outOn R M x).card)]

theorem SupportedFamily.localProbability_eq_zero_of_impossible
    (F : SupportedFamily (V × V) D) (d : D) (h : ∀ ell, ¬ F.bad d ell) :
    F.localProbability d = 0 := by
  letI : IsEmpty (F.LocalBad d) := ⟨fun u => h _ u.property⟩
  simp [SupportedFamily.localProbability]

theorem marked_localProbability_eq_zero_of_degree
    (F : SupportedFamily (V × V) D) (d : D)
    (R : V → V → Prop) (A M P : Finset V) (q B : ℕ)
    (hb : ∀ ell, F.bad d ell ↔ MarkedBad R ell A M P q B)
    (x : V) (hx : x ∈ A) (hq : q < (outOn R M x).card) :
    F.localProbability d = 0 := by
  apply F.localProbability_eq_zero_of_impossible
  intro ell hell
  obtain ⟨color,hcolor⟩ := (hb ell).mp hell
  have hh := hcolor.1 x hx
  omega

theorem marked_localProbability_weighted_le
    (F : SupportedFamily (V × V) D) (d : D)
    (R : V → V → Prop)
    (hloop : ∀ x, ¬ R x x)
    (htour : ∀ x y, x ≠ y → (R x y ↔ ¬ R y x))
    (A M P : Finset V) (q B : ℕ) (hdis : Disjoint A M)
    (hs : F.support d = markedSupport R A M)
    (hb : ∀ ell, F.bad d ell ↔ MarkedBad R ell A M P q B)
    (u : ℚ) (C : ℕ → ℚ) (hu : 0 ≤ u) (hC : ∀ t ≤ q, 0 ≤ C t)
    (htan : ∀ k < A.card, ∀ t ≤ q, (rowPatterns t k : ℚ) ≤ C t * u^k) :
    F.localProbability d ≤
      ((2 : ℚ)^A.card * headErrorFactor q A.card M.card B * u^(A.card.choose 2) /
        (2 : ℚ)^(A.card.choose 2 + M.card * A.card)) *
      ∏ x ∈ A, orientationWeight q C (outOn R M x).card := by
  by_cases hadm : ∀ x ∈ A, (outOn R M x).card ≤ q
  · let H : ℚ := ∏ x : A,
      (rowPatterns (q-(outOn R M x.val).card) (outOn R A x.val).card : ℚ)
    let CP : ℚ := ∏ x : A, C (q-(outOn R M x.val).card)
    have hcount : F.localProbability d ≤
        (2 : ℚ)^A.card * (H * headErrorFactor q A.card M.card B) /
          (2 : ℚ)^(markedSupport R A M).card := by
      apply (marked_localProbability_le F d R A M P q B hs hb).trans
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hh := Nat.mul_le_mul_left (2^A.card) (marked_pattern_product_le R A M P q B)
      have hh' : ((2^A.card * ∏ i : A ⊕ M,
          rowPatterns (markedRowBudget R A M P q B i) (markedRows R A M i).card : ℕ) : ℚ) ≤
          ((2^A.card * ((∏ x : A, rowPatterns (q-(outOn R M x.val).card)
            (outOn R A x.val).card) * headErrorFactor q A.card M.card B) : ℕ) : ℚ) := by
        exact_mod_cast hh
      simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_prod,H] using hh'
    have htanprod : H ≤ u^(A.card.choose 2) * CP :=
      tangent_ordinary_product R hloop htour A M q u C hu hC htan
    have hprodw : (∏ x ∈ A, orientationWeight q C (outOn R M x).card) =
        (2 : ℚ)^(∑ x ∈ A, (outOn R M x).card) * CP := by
      have hp := orientationWeight_product R A M q C hadm
      rw [Finset.prod_coe_sort (s := A)
        (f := fun x : V => orientationWeight q C (outOn R M x).card)] at hp
      exact hp
    have hsupport := markedSupport_card_add R hloop htour A M hdis
    have hpow : (2 : ℚ)^(A.card.choose 2 + M.card*A.card) =
        (2 : ℚ)^(markedSupport R A M).card *
          (2 : ℚ)^(∑ x ∈ A, (outOn R M x).card) := by
      rw [← pow_add,hsupport]
    calc
      F.localProbability d ≤
          (2 : ℚ)^A.card * (H * headErrorFactor q A.card M.card B) /
            (2 : ℚ)^(markedSupport R A M).card := hcount
      _ ≤ (2 : ℚ)^A.card *
          ((u^(A.card.choose 2) * CP) * headErrorFactor q A.card M.card B) /
            (2 : ℚ)^(markedSupport R A M).card := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right htanprod (Nat.cast_nonneg _)) (by positivity)
      _ = _ := by
        rw [hprodw,hpow]
        field_simp <;> ring
  · push_neg at hadm
    obtain ⟨x,hx,hq⟩ := hadm
    rw [marked_localProbability_eq_zero_of_degree F d R A M P q B hb x hx hq]
    apply mul_nonneg
    · positivity
    · exact Finset.prod_nonneg fun z _ => orientationWeight_nonneg q C hC _

end
end ZL
end
end z15

section z17

section

set_option maxHeartbeats 6000000
open scoped Classical BigOperators

namespace ZL
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
































theorem markedIndex_cardA (a m : ℕ) (I : MarkedIndex V a m) : I.2.val.card = a :=
  (Finset.mem_powersetCard.mp I.2.property).2

theorem markedIndex_cardM (a m : ℕ) (I : MarkedIndex V a m) : I.1.val.card = m :=
  (Finset.mem_powersetCard.mp I.1.property).2

theorem markedIndex_disjoint (a m : ℕ) (I : MarkedIndex V a m) :
    Disjoint I.2.val I.1.val := by
  apply Finset.disjoint_left.mpr
  intro x hx hm
  exact Finset.mem_compl.mp ((Finset.mem_powersetCard.mp I.2.property).1 hx) hm









end
end ZL
end
end z17

section z18

section

set_option maxHeartbeats 6000000
open scoped Classical BigOperators

namespace ZL
noncomputable section
variable {V : Type*} [DecidableEq V]

theorem weightedSubsets_containing_le (S T : Finset V) (a : ℕ) (w : V → ℚ)
    (hw : ∀ x, 0 ≤ w x) (W : ℚ) (hW : ∑ x ∈ S, w x ≤ W) :
    (∑ A ∈ (S.powersetCard a).filter (fun A => T ⊆ A), ∏ x ∈ A, w x) ≤
      (∏ x ∈ T, w x) * (W^(a-T.card) / (a-T.card).factorial) := by
  let F := (S.powersetCard a).filter (fun A => T ⊆ A)
  have hparts (A : Finset V) (hA : A ∈ F) :
      T ∪ (A \ T) = A := Finset.union_sdiff_of_subset (Finset.mem_filter.mp hA).2
  have hinj : Set.InjOn (fun A : Finset V => A \ T) (F : Set (Finset V)) := by
    intro A hA B hB he
    rw [← hparts A hA,← hparts B hB]
    exact congrArg (fun C : Finset V => T ∪ C) he
  have himage : F.image (fun A => A \ T) ⊆ (S \ T).powersetCard (a-T.card) := by
    intro B hB
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨hA,hT⟩ := Finset.mem_filter.mp hA
    obtain ⟨hAS,hcard⟩ := Finset.mem_powersetCard.mp hA
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_,?_⟩
    · intro x hx
      exact Finset.mem_sdiff.mpr ⟨hAS (Finset.mem_sdiff.mp hx).1,(Finset.mem_sdiff.mp hx).2⟩
    · rw [Finset.card_sdiff_of_subset hT,hcard]
  have hfactor (A : Finset V) (hA : A ∈ F) :
      (∏ x ∈ A, w x) = (∏ x ∈ T, w x) * ∏ x ∈ A \ T, w x := by
    have hd : Disjoint T (A \ T) := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      exact (Finset.mem_sdiff.mp hy).2 hx
    rw [← Finset.prod_union hd,hparts A hA]
  have hprod : (0 : ℚ) ≤ ∏ x ∈ T, w x := Finset.prod_nonneg fun x _ => hw x
  have hW' : ∑ x ∈ S \ T, w x ≤ W :=
    (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun x _ _ => hw x)).trans hW
  calc
    (∑ A ∈ F, ∏ x ∈ A, w x) =
        (∏ x ∈ T, w x) * ∑ A ∈ F, ∏ x ∈ A \ T, w x := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl hfactor
    _ = (∏ x ∈ T, w x) * ∑ B ∈ F.image (fun A => A \ T), ∏ x ∈ B, w x := by
      rw [Finset.sum_image hinj]
    _ ≤ (∏ x ∈ T, w x) * weightedSubsets (S \ T) w (a-T.card) := by
      apply mul_le_mul_of_nonneg_left _ hprod
      exact Finset.sum_le_sum_of_subset_of_nonneg himage
        (fun B _ _ => Finset.prod_nonneg fun x _ => hw x)
    _ ≤ (∏ x ∈ T, w x) * (W^(a-T.card) / (a-T.card).factorial) :=
      mul_le_mul_of_nonneg_left (weightedSubsets_le (S \ T) w hw _ W hW') hprod

theorem card_powersetCard_containing_le (S T : Finset V) (a : ℕ) :
    ((S.powersetCard a).filter (fun A => T ⊆ A)).card ≤
      S.card.choose (a-T.card) := by
  let F := (S.powersetCard a).filter (fun A => T ⊆ A)
  have hinj : Set.InjOn (fun A : Finset V => A \ T) (F : Set (Finset V)) := by
    intro A hA B hB he
    have hAT := (Finset.mem_filter.mp hA).2
    have hBT := (Finset.mem_filter.mp hB).2
    have hh := congrArg (fun C : Finset V => T ∪ C) he
    simpa only [Finset.union_sdiff_of_subset hAT,Finset.union_sdiff_of_subset hBT] using hh
  have hsub : F.image (fun A => A \ T) ⊆ S.powersetCard (a-T.card) := by
    intro B hB
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨hA,hT⟩ := Finset.mem_filter.mp hA
    obtain ⟨hAS,hcard⟩ := Finset.mem_powersetCard.mp hA
    apply Finset.mem_powersetCard.mpr
    refine ⟨Finset.sdiff_subset.trans hAS,?_⟩
    rw [Finset.card_sdiff_of_subset hT,hcard]
  calc
    F.card = (F.image (fun A => A \ T)).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (S.powersetCard (a-T.card)).card := Finset.card_le_card hsub
    _ = _ := Finset.card_powersetCard _ _

theorem weightedSubsets_containing_max_le (S T : Finset V) (a : ℕ)
    (w : V → ℚ) (hw : ∀ x, 0 ≤ w x) (wm W : ℚ)
    (hwm : ∀ x, w x ≤ wm) (hW0 : 0 ≤ W) (hW : ∑ x ∈ S, w x ≤ W) :
    (∑ A ∈ (S.powersetCard a).filter (fun A => T ⊆ A), ∏ x ∈ A, w x) ≤
      wm^T.card * (W^(a-T.card) / (a-T.card).factorial) := by
  have hp : (∏ x ∈ T, w x) ≤ wm^T.card := by
    calc
      (∏ x ∈ T, w x) ≤ ∏ _x ∈ T, wm :=
        Finset.prod_le_prod (fun x _ => hw x) (fun x _ => hwm x)
      _ = _ := by simp
  exact (weightedSubsets_containing_le S T a w hw W hW).trans
    (mul_le_mul_of_nonneg_right hp (by positivity))

end
end ZL
end
end z18

section z20

section

set_option maxHeartbeats 8000000
open scoped Classical BigOperators

namespace ZL
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem marked_weighted_load_split (R : V → V → Prop) (M : Finset V) (a : ℕ)
    (w : V → ℚ) (hw : ∀ x, 0 ≤ w x) (x y : V) :
    (∑ A ∈ (Mᶜ.powersetCard a).filter (fun A => (x,y) ∈ markedSupport R A M),
      ∏ z ∈ A, w z) ≤
    (∑ A ∈ (Mᶜ.powersetCard a).filter (fun A => {x,y} ⊆ A), ∏ z ∈ A, w z) +
    if x ∈ M then
      (∑ A ∈ (Mᶜ.powersetCard a).filter (fun A => {y} ⊆ A), ∏ z ∈ A, w z)
    else 0 := by
  simp only [Finset.sum_filter]
  have hpoint (A : Finset V) :
      (if (x,y) ∈ markedSupport R A M then ∏ z ∈ A, w z else 0) ≤
      (if {x,y} ⊆ A then ∏ z ∈ A, w z else 0) +
      if x ∈ M then (if {y} ⊆ A then ∏ z ∈ A, w z else 0) else 0 := by
    have hp : (0 : ℚ) ≤ ∏ z ∈ A, w z := Finset.prod_nonneg fun z _ => hw z
    by_cases he : (x,y) ∈ markedSupport R A M
    · have hcases : ({x,y} ⊆ A) ∨ (x ∈ M ∧ {y} ⊆ A) := by
        obtain he | he := Finset.mem_union.mp he
        · have he' := Finset.mem_product.mp (Finset.mem_filter.mp he).1
          exact Or.inl (by simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using he')
        · have he' := Finset.mem_product.mp (Finset.mem_filter.mp he).1
          exact Or.inr ⟨he'.1,Finset.singleton_subset_iff.mpr he'.2⟩
      rcases hcases with hxy | ⟨hx,hy⟩
      · simp only [if_pos he,if_pos hxy]
        split_ifs <;> linarith
      · simp only [if_pos he,if_pos hx,if_pos hy]
        split_ifs <;> linarith
    · simp only [if_neg he]
      split_ifs <;> linarith
  have hs := Finset.sum_le_sum (s := Mᶜ.powersetCard a) (fun A _ => hpoint A)
  rw [Finset.sum_add_distrib] at hs
  by_cases hx : x ∈ M
  · simpa only [if_pos hx] using hs
  · simpa only [if_neg hx,Finset.sum_const_zero,add_zero] using hs



theorem markedWeightedLoad_le (R : V → V → Prop) (a m : ℕ)
    (w : Finset V → V → ℚ) (wm W : ℚ) (hwm0 : 0 ≤ wm) (hW0 : 0 ≤ W)
    (hw : ∀ M ∈ (Finset.univ : Finset V).powersetCard m, ∀ z, 0 ≤ w M z)
    (hwm : ∀ M ∈ (Finset.univ : Finset V).powersetCard m, ∀ z, w M z ≤ wm)
    (hW : ∀ M ∈ (Finset.univ : Finset V).powersetCard m,
      ∑ z ∈ Mᶜ, w M z ≤ W)
    (x y : V) (hxy : x ≠ y) :
    markedWeightedLoad R a m w x y ≤
      ((Fintype.card V).choose m : ℚ) * wm^2 * (W^(a-2) / (a-2).factorial) +
      ((Fintype.card V).choose (m-1) : ℚ) * wm * (W^(a-1) / (a-1).factorial) := by
  let U := (Finset.univ : Finset V).powersetCard m
  let I : ℚ := wm^2 * (W^(a-2) / (a-2).factorial)
  let J : ℚ := wm * (W^(a-1) / (a-1).factorial)
  have hI0 : 0 ≤ I := by dsimp [I]; positivity
  have hJ0 : 0 ≤ J := by dsimp [J]; positivity
  have hbound (M : Finset V) (hM : M ∈ U) :
      (∑ A ∈ (Mᶜ.powersetCard a).filter (fun A => (x,y) ∈ markedSupport R A M),
        ∏ z ∈ A, w M z) ≤ I + if x ∈ M then J else 0 := by
    have hi := weightedSubsets_containing_max_le Mᶜ {x,y} a (w M) (hw M hM)
      wm W (hwm M hM) hW0 (hW M hM)
    have hj := weightedSubsets_containing_max_le Mᶜ {y} a (w M) (hw M hM)
      wm W (hwm M hM) hW0 (hW M hM)
    have hi' : (∑ A ∈ (Mᶜ.powersetCard a).filter (fun A => {x,y} ⊆ A),
        ∏ z ∈ A, w M z) ≤ I := by simpa only [Finset.card_pair hxy] using hi
    have hj' : (∑ A ∈ (Mᶜ.powersetCard a).filter (fun A => {y} ⊆ A),
        ∏ z ∈ A, w M z) ≤ J := by simpa only [Finset.card_singleton,pow_one] using hj
    apply (marked_weighted_load_split R M a (w M) (hw M hM) x y).trans
    by_cases hx : x ∈ M
    · simpa only [if_pos hx] using add_le_add hi' hj'
    · simpa only [if_neg hx,add_zero] using hi'
  have hc : (U.filter (fun M => x ∈ M)).card ≤ (Fintype.card V).choose (m-1) := by
    simpa only [U,Finset.singleton_subset_iff,Finset.card_singleton,Finset.card_univ] using
      card_powersetCard_containing_le (Finset.univ : Finset V) {x} m
  calc
    markedWeightedLoad R a m w x y ≤ ∑ M ∈ U, (I + if x ∈ M then J else 0) :=
      Finset.sum_le_sum hbound
    _ = (U.card : ℚ) * I + ((U.filter (fun M => x ∈ M)).card : ℚ) * J := by
      rw [Finset.sum_add_distrib,← Finset.sum_filter]
      simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ ((Fintype.card V).choose m : ℚ) * I +
        ((Fintype.card V).choose (m-1) : ℚ) * J := by
      simp only [U,Finset.card_powersetCard,Finset.card_univ]
      apply add_le_add le_rfl
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hJ0
    _ = _ := by dsimp [I,J]; ring

end
end ZL
end
end z20

section z21

section

set_option maxHeartbeats 8000000
open scoped Classical BigOperators

namespace ZL
noncomputable section
open RowCounting
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem markedIndex_weighted_mass (R : V → V → Prop) (a m : ℕ)
    (w : Finset V → V → ℚ) (x y : V) :
    (∑ I : MarkedIndex V a m,
      if (x,y) ∈ markedSupport R I.2.val I.1.val then ∏ z ∈ I.2.val, w I.1.val z else 0) =
      markedWeightedLoad R a m w x y := by
  change (∑ I : (Σ M : ((Finset.univ : Finset V).powersetCard m), M.valᶜ.powersetCard a),
      if (x,y) ∈ markedSupport R I.2.val I.1.val then ∏ z ∈ I.2.val, w I.1.val z else 0) = _
  rw [Fintype.sum_sigma]
  simp only [markedWeightedLoad,Finset.sum_filter]
  have hinner (M : ((Finset.univ : Finset V).powersetCard m)) :
      (∑ A : M.valᶜ.powersetCard a,
        if (x,y) ∈ markedSupport R A.val M.val then ∏ z ∈ A.val, w M.val z else 0) =
      ∑ A ∈ M.valᶜ.powersetCard a,
        if (x,y) ∈ markedSupport R A M.val then ∏ z ∈ A, w M.val z else 0 := by
    exact Finset.sum_coe_sort (s := M.valᶜ.powersetCard a)
      (f := fun A : Finset V =>
        if (x,y) ∈ markedSupport R A M.val then ∏ z ∈ A, w M.val z else 0)
  simp_rw [hinner]
  exact Finset.sum_coe_sort (s := (Finset.univ : Finset V).powersetCard m)
    (f := fun M : Finset V => ∑ A ∈ Mᶜ.powersetCard a,
      if (x,y) ∈ markedSupport R A M then ∏ z ∈ A, w M z else 0)

theorem markedFamily_probability_mass_le (R : V → V → Prop)
    (hloop : ∀ x, ¬ R x x)
    (htour : ∀ x y, x ≠ y → (R x y ↔ ¬ R y x))
    (q a m B : ℕ) (u : ℚ) (C : ℕ → ℚ)
    (hu : 0 ≤ u) (hC : ∀ t ≤ q, 0 ≤ C t)
    (htan : ∀ k < a, ∀ t ≤ q, (rowPatterns t k : ℚ) ≤ C t * u^k)
    (x y : V) :
    (∑ I ∈ Finset.univ.filter (fun I => (x,y) ∈ (markedFamily R q a m B).support I),
      (markedFamily R q a m B).localProbability I) ≤
      ((2 : ℚ)^a * headErrorFactor q a m B * u^(a.choose 2) / (2 : ℚ)^(a.choose 2+m*a)) *
        markedWeightedLoad R a m (fun M z => orientationWeight q C (outOn R M z).card) x y := by
  let pref : ℚ := (2 : ℚ)^a * headErrorFactor q a m B * u^(a.choose 2) /
    (2 : ℚ)^(a.choose 2+m*a)
  have hp (I : MarkedIndex V a m) :
      (markedFamily R q a m B).localProbability I ≤
        pref * ∏ z ∈ I.2.val, orientationWeight q C (outOn R I.1.val z).card := by
    have hA := markedIndex_cardA a m I
    have hM := markedIndex_cardM a m I
    have htan' : ∀ k < I.2.val.card, ∀ t ≤ q,
        (rowPatterns t k : ℚ) ≤ C t * u^k := by simpa only [hA] using htan
    have h := marked_localProbability_weighted_le (markedFamily R q a m B) I R hloop htour
      I.2.val I.1.val ∅ q B (markedIndex_disjoint a m I) rfl (fun _ => Iff.rfl)
      u C hu hC htan'
    simpa only [hA,hM,pref] using h
  calc
    (∑ I ∈ Finset.univ.filter (fun I => (x,y) ∈ (markedFamily R q a m B).support I),
      (markedFamily R q a m B).localProbability I) ≤
        ∑ I ∈ Finset.univ.filter (fun I => (x,y) ∈ (markedFamily R q a m B).support I),
          pref * ∏ z ∈ I.2.val, orientationWeight q C (outOn R I.1.val z).card :=
      Finset.sum_le_sum fun I _ => hp I
    _ = pref * markedWeightedLoad R a m
          (fun M z => orientationWeight q C (outOn R M z).card) x y := by
      rw [← Finset.mul_sum,Finset.sum_filter]
      congr 1
      calc
        _ = ∑ I : MarkedIndex V a m,
            if (x,y) ∈ markedSupport R I.2.val I.1.val then
              ∏ z ∈ I.2.val, orientationWeight q C (outOn R I.1.val z).card else 0 := by
          apply Finset.sum_congr
          · ext I; simp
          · intro I hI; rfl
        _ = _ := markedIndex_weighted_mass R a m
          (fun M z => orientationWeight q C (outOn R M z).card) x y

theorem _root_.solution (R : V → V → Prop) (n deg c : ℕ)
    (hn : Fintype.card V = n)
    (hloop : ∀ x, ¬ R x x)
    (htour : ∀ x y, x ≠ y → (R x y ↔ ¬ R y x))
    (hin : ∀ y, (inOn R Finset.univ y).card = deg)
    (hcommon : ∀ x y, x ≠ y →
      (Finset.univ.filter fun z => R z x ∧ R z y).card = c)
    (q a m B : ℕ) (u : ℚ) (C : ℕ → ℚ) (α β γ wm W lam : ℚ)
    (hu : 0 ≤ u) (hC : ∀ t ≤ q, 0 ≤ C t) (hγ : 0 ≤ γ)
    (hwm0 : 0 ≤ wm) (hW0 : 0 ≤ W) (hlam0 : 0 ≤ lam)
    (htan : ∀ k < a, ∀ t ≤ q, (rowPatterns t k : ℚ) ≤ C t * u^k)
    (hpoly : ∀ f ≤ m, orientationWeight q C f ≤ α+β*f+γ*f.choose 2)
    (hmax : ∀ f ≤ m, orientationWeight q C f ≤ wm)
    (hWdef : W = α*((n : ℚ)-m)+β*((m : ℚ)*deg-m.choose 2)+γ*(m.choose 2 : ℚ)*c)
    (x y : V) :
    (∑ I ∈ Finset.univ.filter (fun I => (x,y) ∈ (markedFamily R q a m B).support I),
      (markedFamily R q a m B).localProbability I * lam^(a.choose 2+m*a)) / 2 ≤
      ((2 : ℚ)^a * headErrorFactor q a m B * u^(a.choose 2) / (2 : ℚ)^(a.choose 2+m*a)) *
      (((n.choose m : ℚ)*wm^2)*(W^(a-2)/(a-2).factorial) +
       ((n.choose (m-1) : ℚ)*wm)*(W^(a-1)/(a-1).factorial)) *
        lam^(a.choose 2+m*a) / 2 := by
  by_cases hR : R x y
  · have hxy : x ≠ y := by rintro rfl; exact hloop x hR
    let w : Finset V → V → ℚ := fun M z => orientationWeight q C (outOn R M z).card
    have hw (M : Finset V) (_hM : M ∈ (Finset.univ : Finset V).powersetCard m)
        (z : V) : 0 ≤ w M z := orientationWeight_nonneg q C hC _
    have hf (M : Finset V) (hM : M ∈ (Finset.univ : Finset V).powersetCard m)
        (z : V) : (outOn R M z).card ≤ m := by
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.mem_powersetCard.mp hM).2
    have hwsum (M : Finset V) (hM : M ∈ (Finset.univ : Finset V).powersetCard m) :
        ∑ z ∈ Mᶜ, w M z ≤ W := by
      have hMc := (Finset.mem_powersetCard.mp hM).2
      have hp : ∀ f ≤ M.card, orientationWeight q C f ≤ α+β*f+γ*f.choose 2 := by
        simpa only [hMc] using hpoly
      have hh := orientation_weight_sum_le R deg c hloop htour hin hcommon M
        (orientationWeight q C) α β γ hγ hp
      simpa only [hn,hMc,← hWdef,w] using hh
    have hl := markedWeightedLoad_le R a m w wm W hwm0 hW0 hw
      (fun M hM z => hmax _ (hf M hM z)) hwsum x y hxy
    rw [hn] at hl
    have hp := markedFamily_probability_mass_le R hloop htour q a m B u C hu hC htan x y
    rw [← Finset.sum_mul]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hlam0 _)
    exact hp.trans (mul_le_mul_of_nonneg_left hl (by positivity))
  · have hempty : (Finset.univ.filter (fun I : MarkedIndex V a m =>
        (x,y) ∈ (markedFamily R q a m B).support I)) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro I _ hi
      obtain hi | hi := Finset.mem_union.mp hi
      · exact hR (Finset.mem_filter.mp hi).2
      · exact hR (Finset.mem_filter.mp hi).2
    rw [hempty,Finset.sum_empty,zero_div]
    positivity

end
end ZL
end
end z21
