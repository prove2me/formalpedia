-- Prove2me | solution 1 for PadbergRao.UpperBound.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T15:12:57.464749+00:00
-- url     : https://prove2.me/submissions/783560d0-6ba0-42f5-80ad-c68a80b87eab

import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Ring.Nat
import Definitions.Def_PadbergRao_UpperBound_graphGxd

namespace PadbergProof
open PadbergRao.UpperBound
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def cross {α : Type*} (U : Finset α) (p q : α) (w : ℝ) : ℝ :=
  by
    classical
    exact if (p ∈ U ↔ q ∈ U) then 0 else w

theorem cross_nonneg {α : Type*} (U : Finset α) (p q : α) (w : ℝ) (hw : 0 ≤ w) :
    0 ≤ cross U p q w := by unfold cross; split_ifs <;> positivity

theorem cross_symm {α : Type*} (U : Finset α) (p q : α) (w : ℝ) :
    cross U p q w = cross U q p w := by
  by_cases hp : p ∈ U <;> by_cases hq : q ∈ U <;> simp [cross,hp,hq]

theorem cross_compl {α : Type*} [Fintype α] [DecidableEq α] (U : Finset α) (p q : α) (w : ℝ) :
    cross Uᶜ p q w = cross U p q w := by
  by_cases hp : p ∈ U <;> by_cases hq : q ∈ U <;> simp [cross,hp,hq]

theorem if_add (P : Prop) [Decidable P] (a b : ℝ) :
    (if P then a+b else 0) = (if P then a else 0)+(if P then b else 0) := by
  by_cases h : P <;> simp [h]

theorem if_sum {α : Type*} (P : Prop) [Decidable P] (Z : Finset α) (F : α → ℝ) :
    (if P then ∑ z ∈ Z, F z else 0) = ∑ z ∈ Z, if P then F z else 0 := by
  by_cases h : P <;> simp [h]

theorem cap_formula (G : SimpleGraph V) [DecidableRel G.Adj] (b : V → ℕ) (d : Sym2 V → ℕ)
    (x : Sym2 V → ℝ) (tail : Sym2 V → V) (U : Finset (Node G x)) :
    yCap G b d x tail U =
      (∑ i : V, cross U (Sum.inl (some i)) (Sum.inl none) (slack G b x i))+
      ∑ e : {e : Sym2 V // e ∈ posEdges G x},
        ∑ i : V, cross U (Sum.inl (some i)) (Sum.inr e) (subdivWeight d x tail i e.1) := by
  classical
  have hsum (Z : Finset (Node G x)) (F : Node G x → ℝ) :
      ∑ p ∈ Z, F p = ∑ p : Node G x, if p ∈ Z then F p else 0 := by simp
  unfold yCap
  rw [hsum]
  simp_rw [hsum Uᶜ]
  simp only [Finset.mem_compl,Fintype.sum_sum_type,Fintype.sum_option]
  simp only [yWeight]
  simp only [ite_self,Finset.sum_const_zero,add_zero,zero_add]
  simp_rw [if_add,if_sum,Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i : V => fun e : {e : Sym2 V // e ∈ posEdges G x} =>
    if Sum.inl (some i) ∈ U then if Sum.inr e ∉ U then subdivWeight d x tail i e.1 else 0 else 0)]
  have hcross (p q : Node G x) (w : ℝ) :
      (if p ∈ U then if q ∉ U then w else 0 else 0)+
      (if q ∈ U then if p ∉ U then w else 0 else 0) = cross U p q w := by
    by_cases hp : p ∈ U <;> by_cases hq : q ∈ U <;> simp [cross,hp,hq]
  simp_rw [← hcross,Finset.sum_add_distrib]
  ring

end PadbergProof

namespace PadbergProof
open PadbergRao.UpperBound
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem pos_mem_edge (G : SimpleGraph V) [DecidableRel G.Adj] (x : Sym2 V → ℝ)
    {e : Sym2 V} (he : e ∈ posEdges G x) : e ∈ G.edgeFinset := (Finset.mem_filter.mp he).1

noncomputable def head (G : SimpleGraph V) [DecidableRel G.Adj] (tail : Sym2 V → V)
    (htail : ∀ e ∈ G.edgeFinset, tail e ∈ e) (e : Sym2 V) (he : e ∈ G.edgeFinset) : V :=
  Sym2.Mem.other (htail e he)

theorem edge_pair (G : SimpleGraph V) [DecidableRel G.Adj] (tail : Sym2 V → V)
    (htail : ∀ e ∈ G.edgeFinset, tail e ∈ e) (e : Sym2 V) (he : e ∈ G.edgeFinset) :
    e=s(tail e,head G tail htail e he) := (Sym2.other_spec (htail e he)).symm

theorem head_ne (G : SimpleGraph V) [DecidableRel G.Adj] (tail : Sym2 V → V)
    (htail : ∀ e ∈ G.edgeFinset, tail e ∈ e) (e : Sym2 V) (he : e ∈ G.edgeFinset) :
    head G tail htail e he ≠ tail e := Sym2.other_ne (G.not_isDiag_of_mem_edgeFinset he) (htail e he)

theorem subdiv_sum (G : SimpleGraph V) [DecidableRel G.Adj] (d : Sym2 V → ℕ)
    (x : Sym2 V → ℝ) (tail : Sym2 V → V) (htail : ∀ e ∈ G.edgeFinset, tail e ∈ e)
    (U : Finset (Node G x)) (e : {e : Sym2 V // e ∈ posEdges G x}) :
    (∑ i : V, cross U (Sum.inl (some i)) (Sum.inr e) (subdivWeight d x tail i e.1)) =
      cross U (Sum.inl (some (tail e))) (Sum.inr e) ((d e:ℝ)-x e)+
      cross U (Sum.inl (some (head G tail htail e (pos_mem_edge G x e.2)))) (Sum.inr e) (x e) := by
  classical
  let a := tail e
  let b := head G tail htail e (pos_mem_edge G x e.2)
  have hba : b ≠ a := Sym2.other_ne (G.not_isDiag_of_mem_edgeFinset (pos_mem_edge G x e.2)) (htail e (pos_mem_edge G x e.2))
  have he : e.1=s(a,b) := edge_pair G tail htail _ _
  have hh (i : V) : cross U (Sum.inl (some i)) (Sum.inr e) (subdivWeight d x tail i e.1) =
      (if i=a then cross U (Sum.inl (some a)) (Sum.inr e) ((d e:ℝ)-x e) else 0)+
      (if i=b then cross U (Sum.inl (some b)) (Sum.inr e) (x e) else 0) := by
    by_cases hia : i=a
    · subst i
      simp [subdivWeight,a,hba,Ne.symm hba]
    · by_cases hib : i=b
      · subst i
        simp only [subdivWeight,if_neg hia]
        have hbmem : b ∈ e.1 := by rw [he]; simp
        simp [hbmem,show b≠tail e from hia]
      · have hi : i ∉ e.1 := by rw [he]; simpa using ⟨hia,hib⟩
        simp [subdivWeight,show i≠tail e from hia,hi,hia,hib,cross]
  simp_rw [hh]
  rw [Finset.sum_add_distrib]
  simp [a,b]

end PadbergProof

namespace PadbergProof
open PadbergRao.UpperBound
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem slack_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] (b : V → ℕ) (d : Sym2 V → ℕ)
    (x : Sym2 V → ℝ) (hx : IsFeasible G b d x) (i : V) : 0 ≤ slack G b x i :=
  sub_nonneg.mpr (hx.2 i)

theorem subdiv_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] (b : V → ℕ) (d : Sym2 V → ℕ)
    (x : Sym2 V → ℝ) (hx : IsFeasible G b d x) (tail : Sym2 V → V) (i : V)
    (e : Sym2 V) (he : e ∈ G.edgeFinset) : 0 ≤ subdivWeight d x tail i e := by
  unfold subdivWeight
  split_ifs
  · exact sub_nonneg.mpr (hx.1 e he).2
  · exact (hx.1 e he).1
  · rfl

theorem cap_compl (G : SimpleGraph V) [DecidableRel G.Adj] (b : V → ℕ) (d : Sym2 V → ℕ)
    (x : Sym2 V → ℝ) (tail : Sym2 V → V) (U : Finset (Node G x)) :
    yCap G b d x tail Uᶜ = yCap G b d x tail U := by
  rw [cap_formula,cap_formula]
  simp only [cross_compl]

theorem cap_small_toggle (G : SimpleGraph V) [DecidableRel G.Adj] (b : V → ℕ) (d : Sym2 V → ℕ)
    (x : Sym2 V → ℝ) (hd : ∀ e ∈ G.edgeFinset, 0 < d e) (hx : IsFeasible G b d x)
    (tail : Sym2 V → V) (htail : ∀ e ∈ G.edgeFinset, tail e ∈ e)
    (U : Finset (Node G x)) (hcap : yCap G b d x tail U < 1)
    (e : {e : Sym2 V // e ∈ posEdges G x})
    (htog : ¬ (Sum.inl (some (tail e)) ∈ U ↔ Sum.inr e ∈ U)) :
    ¬ (Sum.inl (some (tail e)) ∈ U ↔
      Sum.inl (some (head G tail htail e (pos_mem_edge G x e.2))) ∈ U) := by
  classical
  intro heq
  have hs : 0 ≤ ∑ i : V, cross U (Sum.inl (some i)) (Sum.inl none) (slack G b x i) :=
    Finset.sum_nonneg (fun i _ => cross_nonneg _ _ _ _ (slack_nonneg G b d x hx i))
  have hn (f : {e : Sym2 V // e ∈ posEdges G x}) :
      0 ≤ ∑ i : V, cross U (Sum.inl (some i)) (Sum.inr f) (subdivWeight d x tail i f.1) :=
    Finset.sum_nonneg (fun i _ => cross_nonneg _ _ _ _ (subdiv_nonneg G b d x hx tail i f (pos_mem_edge G x f.2)))
  have hle := Finset.single_le_sum (fun f _ => hn f) (Finset.mem_univ e)
  have hd1 : (1:ℝ) ≤ d e := by exact_mod_cast hd e (pos_mem_edge G x e.2)
  have htog' : ¬ (Sum.inl (some (head G tail htail e (pos_mem_edge G x e.2))) ∈ U ↔ Sum.inr e ∈ U) := by
    exact fun h => htog (heq.trans h)
  rw [subdiv_sum G d x tail htail U e] at hle
  simp only [cross,if_neg htog,if_neg htog'] at hle
  rw [cap_formula] at hcap
  simp only [cross] at hcap hs
  linarith

end PadbergProof

open scoped BigOperators
namespace APadbergParity
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
open PadbergRao.UpperBound

def weight (G : SimpleGraph V) [DecidableRel G.Adj] (b : V → ℕ) (d : Sym2 V → ℕ)
    (x : Sym2 V → ℝ) (tail : Sym2 V → V) : Node G x → ℕ
  | Sum.inl none => ∑ v, b v
  | Sum.inl (some v) => b v + ∑ e ∈ (posEdges G x).filter (fun e => tail e = v), d e
  | Sum.inr e => d e.1

def vertices (G : SimpleGraph V) [DecidableRel G.Adj] (x : Sym2 V → ℝ)
    (U : Finset (Node G x)) : Finset V := Finset.univ.filter (fun v => Sum.inl (some v) ∈ U)

def toggles (G : SimpleGraph V) [DecidableRel G.Adj] (x : Sym2 V → ℝ)
    (tail : Sym2 V → V) (U : Finset (Node G x)) : Finset {e : Sym2 V // e ∈ posEdges G x} :=
  Finset.univ.filter (fun e => Xor (Sum.inr e ∈ U) (Sum.inl (some (tail e.1)) ∈ U))

theorem odd_iff_weight (G : SimpleGraph V) [DecidableRel G.Adj] (b : V → ℕ)
    (d : Sym2 V → ℕ) (x : Sym2 V → ℝ) (tail : Sym2 V → V) (U : Finset (Node G x)) :
    IsOddNodeSet G b d x tail U ↔ Odd (∑ p ∈ U, weight G b d x tail p) := by
  rw [Finset.odd_sum_iff_odd_card_odd]
  unfold IsOddNodeSet
  have hh : U.filter (fun p => label G b d x tail p = true) =
      U.filter (fun p => Odd (weight G b d x tail p)) := by
    apply Finset.filter_congr
    intro p hp
    cases p with
    | inl v => cases v <;> simp only [Finset.mem_filter,label,weight,decide_eq_true_eq]
    | inr e => simp only [Finset.mem_filter,label,weight,decide_eq_true_eq]
  rw [hh]


theorem cast_weight_sum (G : SimpleGraph V) [DecidableRel G.Adj] (b : V → ℕ)
    (d : Sym2 V → ℕ) (x : Sym2 V → ℝ) (tail : Sym2 V → V) (U : Finset (Node G x)) :
    ((∑ p ∈ U, weight G b d x tail p) : ZMod 2) =
      (if specialNode G x ∈ U then (∑ v, (b v : ZMod 2)) else 0) +
      (∑ v ∈ vertices G x U, (b v : ZMod 2)) +
      ∑ e ∈ toggles G x tail U, (d e.1 : ZMod 2) := by
  classical
  have hvertex (v : V) : (weight G b d x tail (Sum.inl (some v)) : ZMod 2) =
      (b v : ZMod 2) + ∑ e : {e : Sym2 V // e ∈ posEdges G x},
        if tail e.1 = v then (d e.1 : ZMod 2) else 0 := by
    simp only [weight, Nat.cast_add, Nat.cast_sum, Finset.sum_filter, apply_ite Nat.cast, Nat.cast_zero]
    rw [Finset.sum_subtype (posEdges G x) (fun _ => Iff.rfl)]
  have hsplit : (∑ p ∈ U, (weight G b d x tail p : ZMod 2)) =
      (if specialNode G x ∈ U then (∑ v, (b v : ZMod 2)) else 0) +
      (∑ v, if Sum.inl (some v) ∈ U then (weight G b d x tail (Sum.inl (some v)) : ZMod 2) else 0) +
      (∑ e : {e : Sym2 V // e ∈ posEdges G x}, if Sum.inr e ∈ U then (d e.1 : ZMod 2) else 0) := by
    calc
      _ = ∑ p : Node G x, if p ∈ U then (weight G b d x tail p : ZMod 2) else 0 := by simp
      _ = _ := by
        rw [Fintype.sum_sum_type, Fintype.sum_option]
        simp only [weight,specialNode,Nat.cast_sum]
        rfl
  rw [hsplit]
  simp only [vertices,toggles,Finset.sum_filter]
  simp_rw [hvertex]
  have hexpand (v : V) :
      (if Sum.inl (some v) ∈ U then (b v : ZMod 2) +
          ∑ e : {e : Sym2 V // e ∈ posEdges G x}, if tail e.1 = v then (d e.1 : ZMod 2) else 0 else 0) =
      (if Sum.inl (some v) ∈ U then (b v : ZMod 2) else 0) +
      ∑ e : {e : Sym2 V // e ∈ posEdges G x}, if Sum.inl (some v) ∈ U ∧ tail e.1 = v then (d e.1 : ZMod 2) else 0 := by
    by_cases h : Sum.inl (some v) ∈ U <;> simp [h]
  simp_rw [hexpand]
  rw [Finset.sum_add_distrib,Finset.sum_comm]
  have htail (e : {e : Sym2 V // e ∈ posEdges G x}) :
      (∑ v : V, if Sum.inl (some v) ∈ U ∧ tail e.1 = v then (d e.1 : ZMod 2) else 0) =
      if Sum.inl (some (tail e.1)) ∈ U then (d e.1 : ZMod 2) else 0 := by
    rw [Finset.sum_eq_single (tail e.1)]
    · simp
    · intro v hv hne
      simp [Ne.symm hne]
    · simp
  simp_rw [htail]
  have hedge (e : {e : Sym2 V // e ∈ posEdges G x}) :
      (if Sum.inl (some (tail e.1)) ∈ U then (d e.1 : ZMod 2) else 0) +
      (if Sum.inr e ∈ U then (d e.1 : ZMod 2) else 0) =
      (if Xor (Sum.inr e ∈ U) (Sum.inl (some (tail e.1)) ∈ U) then (d e.1 : ZMod 2) else 0) := by
    by_cases h1 : Sum.inl (some (tail e.1)) ∈ U <;>
      by_cases h2 : Sum.inr e ∈ U <;> simp [h1,h2,CharTwo.add_self_eq_zero]
  rw [add_assoc,add_assoc,←Finset.sum_add_distrib]
  simp_rw [hedge]
  simp only [add_assoc]

theorem odd_iff_vertices_toggles (G : SimpleGraph V) [DecidableRel G.Adj] (b : V → ℕ)
    (d : Sym2 V → ℕ) (x : Sym2 V → ℝ) (tail : Sym2 V → V) (U : Finset (Node G x))
    (hU : specialNode G x ∉ U) :
    IsOddNodeSet G b d x tail U ↔
      Odd ((∑ v ∈ vertices G x U, b v) + (∑ e ∈ toggles G x tail U, d e.1)) := by
  rw [odd_iff_weight, ← ZMod.natCast_eq_one_iff_odd, ← ZMod.natCast_eq_one_iff_odd]
  have h := cast_weight_sum G b d x tail U
  simp only [if_neg hU,zero_add] at h
  simpa only [Nat.cast_sum,Nat.cast_add] using Iff.of_eq (congrArg (fun z : ZMod 2 => z = 1) h)

theorem even_total_weight (G : SimpleGraph V) [DecidableRel G.Adj] (b : V → ℕ)
    (d : Sym2 V → ℕ) (x : Sym2 V → ℝ) (tail : Sym2 V → V) :
    Even (∑ p : Node G x, weight G b d x tail p) := by
  classical
  apply ZMod.natCast_eq_zero_iff_even.mp
  have h := cast_weight_sum G b d x tail Finset.univ
  simpa [vertices,toggles,CharTwo.add_self_eq_zero,Nat.cast_sum] using h

theorem odd_compl_iff (G : SimpleGraph V) [DecidableRel G.Adj] (b : V → ℕ)
    (d : Sym2 V → ℕ) (x : Sym2 V → ℝ) (tail : Sym2 V → V) (U : Finset (Node G x)) :
    IsOddNodeSet G b d x tail Uᶜ ↔ IsOddNodeSet G b d x tail U := by
  classical
  rw [odd_iff_weight,odd_iff_weight]
  have h := even_total_weight G b d x tail
  rw [← Finset.sum_add_sum_compl U (weight G b d x tail),Nat.even_add] at h
  simpa only [←Nat.not_even_iff_odd] using not_congr h.symm

end
end APadbergParity
open scoped BigOperators
namespace APadbergParity
noncomputable section
open PadbergRao.UpperBound
variable {V : Type*} [Fintype V] [DecidableEq V]

def construct (G : SimpleGraph V) [DecidableRel G.Adj] (x : Sym2 V → ℝ)
    (tail : Sym2 V → V) (W : Finset V)
    (R : Finset {e : Sym2 V // e ∈ posEdges G x}) : Finset (Node G x) := by
  classical
  exact Finset.univ.filter fun p => match p with
    | Sum.inl none => False
    | Sum.inl (some v) => v ∈ W
    | Sum.inr e => Xor (e ∈ R) (tail e.1 ∈ W)

theorem special_not_construct (G : SimpleGraph V) [DecidableRel G.Adj] (x : Sym2 V → ℝ)
    (tail : Sym2 V → V) (W : Finset V)
    (R : Finset {e : Sym2 V // e ∈ posEdges G x}) :
    specialNode G x ∉ construct G x tail W R := by
  classical
  simp [construct,specialNode]

theorem vertices_construct (G : SimpleGraph V) [DecidableRel G.Adj] (x : Sym2 V → ℝ)
    (tail : Sym2 V → V) (W : Finset V)
    (R : Finset {e : Sym2 V // e ∈ posEdges G x}) :
    vertices G x (construct G x tail W R) = W := by
  classical
  apply Finset.ext
  intro v
  simp [vertices,construct]

theorem toggles_construct (G : SimpleGraph V) [DecidableRel G.Adj] (x : Sym2 V → ℝ)
    (tail : Sym2 V → V) (W : Finset V)
    (R : Finset {e : Sym2 V // e ∈ posEdges G x}) :
    toggles G x tail (construct G x tail W R) = R := by
  classical
  apply Finset.ext
  intro e
  simp only [toggles,construct,Finset.mem_filter,Finset.mem_univ,true_and]
  by_cases hr : e ∈ R <;> by_cases hw : tail e.1 ∈ W <;> simp [hr,hw]

end
end APadbergParity
namespace PadbergProof
open PadbergRao.UpperBound APadbergParity
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem cut_ends (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V)
    (tail : Sym2 V → V) (htail : ∀ e ∈ G.edgeFinset, tail e ∈ e)
    (e : Sym2 V) (he : e ∈ G.edgeFinset) :
    e ∈ cutEdges G W ↔ ¬(tail e ∈ W ↔ head G tail htail e he ∈ W) := by
  classical
  have hm (v : V) : v ∈ e ↔ v=tail e ∨ v=head G tail htail e he := by
    conv_lhs => rw [edge_pair G tail htail e he]
    exact Sym2.mem_iff
  simp only [cutEdges,Finset.mem_filter,he,true_and,hm]
  by_cases ha : tail e ∈ W <;> by_cases hb : head G tail htail e he ∈ W <;> simp_all

theorem toggles_cut (G : SimpleGraph V) [DecidableRel G.Adj] (b : V → ℕ) (d : Sym2 V → ℕ)
    (x : Sym2 V → ℝ) (hd : ∀ e ∈ G.edgeFinset, 0 < d e) (hx : IsFeasible G b d x)
    (tail : Sym2 V → V) (htail : ∀ e ∈ G.edgeFinset, tail e ∈ e)
    (U : Finset (Node G x)) (hcap : yCap G b d x tail U < 1) :
    ∀ e ∈ toggles G x tail U, e.1 ∈ cutEdges G (vertices G x U) := by
  classical
  intro e he
  have htog : ¬(Sum.inl (some (tail e)) ∈ U ↔ Sum.inr e ∈ U) := by
    simpa [toggles,xor_iff_not_iff,iff_comm] using he
  have hh := cap_small_toggle G b d x hd hx tail htail U hcap e htog
  rw [cut_ends G _ tail htail e (pos_mem_edge G x e.2)]
  simpa [vertices] using hh

theorem edge_contribution (G : SimpleGraph V) [DecidableRel G.Adj] (b : V → ℕ) (d : Sym2 V → ℕ)
    (x : Sym2 V → ℝ) (tail : Sym2 V → V) (htail : ∀ e ∈ G.edgeFinset, tail e ∈ e)
    (U : Finset (Node G x))
    (hR : ∀ e ∈ toggles G x tail U, e.1 ∈ cutEdges G (vertices G x U))
    (e : {e : Sym2 V // e ∈ posEdges G x}) :
    (∑ i : V, cross U (Sum.inl (some i)) (Sum.inr e) (subdivWeight d x tail i e.1)) =
      (if e.1 ∈ cutEdges G (vertices G x U) then x e else 0)+
      (if e ∈ toggles G x tail U then (d e:ℝ)-2*x e else 0) := by
  classical
  rw [subdiv_sum G d x tail htail U e]
  simp only [cut_ends G _ tail htail e (pos_mem_edge G x e.2)]
  have hh := hR e
  rw [cut_ends G _ tail htail e (pos_mem_edge G x e.2)] at hh
  by_cases ha : Sum.inl (some (tail e)) ∈ U <;>
    by_cases hb : Sum.inl (some (head G tail htail e (pos_mem_edge G x e.2))) ∈ U <;>
    by_cases hz : Sum.inr e ∈ U
  all_goals simp [cross,vertices,toggles,ha,hb,hz] at hh ⊢ <;> ring

end PadbergProof
namespace PadbergProof
open PadbergRao.UpperBound APadbergParity
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem sum_cut_pos (G : SimpleGraph V) [DecidableRel G.Adj] (b : V → ℕ) (d : Sym2 V → ℕ)
    (x : Sym2 V → ℝ) (hx : IsFeasible G b d x) (W : Finset V) :
    (∑ e : {e : Sym2 V // e ∈ posEdges G x}, if e.1 ∈ cutEdges G W then x e else 0) =
      ∑ e ∈ cutEdges G W, x e := by
  classical
  rw [← Finset.sum_subtype (posEdges G x) (fun _ => Iff.rfl) (f := fun e => if e ∈ cutEdges G W then x e else 0)]
  simp only [posEdges,Finset.sum_filter]
  conv_rhs => unfold cutEdges; rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hp : 0 < x e
  · simp [hp,cutEdges,Finset.mem_filter,he]
  · have hz : x e=0 := le_antisymm (not_lt.mp hp) (hx.1 e he).1
    simp [hz]

theorem sum_image_val {M : Type*} [AddCommMonoid M] (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : Sym2 V → ℝ) (R : Finset {e : Sym2 V // e ∈ posEdges G x}) (F : Sym2 V → M) :
    (∑ e ∈ R.image Subtype.val, F e) = ∑ e ∈ R, F e.1 := by
  classical
  rw [Finset.sum_image]
  intro a ha b hb hab
  exact Subtype.ext hab

noncomputable def toggleEdges (G : SimpleGraph V) [DecidableRel G.Adj] (x : Sym2 V → ℝ)
    (tail : Sym2 V → V) (U : Finset (Node G x)) : Finset (Sym2 V) :=
  (toggles G x tail U).image Subtype.val

theorem cap_identity (G : SimpleGraph V) [DecidableRel G.Adj] (b : V → ℕ) (d : Sym2 V → ℕ)
    (x : Sym2 V → ℝ) (hx : IsFeasible G b d x)
    (tail : Sym2 V → V) (htail : ∀ e ∈ G.edgeFinset, tail e ∈ e)
    (U : Finset (Node G x)) (hS : specialNode G x ∉ U)
    (hR : ∀ e ∈ toggles G x tail U, e.1 ∈ cutEdges G (vertices G x U)) :
    yCap G b d x tail U =
      (∑ e ∈ cutEdges G (vertices G x U), x e)+
      (∑ e ∈ toggleEdges G x tail U, (d e:ℝ))-2*(∑ e ∈ toggleEdges G x tail U, x e)+
      (∑ i ∈ vertices G x U, slack G b x i) := by
  classical
  rw [cap_formula]
  have hn : (Sum.inl none : Node G x) ∉ U := hS
  have hs : (∑ i : V, cross U (Sum.inl (some i)) (Sum.inl none) (slack G b x i)) =
      ∑ i ∈ vertices G x U, slack G b x i := by
    simp [vertices,Finset.sum_filter,cross,hn]
  rw [hs]
  simp_rw [edge_contribution G b d x tail htail U hR]
  rw [Finset.sum_add_distrib,sum_cut_pos G b d x hx]
  have ht : (∑ e : {e : Sym2 V // e ∈ posEdges G x},
      if e ∈ toggles G x tail U then (d e:ℝ)-2*x e else 0) =
      (∑ e ∈ toggleEdges G x tail U, (d e:ℝ))-2*(∑ e ∈ toggleEdges G x tail U, x e) := by
    simp only [toggleEdges,sum_image_val,Finset.sum_sub_distrib,Finset.mul_sum]
    have hi : (posEdges G x).attach ∩ toggles G x tail U = toggles G x tail U :=
      Finset.inter_eq_right.mpr (by intro e he; exact Finset.mem_attach _ _)
    simp [hi]
  rw [ht]
  ring

end PadbergProof
namespace PadbergProof
open PadbergRao.UpperBound APadbergParity
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem lemma32 (G : SimpleGraph V) [DecidableRel G.Adj] (b : V → ℕ) (d : Sym2 V → ℕ)
    (x : Sym2 V → ℝ) (hd : ∀ e ∈ G.edgeFinset, 0 < d e) (hx : IsFeasible G b d x)
    (tail : Sym2 V → V) (htail : ∀ e ∈ G.edgeFinset, tail e ∈ e)
    (U : Finset (Node G x)) (hU : IsOddNodeSet G b d x tail U)
    (hcap : yCap G b d x tail U < 1) (hS : specialNode G x ∉ U) :
    ∃ (W : Finset V) (T : Finset (Sym2 V)), T ⊆ cutEdges G W ∧
      Odd ((∑ i ∈ W, b i)+(∑ e ∈ T, d e)) ∧
      (∑ e ∈ cutEdges G W, x e)+(∑ e ∈ T, (d e:ℝ))-2*(∑ e ∈ T, x e)+
        (∑ i ∈ W, slack G b x i)=yCap G b d x tail U := by
  classical
  have hR := toggles_cut G b d x hd hx tail htail U hcap
  refine ⟨vertices G x U,toggleEdges G x tail U,?_,?_,(cap_identity G b d x hx tail htail U hS hR).symm⟩
  · intro e he
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
    exact hR f hf
  · rw [toggleEdges,sum_image_val]
    exact (odd_iff_vertices_toggles G b d x tail U hS).mp hU

theorem lemma31 (G : SimpleGraph V) [DecidableRel G.Adj] (b : V → ℕ) (d : Sym2 V → ℕ)
    (x : Sym2 V → ℝ) (hx : IsFeasible G b d x)
    (tail : Sym2 V → V) (htail : ∀ e ∈ G.edgeFinset, tail e ∈ e)
    (W : Finset V) (T : Finset (Sym2 V)) (hT : T ⊆ cutEdges G W ∩ posEdges G x)
    (hodd : Odd ((∑ i ∈ W, b i)+(∑ e ∈ T, d e))) :
    ∃ U : Finset (Node G x), IsOddNodeSet G b d x tail U ∧ specialNode G x ∉ U ∧
      (∑ e ∈ cutEdges G W, x e)+(∑ e ∈ T, (d e:ℝ))-2*(∑ e ∈ T, x e)+
        (∑ i ∈ W, slack G b x i)=yCap G b d x tail U := by
  classical
  let R : Finset {e : Sym2 V // e ∈ posEdges G x} := Finset.univ.filter (fun e => e.1 ∈ T)
  have hRT : R.image Subtype.val=T := by
    ext e
    simp only [Finset.mem_image,R,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨f,hf,rfl⟩; exact hf
    · intro he
      exact ⟨⟨e,(Finset.mem_inter.mp (hT he)).2⟩,he,rfl⟩
  let U := construct G x tail W R
  have hS : specialNode G x ∉ U := special_not_construct G x tail W R
  have hW : vertices G x U=W := vertices_construct G x tail W R
  have hRU : toggles G x tail U=R := toggles_construct G x tail W R
  have hTU : toggleEdges G x tail U=T := by rw [toggleEdges,hRU,hRT]
  have hR : ∀ e ∈ toggles G x tail U, e.1 ∈ cutEdges G (vertices G x U) := by
    intro e he
    rw [hRU] at he
    rw [hW]
    exact (Finset.mem_inter.mp (hT (Finset.mem_filter.mp he).2)).1
  refine ⟨U,?_,hS,?_⟩
  · rw [odd_iff_vertices_toggles G b d x tail U hS,hW,hRU,← sum_image_val G x R d,hRT]
    exact hodd
  · have hc := cap_identity G b d x hx tail htail U hS hR
    rw [hW,hTU] at hc
    exact hc.symm

end PadbergProof

namespace PadbergProof
open PadbergRao.UpperBound
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem incident_sum (G : SimpleGraph V) [DecidableRel G.Adj] (x : Sym2 V → ℝ)
    (W : Finset V) :
    (∑ i ∈ W, ∑ e ∈ incidentEdges G i, x e) =
      2*(∑ e ∈ edgesWithin G W, x e)+∑ e ∈ cutEdges G W, x e := by
  classical
  simp only [incidentEdges,edgesWithin,cutEdges,Finset.sum_filter]
  rw [Finset.sum_comm,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  induction e using Sym2.inductionOn with
  | hf u v =>
    have huv : u ≠ v := by
      have hadj : G.Adj u v := by simpa using he
      exact hadj.ne
    have hind (i : V) : (if i ∈ s(u,v) then x s(u,v) else 0) =
        (if i=u then x s(u,v) else 0)+(if i=v then x s(u,v) else 0) := by
      simp only [Sym2.mem_iff]
      by_cases hiu : i=u <;> by_cases hiv : i=v <;> simp_all
    simp_rw [hind]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq']
    by_cases hu : u ∈ W <;> by_cases hv : v ∈ W
    all_goals simp [Sym2.mem_iff,hu,hv,huv] <;> ring

theorem slack_sum (G : SimpleGraph V) [DecidableRel G.Adj] (b : V → ℕ)
    (x : Sym2 V → ℝ) (W : Finset V) :
    (∑ i ∈ W, slack G b x i) = (∑ i ∈ W, (b i : ℝ))-
      (2*(∑ e ∈ edgesWithin G W, x e)+∑ e ∈ cutEdges G W, x e) := by
  simp only [slack,Finset.sum_sub_distrib,incident_sum]

theorem eq36 (G : SimpleGraph V) [DecidableRel G.Adj] (b : V → ℕ) (d : Sym2 V → ℕ)
    (x : Sym2 V → ℝ) (W : Finset V) (T : Finset (Sym2 V)) :
    2*(∑ e ∈ edgesWithin G W, x e)+(∑ e ∈ cutEdges G W, x e)+(∑ e ∈ T, x e)+
      (∑ i ∈ W, slack G b x i)+(∑ e ∈ T, ((d e : ℝ)-x e)) =
      (∑ i ∈ W, (b i : ℝ))+∑ e ∈ T, (d e : ℝ) := by
  rw [slack_sum,Finset.sum_sub_distrib]
  ring

theorem eq37 (G : SimpleGraph V) [DecidableRel G.Adj] (b : V → ℕ) (d : Sym2 V → ℕ)
    (x : Sym2 V → ℝ) (W : Finset V) (T : Finset (Sym2 V)) :
    ((∑ i ∈ W, (b i : ℝ))+(∑ e ∈ T, (d e : ℝ))-1)/2 <
        (∑ e ∈ edgesWithin G W, x e)+∑ e ∈ T, x e ↔
      (∑ e ∈ cutEdges G W, x e)+(∑ e ∈ T, (d e : ℝ))-2*(∑ e ∈ T, x e)+
        (∑ i ∈ W, slack G b x i)<1 := by
  rw [slack_sum]
  constructor <;> intro h <;> linarith

end PadbergProof
namespace PadbergProof
open PadbergRao.UpperBound APadbergParity
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem blossom_positive (G : SimpleGraph V) [DecidableRel G.Adj] (b : V → ℕ) (d : Sym2 V → ℕ)
    (x : Sym2 V → ℝ) (hd : ∀ e ∈ G.edgeFinset, 0 < d e) (hx : IsFeasible G b d x)
    (W : Finset V) (T : Finset (Sym2 V)) (hT : T ⊆ cutEdges G W)
    (hcap : (∑ e ∈ cutEdges G W, x e)+(∑ e ∈ T, (d e:ℝ))-2*(∑ e ∈ T, x e)+
        (∑ i ∈ W, slack G b x i)<1) : T ⊆ posEdges G x := by
  classical
  have hdecomp : (∑ e ∈ cutEdges G W, x e)+(∑ e ∈ T, (d e:ℝ))-2*(∑ e ∈ T, x e) =
      (∑ e ∈ cutEdges G W \ T, x e)+(∑ e ∈ T, ((d e:ℝ)-x e)) := by
    have hh := Finset.sum_sdiff hT (f := x)
    rw [Finset.sum_sub_distrib]
    linarith
  rw [hdecomp] at hcap
  have hcut (e : Sym2 V) (he : e ∈ cutEdges G W) : e ∈ G.edgeFinset := (Finset.mem_filter.mp he).1
  have hn : 0 ≤ ∑ e ∈ cutEdges G W \ T, x e :=
    Finset.sum_nonneg (fun e he => (hx.1 e (hcut e (Finset.mem_sdiff.mp he).1)).1)
  have hs : 0 ≤ ∑ i ∈ W, slack G b x i :=
    Finset.sum_nonneg (fun i _ => slack_nonneg G b d x hx i)
  have ht (e : Sym2 V) (he : e ∈ T) : 0 ≤ (d e:ℝ)-x e :=
    sub_nonneg.mpr (hx.1 e (hcut e (hT he))).2
  intro e he
  have heg := hcut e (hT he)
  apply Finset.mem_filter.mpr
  refine ⟨heg,?_⟩
  by_contra hnot
  have hz : x e=0 := le_antisymm (not_lt.mp hnot) (hx.1 e heg).1
  have hle := Finset.single_le_sum ht he
  have hd1 : (1:ℝ) ≤ d e := by exact_mod_cast hd e heg
  rw [hz,sub_zero] at hle
  linarith

theorem main (G : SimpleGraph V) [DecidableRel G.Adj] (b : V → ℕ) (d : Sym2 V → ℕ)
    (x : Sym2 V → ℝ) (hd : ∀ e ∈ G.edgeFinset, 0 < d e) (hx : IsFeasible G b d x)
    (tail : Sym2 V → V) (htail : ∀ e ∈ G.edgeFinset, tail e ∈ e) :
    (∃ (W : Finset V) (T : Finset (Sym2 V)), IsViolatedBlossom G b d x W T) ↔
      ∃ U : Finset (Node G x), IsOddNodeSet G b d x tail U ∧ yCap G b d x tail U<1 := by
  classical
  constructor
  · rintro ⟨W,T,hT,hodd,hviol⟩
    have hcap := (eq37 G b d x W T).mp hviol
    have hp := blossom_positive G b d x hd hx W T hT hcap
    obtain ⟨U,hU,hS,he⟩ := lemma31 G b d x hx tail htail W T
      (fun e he => Finset.mem_inter.mpr ⟨hT he,hp he⟩) hodd
    exact ⟨U,hU,by linarith⟩
  · rintro ⟨U,hU,hcap⟩
    have hh : ∃ Z : Finset (Node G x), IsOddNodeSet G b d x tail Z ∧
        yCap G b d x tail Z<1 ∧ specialNode G x ∉ Z := by
      by_cases hS : specialNode G x ∈ U
      · exact ⟨Uᶜ,(odd_compl_iff G b d x tail U).mpr hU,
          by simpa [cap_compl] using hcap,by simpa using hS⟩
      · exact ⟨U,hU,hcap,hS⟩
    obtain ⟨Z,hZ,hcapZ,hS⟩ := hh
    obtain ⟨W,T,hT,hodd,he⟩ := lemma32 G b d x hd hx tail htail Z hZ hcapZ hS
    exact ⟨W,T,hT,hodd,(eq37 G b d x W T).mpr (he ▸ hcapZ)⟩

end PadbergProof

namespace PadbergRao.UpperBound

/-- Padberg–Rao (1982), p. 77, Theorem 3.1: for a feasible solution `x̄` of (3.1), some blossom
inequality (3.3) is violated by `x̄` (there are `W ⊆ V`, `T ⊆ (W : V − W)` with `b(W) + d(T)` odd
and `x̄(W) + x̄(T) > ½(b(W) + d(T) − 1)`) if and only if an odd minimum cut-set of `G(x̄, d)` has
capacity less than one, i.e. some odd cut-set of `G(x̄, d)` has capacity less than one. -/
theorem _root_.solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (b : V → ℕ) (d : Sym2 V → ℕ) (x : Sym2 V → ℝ)
    (hb : ∀ i, 0 < b i) (hd : ∀ e ∈ G.edgeFinset, 0 < d e) (hx : IsFeasible G b d x)
    (tail : Sym2 V → V) (htail : ∀ e ∈ G.edgeFinset, tail e ∈ e) :
    (∃ (W : Finset V) (T : Finset (Sym2 V)), IsViolatedBlossom G b d x W T) ↔
      ∃ U : Finset (Node G x), IsOddNodeSet G b d x tail U ∧ yCap G b d x tail U < 1 := by
  exact PadbergProof.main G b d x hd hx tail htail

end PadbergRao.UpperBound
