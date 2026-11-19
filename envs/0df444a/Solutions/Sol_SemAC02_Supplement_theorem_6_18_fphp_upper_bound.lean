-- Prove2me | solution 1 for SemAC02.Supplement.theorem_6_18_fphp_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @Henry Yuen
-- created : 2026-11-18T07:46:26.475995+00:00
-- url     : https://prove2.me/submissions/7b63f2d3-ed9a-4b41-8ce5-e0801c945c1c

import Definitions.Def_SemAC02_Supplement_fphpG
import Definitions.Def_SemAC02_Supplement_ACirc
import Definitions.Def_SemAC02_Supplement_IsSemPCRef
import Mathlib

section
-- Inlined Solutions.ArithmeticCircuitBasics

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.ArithmeticCircuitBasics

open MvPolynomial ACirc

lemma toPoly_sum {F V : Type} [CommRing F] (ps : List (F × ACirc F V)) :
    toPoly (.sum ps) = (ps.map (fun p => C p.1*toPoly p.2)).sum := by
  rw [toPoly,List.attach_map_val (f := fun p : F × ACirc F V => C p.1*toPoly p.2)]

lemma toPoly_prod {F V : Type} [CommRing F] (cs : List (ACirc F V)) :
    toPoly (.prod cs) = (cs.map toPoly).prod := by
  rw [toPoly,List.attach_map_val]

lemma mem_fold_union {I : Type} [DecidableEq I] (a : I) (Ss : List (Finset I)) :
    a ∈ Ss.foldr (· ∪ ·) ∅ ↔ ∃ S ∈ Ss, a ∈ S := by
  induction Ss with
  | nil => simp
  | cons S Ss ih => simp only [List.foldr_cons,Finset.mem_union,ih,List.mem_cons]; aesop

lemma mem_subterms_prod {F V : Type} (a : ACirc F V) (cs : List (ACirc F V)) :
    a ∈ subterms (.prod cs) ↔ a = .prod cs ∨ ∃ c ∈ cs, a ∈ subterms c := by
  classical
  rw [subterms,List.attach_map_val (f := fun c : ACirc F V => subterms c),Finset.mem_insert,mem_fold_union]
  simp only [List.mem_map]
  aesop

lemma mem_subterms_sum {F V : Type} (a : ACirc F V) (ps : List (F × ACirc F V)) :
    a ∈ subterms (.sum ps) ↔ a = .sum ps ∨ ∃ p ∈ ps, a ∈ subterms p.2 := by
  classical
  rw [subterms,List.attach_map_val (f := fun p : F × ACirc F V => subterms p.2),Finset.mem_insert,mem_fold_union]
  simp only [List.mem_map]
  aesop

lemma self_mem_subterms {F V : Type} (c : ACirc F V) : c ∈ subterms c := by
  cases c with
  | var i => simp [subterms]
  | const a => simp [subterms]
  | sum ps => exact (mem_subterms_sum _ _).mpr (Or.inl rfl)
  | prod cs => exact (mem_subterms_prod _ _).mpr (Or.inl rfl)

lemma cval_sum {F V : Type} [CommRing F] (ps : List (F × ACirc F V)) (x : V → Bool) :
    cval (.sum ps) x = (ps.map (fun p => p.1*cval p.2 x)).sum := by
  simp only [cval,polyFn,toPoly_sum,map_list_sum,List.map_map,Function.comp_def,map_mul,eval_C]

lemma cval_prod {F V : Type} [CommRing F] (cs : List (ACirc F V)) (x : V → Bool) :
    cval (.prod cs) x = (cs.map (fun c => cval c x)).prod := by
  simp only [cval,polyFn,toPoly_prod,map_list_prod,List.map_map,Function.comp_def]

end SemAC02.Supplement.ArithmeticCircuitBasics
end

section
-- Inlined Solutions.SparseZeroTests

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.SparseZeroTests

open ACirc ArithmeticCircuitBasics

abbrev Sparse (V : Type) := List (ZMod 2 × ACirc (ZMod 2) V)

lemma zero_or_one (a : ZMod 2) : a=0 ∨ a=1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

def complement {V : Type} (b : Sparse V) : ACirc (ZMod 2) V := .sum ((1,.prod [])::b)

def zeroTest {V : Type} (bs : List (Sparse V)) : ACirc (ZMod 2) V :=
  .sum [(1,.prod []),(1,.prod (bs.map complement))]

def Bounded {V : Type} (w : ℕ∞) (b : Sparse V) : Prop := ∀ p∈b, IsMonGate w p.2

lemma complement_layer {V : Type} {w : ℕ∞} (b : Sparse V) (hb : Bounded w b) :
    IsSumOf (IsMonGate w) (complement b) := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨by simp,by simp⟩
  · exact hb p hp

theorem layer {V : Type} {w : ℕ∞} (bs : List (Sparse V)) (hb : ∀ b∈bs, Bounded w b) :
    IsSPSP w (zeroTest bs) := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · simp [IsProdOf]
  · have he : p=(1,.prod (bs.map complement)) := List.mem_singleton.mp hp
    subst p
    intro c hc
    obtain ⟨b,hb',rfl⟩ := List.mem_map.mp hc
    exact complement_layer b (hb b hb')

lemma complement_value {V : Type} (b : Sparse V) (x : V → Bool) :
    cval (complement b) x=1+cval (.sum b) x := by
  simp only [complement,cval_sum,List.map_cons,List.sum_cons,cval_prod,List.map_nil,List.prod_nil,mul_one]

lemma value {V : Type} (bs : List (Sparse V)) (x : V → Bool) :
    cval (zeroTest bs) x=1+(bs.map (fun b => 1+cval (.sum b) x)).prod := by
  simp only [zeroTest,cval_sum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,cval_prod,
    List.prod_nil,mul_one,one_mul,add_zero,List.map_map,Function.comp_def,complement_value]

lemma nil_value {V : Type} (x : V → Bool) : cval (zeroTest ([] : List (Sparse V))) x=0 := by
  simp [value,CharTwo.add_self_eq_zero]

lemma singleton_value {V : Type} (b : Sparse V) (x : V → Bool) :
    cval (zeroTest [b]) x=cval (.sum b) x := by simp [value,CharTwo.add_cancel_left]

lemma cons_value {V : Type} (b : Sparse V) (bs : List (Sparse V)) (x : V → Bool) :
    cval (zeroTest (b::bs)) x=1+(1+cval (.sum b) x)*(1+cval (zeroTest bs) x) := by
  simp only [value,List.map_cons,List.prod_cons,CharTwo.add_cancel_left]

theorem zero_iff {V : Type} (bs : List (Sparse V)) (x : V → Bool) :
    cval (zeroTest bs) x=0 ↔ ∀ b∈bs, cval (.sum b) x=0 := by
  induction bs with
  | nil => simp [nil_value]
  | cons b bs ih =>
    rw [cons_value]
    have h₁ := zero_or_one (cval (.sum b) x)
    have h₂ := zero_or_one (cval (zeroTest bs) x)
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    all_goals simp only [h₁,h₂,add_zero,mul_one,one_mul,CharTwo.add_self_eq_zero,mul_zero,zero_mul,
      zero_add,one_ne_zero,iff_true,iff_false,not_true_eq_false,List.mem_cons,forall_eq_or_imp] at ih ⊢
    all_goals tauto

end SemAC02.Supplement.SparseZeroTests
end

section
-- Inlined Solutions.SemanticCircuitDerivation

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.SemanticCircuitDerivation

open ACirc

inductive Infers {V : Type} (Ω : Set (V → Bool)) (Ax : Set ((V → Bool) → ZMod 2))
    (E : ACirc (ZMod 2) V → Prop) (c : ACirc (ZMod 2) V) : Prop
  | initial (a : (V → Bool) → ZMod 2) (ha : a∈Ax) (h : ∀ x∈Ω, cval c x=a x) : Infers Ω Ax E c
  | zero (h : ∀ x∈Ω, cval c x=0) : Infers Ω Ax E c
  | binary (p q : ACirc (ZMod 2) V) (hp : E p) (hq : E q)
      (h : ∀ x∈Ω, cval p x=0 → cval q x=0 → cval c x=0) : Infers Ω Ax E c

def Valid {V : Type} (Cl : ACirc (ZMod 2) V → Prop) (Ω : Set (V → Bool))
    (Ax : Set ((V → Bool) → ZMod 2)) (π : List (ACirc (ZMod 2) V)) : Prop :=
  (∀ c∈π, Cl c) ∧ ∀ k (hk : k<π.length),
    Infers Ω Ax (fun c => ∃ j<k, π[j]?=some c) π[k]

lemma inference_mono {V : Type} {Ω : Set (V → Bool)} {Ax : Set ((V → Bool) → ZMod 2)}
    {E E' : ACirc (ZMod 2) V → Prop} (hE : ∀ c, E c → E' c)
    {c : ACirc (ZMod 2) V} (h : Infers Ω Ax E c) : Infers Ω Ax E' c := by
  cases h with
  | initial a ha h => exact Infers.initial a ha h
  | zero h => exact Infers.zero h
  | binary p q hp hq h => exact Infers.binary p q (hE p hp) (hE q hq) h

lemma valid_nil {V : Type} (Cl : ACirc (ZMod 2) V → Prop) (Ω : Set (V → Bool))
    (Ax : Set ((V → Bool) → ZMod 2)) : Valid Cl Ω Ax [] := by simp [Valid]

lemma valid_snoc {V : Type} (Cl : ACirc (ZMod 2) V → Prop) (Ω : Set (V → Bool))
    (Ax : Set ((V → Bool) → ZMod 2)) {π : List (ACirc (ZMod 2) V)}
    (hπ : Valid Cl Ω Ax π) (c : ACirc (ZMod 2) V) (hc : Cl c)
    (hi : Infers Ω Ax (fun a => a∈π) c) : Valid Cl Ω Ax (π++[c]) := by
  constructor
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hπ.1 a ha
    · exact (List.mem_singleton.mp ha) ▸ hc
  · intro k hk
    by_cases hkπ : k<π.length
    · rw [List.getElem_append_left hkπ]
      apply inference_mono _ (hπ.2 k hkπ)
      rintro a ⟨j,hjk,hj⟩
      exact ⟨j,hjk,by rw [List.getElem?_append_left (by omega : j<π.length),hj]⟩
    · have he : k=π.length := by simp only [List.length_append,List.length_singleton] at hk; omega
      subst k
      have hec : (π++[c])[π.length]=c := by
        simpa using (List.getElem_append_right' (l₂ := [c]) (i := 0) π (by simp)).symm
      rw [hec]
      apply inference_mono _ hi
      intro a ha
      obtain ⟨j,hj,hval⟩ := List.mem_iff_getElem.mp ha
      exact ⟨j,hj,by rw [List.getElem?_append_left hj,List.getElem?_eq_getElem hj,hval]⟩

theorem refutation {V : Type} (Cl : ACirc (ZMod 2) V → Prop) (Ω : Set (V → Bool))
    (Ax : Set ((V → Bool) → ZMod 2)) (π : List (ACirc (ZMod 2) V))
    (hπ : Valid Cl Ω Ax π) (hfinal : ∃ c, π.getLast?=some c ∧ ∀ x∈Ω, cval c x=1) :
    IsSemPCRef Cl Ω Ax π := by
  refine ⟨hπ.1,?_,hfinal⟩
  intro k hk
  cases hπ.2 k hk with
  | initial a ha h => exact Or.inl ⟨a,ha,h⟩
  | zero h => exact Or.inr (Or.inl h)
  | binary p q hp hq h =>
    obtain ⟨i,hi,hpi⟩ := hp
    obtain ⟨j,hj,hqj⟩ := hq
    have hepi : π[i]'(hi.trans hk)=p := by simpa only [List.getElem?_eq_getElem (hi.trans hk),Option.some.injEq] using hpi
    have heqj : π[j]'(hj.trans hk)=q := by simpa only [List.getElem?_eq_getElem (hj.trans hk),Option.some.injEq] using hqj
    exact Or.inr (Or.inr ⟨i,j,hi,hj,by simpa only [hepi,heqj] using h⟩)

end SemAC02.Supplement.SemanticCircuitDerivation
end

section
-- Inlined Solutions.FunctionalPigeonholeCircuits

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.FunctionalPigeonholeCircuits

open MvPolynomial ACirc ArithmeticCircuitBasics SparseZeroTests SemanticCircuitDerivation

abbrev Vars (n : ℕ) := Edge (completeBip (n+1) n)

def edge {n : ℕ} (u : Fin (n+1)) (v : Fin n) : Vars n := ⟨(u,v),trivial⟩

def mon {V : Type} (xs : List V) : ACirc (ZMod 2) V := .prod (xs.map .var)
def atom {V : Type} (xs : List V) : Sparse V := [(1,mon xs)]

noncomputable def rowSparse {n : ℕ} (u : Fin (n+1)) : Sparse (Vars n) :=
  (1,mon [])::((Finset.univ : Finset (Fin n)).toList.map (fun v => (1,mon [edge u v])))

noncomputable def rowCircuit {n : ℕ} (u : Fin (n+1)) : ACirc (ZMod 2) (Vars n) :=
  .sum [(1,.prod [.sum (rowSparse u)])]

noncomputable def pigeonCircuit {n : ℕ} (u : Fin (n+1)) : ACirc (ZMod 2) (Vars n) :=
  .sum [(1,.prod ((Finset.univ : Finset (Fin n)).toList.map
    (fun v => complement (atom [edge u v]))))]

def functionPairs (n : ℕ) : Finset (Fin n×Fin n) := Finset.univ.filter (fun p => p.1≠p.2)

noncomputable def functionSystem {n : ℕ} (u : Fin (n+1)) : List (Sparse (Vars n)) :=
  (functionPairs n).toList.map (fun p => atom [edge u p.1,edge u p.2])

def holeTriples (n : ℕ) : Finset ((Fin (n+1)×Fin (n+1))×Fin n) :=
  Finset.univ.filter (fun p => p.1.1≠p.1.2)

noncomputable def holeSystem (n : ℕ) : List (Sparse (Vars n)) :=
  (holeTriples n).toList.map (fun p => atom [edge p.1.1 p.2,edge p.1.2 p.2])

noncomputable def finalSystem (n : ℕ) : List (Sparse (Vars n)) :=
  (Finset.univ : Finset (Fin (n+1))).toList.map rowSparse++holeSystem n

lemma mon_value {V : Type} (xs : List V) (x : V → Bool) :
    cval (mon xs) x=(xs.map (boolPt x : V → ZMod 2)).prod := by
  rw [mon,cval_prod]
  simp only [List.map_map,Function.comp_def,cval,polyFn,toPoly,eval_X]

lemma atom_value {V : Type} (xs : List V) (x : V → Bool) :
    cval (.sum (atom xs)) x=(xs.map (boolPt x : V → ZMod 2)).prod := by
  simp only [atom,cval_sum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,one_mul,add_zero,mon_value]

lemma mon_layer {V : Type} (xs : List V) (hx : xs.length≤2) : IsMonGate 2 (mon xs) := by
  constructor
  · change (((xs.map ACirc.var).length : ℕ) : ℕ∞)≤2
    norm_cast
    simpa only [List.length_map] using hx
  · intro c hc
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hc
    trivial

lemma atom_bounded {V : Type} (xs : List V) (hx : xs.length≤2) : Bounded 2 (atom xs) := by
  intro p hp
  have he : p=(1,mon xs) := List.mem_singleton.mp hp
  subst p
  exact mon_layer xs hx

lemma row_bounded {n : ℕ} (u : Fin (n+1)) : Bounded 2 (rowSparse u) := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact mon_layer [] (by simp)
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hp
    exact mon_layer [edge u v] (by simp)

lemma row_layer {n : ℕ} (u : Fin (n+1)) : IsSPSP 2 (rowCircuit u) := by
  intro p hp
  have he := List.mem_singleton.mp hp
  subst p
  intro c hc
  have he := List.mem_singleton.mp hc
  subst c
  exact row_bounded u

lemma pigeon_layer {n : ℕ} (u : Fin (n+1)) : IsSPSP 2 (pigeonCircuit u) := by
  intro p hp
  have he := List.mem_singleton.mp hp
  subst p
  intro c hc
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hc
  exact complement_layer _ (atom_bounded _ (by simp))

lemma row_value {n : ℕ} (u : Fin (n+1)) (x : Vars n → Bool) :
    cval (rowCircuit u) x=cval (.sum (rowSparse u)) x := by
  simp [rowCircuit,cval_sum,cval_prod]

lemma row_sparse_value {n : ℕ} (u : Fin (n+1)) (x : Vars n → Bool) :
    cval (.sum (rowSparse u)) x=1+∑ v : Fin n, (boolPt x (edge u v) : ZMod 2) := by
  rw [rowSparse,cval_sum]
  simp only [List.map_cons,List.sum_cons,mon_value,List.map_nil,List.prod_nil,one_mul,
    List.map_map,Function.comp_def,List.map_cons,List.prod_cons,mul_one]
  rw [Finset.sum_map_toList]

lemma pigeon_value {n : ℕ} (u : Fin (n+1)) (x : Vars n → Bool) :
    cval (pigeonCircuit u) x=∏ v : Fin n, (1+(boolPt x (edge u v) : ZMod 2)) := by
  simp only [pigeonCircuit,cval_sum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    one_mul,add_zero,cval_prod,List.map_map,Function.comp_def,complement_value]
  rw [Finset.prod_map_toList]
  simp only [atom,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,one_mul,add_zero,
    mon_value,List.prod_cons,List.prod_nil,mul_one]

lemma function_bounded {n : ℕ} (u : Fin (n+1)) : ∀ b∈functionSystem u, Bounded 2 b := by
  intro b hb
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hb
  exact atom_bounded _ (by simp)

lemma final_bounded (n : ℕ) : ∀ b∈finalSystem n, Bounded 2 b := by
  intro b hb
  rcases List.mem_append.mp hb with hb | hb
  · obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hb
    exact row_bounded u
  · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hb
    exact atom_bounded _ (by simp)

end SemAC02.Supplement.FunctionalPigeonholeCircuits
end

section
-- Inlined Solutions.FunctionalPigeonholeSemantics

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.FunctionalPigeonholeSemantics

lemma zero_or_one (a : ZMod 2) : a=0 ∨ a=1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem row_sum {n : ℕ} (a : Fin n → ZMod 2)
    (hfun : ∀ i j, i≠j → a i*a j=0) (hpigeon : ∏ i, (1+a i)=0) :
    1+∑ i, a i=0 := by
  classical
  have hex : ∃ i, a i=1 := by
    by_contra hn
    have hz : ∀ i, a i=0 := by
      intro i
      rcases zero_or_one (a i) with hz | ho
      · exact hz
      · exact False.elim (hn ⟨i,ho⟩)
    simp [hz] at hpigeon
  obtain ⟨i,hi⟩ := hex
  have hj : ∀ j, j≠i → a j=0 := by
    intro j hji
    have hh := hfun i j (Ne.symm hji)
    simpa only [hi,one_mul] using hh
  have hsum : ∑ j, a j=1 := by
    rw [Finset.sum_eq_single i]
    · exact hi
    · intro j hj' hji
      exact hj j hji
    · simp
  simp [hsum,CharTwo.add_self_eq_zero]

theorem no_matrix {n : ℕ} (a : Fin (n+1) → Fin n → ZMod 2)
    (hrow : ∀ u, 1+∑ v, a u v=0)
    (hhole : ∀ u u' v, u≠u' → a u v*a u' v=0) : False := by
  classical
  have hex (u : Fin (n+1)) : ∃ v, a u v=1 := by
    by_contra hn
    have hz : ∀ v, a u v=0 := by
      intro v
      rcases zero_or_one (a u v) with hz | ho
      · exact hz
      · exact False.elim (hn ⟨v,ho⟩)
    have hh := hrow u
    simp [hz] at hh
  let f (u : Fin (n+1)) : Fin n := Classical.choose (hex u)
  have hf (u) : a u (f u)=1 := Classical.choose_spec (hex u)
  have hinj : Function.Injective f := by
    intro u u' he
    by_contra hne
    have hh := hhole u u' (f u) hne
    rw [hf u,he,hf u'] at hh
    simp at hh
  have hc := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fin] at hc
  omega

end SemAC02.Supplement.FunctionalPigeonholeSemantics
end

section
-- Inlined Solutions.FunctionalPigeonholeAxioms

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.FunctionalPigeonholeAxioms

open MvPolynomial ACirc ArithmeticCircuitBasics SparseZeroTests SemanticCircuitDerivation FunctionalPigeonholeCircuits

lemma function_input {n : ℕ} (u : Fin (n+1)) (b : Sparse (Vars n)) (hb : b∈functionSystem u)
    (E : ACirc (ZMod 2) (Vars n) → Prop) :
    Infers Set.univ (polyAx (fphpG (completeBip (n+1) n))) E (zeroTest [b]) := by
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hb
  have hne : p.1≠p.2 := (Finset.mem_filter.mp (Finset.mem_toList.mp hp)).2
  let f := xE (completeBip (n+1) n) u p.1 trivial*xE (completeBip (n+1) n) u p.2 trivial
  apply Infers.initial (polyFn f)
  · exact ⟨f,Or.inr (Or.inl ⟨u,p.1,p.2,trivial,trivial,hne,rfl⟩),rfl⟩
  · intro x hx
    simp only [singleton_value,atom_value,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
    simp [f,polyFn,xE,edge]

lemma hole_input {n : ℕ} (b : Sparse (Vars n)) (hb : b∈holeSystem n)
    (E : ACirc (ZMod 2) (Vars n) → Prop) :
    Infers Set.univ (polyAx (fphpG (completeBip (n+1) n))) E (zeroTest [b]) := by
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hb
  have hne : p.1.1≠p.1.2 := (Finset.mem_filter.mp (Finset.mem_toList.mp hp)).2
  let f := xE (completeBip (n+1) n) p.1.1 p.2 trivial*xE (completeBip (n+1) n) p.1.2 p.2 trivial
  apply Infers.initial (polyFn f)
  · exact ⟨f,Or.inr (Or.inr ⟨p.1.1,p.1.2,p.2,trivial,trivial,hne,rfl⟩),rfl⟩
  · intro x hx
    simp only [singleton_value,atom_value,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
    simp [f,polyFn,xE,edge]

lemma pigeon_input {n : ℕ} (u : Fin (n+1)) (E : ACirc (ZMod 2) (Vars n) → Prop) :
    Infers Set.univ (polyAx (fphpG (completeBip (n+1) n))) E (pigeonCircuit u) := by
  let f : MvPolynomial (Vars n) (ZMod 2) := ∏ v : Fin n, (1+X (edge u v))
  have hnbr : PCNonBool.nbrOn (completeBip (n+1) n) Finset.univ u=Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro v hv
    trivial
  have hf : f∈fphpG (completeBip (n+1) n) := by
    apply Or.inl
    refine ⟨u,?_⟩
    change (∏ v : Fin n, (1+X (edge u v)))=∏ v∈
      (PCNonBool.nbrOn (completeBip (n+1) n) Finset.univ u).attach, (1+X (edge u v.1))
    rw [Finset.prod_attach (f := fun v : Fin n => (1+X (edge u v) : MvPolynomial (Vars n) (ZMod 2)))]
    rw [hnbr]
  have hfax : polyFn f∈polyAx (fphpG (completeBip (n+1) n)) := ⟨f,hf,rfl⟩
  apply Infers.initial (polyFn f) hfax
  intro x hx
  rw [pigeon_value]
  simp [f,polyFn]

lemma row_inference {n : ℕ} (u : Fin (n+1)) (E : ACirc (ZMod 2) (Vars n) → Prop)
    (hA : E (zeroTest (functionSystem u))) (hP : E (pigeonCircuit u)) :
    Infers Set.univ (polyAx (fphpG (completeBip (n+1) n))) E (rowCircuit u) := by
  apply Infers.binary _ _ hA hP
  intro x hx hAz hPz
  have hf : ∀ v v' : Fin n, v≠v' →
      (boolPt x (edge u v) : ZMod 2)*boolPt x (edge u v')=0 := by
    intro v v' hne
    have hb : atom [edge u v,edge u v']∈functionSystem u := List.mem_map.mpr
      ⟨(v,v'),Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hne⟩),rfl⟩
    have hh := (zero_iff (functionSystem u) x).mp hAz _ hb
    simpa only [atom_value,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one] using hh
  rw [pigeon_value] at hPz
  rw [row_value,row_sparse_value]
  exact FunctionalPigeonholeSemantics.row_sum (fun v => boolPt x (edge u v)) hf hPz

theorem final_unsat (n : ℕ) : ¬∃ x : Vars n → Bool, ∀ b∈finalSystem n, cval (.sum b) x=0 := by
  rintro ⟨x,hx⟩
  apply FunctionalPigeonholeSemantics.no_matrix (fun u v => boolPt x (edge u v))
  · intro u
    have hb : rowSparse u∈finalSystem n := List.mem_append_left _
      (List.mem_map.mpr ⟨u,Finset.mem_toList.mpr (Finset.mem_univ _),rfl⟩)
    simpa only [row_sparse_value] using hx _ hb
  · intro u u' v hne
    have hb : atom [edge u v,edge u' v]∈finalSystem n := List.mem_append_right _ (List.mem_map.mpr
      ⟨((u,u'),v),Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hne⟩),rfl⟩)
    simpa only [atom_value,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one] using hx _ hb

end SemAC02.Supplement.FunctionalPigeonholeAxioms
end

section
-- Inlined Solutions.ArithmeticSubtermCounts

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.ArithmeticSubtermCounts

open ACirc ArithmeticCircuitBasics Classical

lemma card_fold_union_le {I : Type} (ss : List (Finset I)) :
    (ss.foldr (·∪·) ∅).card≤(ss.map Finset.card).sum := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
    have hh := Finset.card_union_le s (ss.foldr (·∪·) ∅)
    simp only [List.foldr_cons,List.map_cons,List.sum_cons]
    omega

lemma sum_map_le {I : Type} (xs : List I) (f : I → ℕ) (B : ℕ) (h : ∀ i∈xs, f i≤B) :
    (xs.map f).sum≤xs.length*B := by
  induction xs with
  | nil => simp
  | cons i xs ih =>
    have hi := h i (by simp)
    have hh := ih (fun j hj => h j (by simp [hj]))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

lemma sum_card {F V : Type} (ps : List (F×ACirc F V)) :
    (subterms (.sum ps)).card≤1+(ps.map (fun p => (subterms p.2).card)).sum := by
  rw [subterms,List.attach_map_val (f := fun p : F×ACirc F V => subterms p.2)]
  have hh := Finset.card_insert_le (.sum ps) ((ps.map (fun p => subterms p.2)).foldr (·∪·) ∅)
  have hb := card_fold_union_le (ps.map (fun p => subterms p.2))
  simp only [List.map_map,Function.comp_def] at hb
  omega

lemma prod_card {F V : Type} (cs : List (ACirc F V)) :
    (subterms (.prod cs)).card≤1+(cs.map (fun c => (subterms c).card)).sum := by
  rw [subterms,List.attach_map_val]
  have hh := Finset.card_insert_le (.prod cs) ((cs.map subterms).foldr (·∪·) ∅)
  have hb := card_fold_union_le (cs.map subterms)
  simp only [List.map_map,Function.comp_def] at hb
  omega

end SemAC02.Supplement.ArithmeticSubtermCounts
end

section
-- Inlined Solutions.FunctionalPigeonholeSize

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.FunctionalPigeonholeSize

open ACirc ArithmeticCircuitBasics ArithmeticSubtermCounts SparseZeroTests FunctionalPigeonholeCircuits

lemma mon_card {V : Type} (xs : List V) : (subterms (mon xs)).card≤1+xs.length := by
  have hh := prod_card (F := ZMod 2) (xs.map ACirc.var)
  simpa [mon,List.map_map,Function.comp_def,subterms] using hh

lemma complement_card {V : Type} (b : Sparse V) :
    (subterms (complement b)).card≤2+(b.map (fun p => (subterms p.2).card)).sum := by
  have hh := sum_card ((1,.prod [])::b)
  have h0 : (subterms (.prod [] : ACirc (ZMod 2) V)).card=1 := by simp [subterms]
  simp only [List.map_cons,List.sum_cons,h0] at hh
  change (subterms (complement b)).card≤_ at hh
  omega

lemma complement_atom_card {V : Type} (xs : List V) :
    (subterms (complement (atom xs))).card≤3+xs.length := by
  have hh := complement_card (atom xs)
  simp only [atom,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] at hh
  have hm := mon_card xs
  unfold atom
  omega

lemma row_sparse_cost {n : ℕ} (u : Fin (n+1)) :
    ((rowSparse u).map (fun p => (subterms p.2).card)).sum≤1+2*n := by
  have h0 := mon_card ([] : List (Vars n))
  have hh := sum_map_le (Finset.univ : Finset (Fin n)).toList
    (fun v => (subterms (mon [edge u v])).card) 2 (fun v hv => by have hm := mon_card [edge u v]; simpa using hm)
  simp only [Finset.length_toList,Finset.card_univ,Fintype.card_fin] at hh
  simp only [rowSparse,List.map_cons,List.map_map,Function.comp_def,List.sum_cons]
  simp only [List.length_nil,Nat.add_zero] at h0
  omega

lemma row_complement_card {n : ℕ} (u : Fin (n+1)) :
    (subterms (complement (rowSparse u))).card≤2*n+3 := by
  have hh := complement_card (rowSparse u)
  have hr := row_sparse_cost u
  omega

lemma row_card {n : ℕ} (u : Fin (n+1)) : (subterms (rowCircuit u)).card≤2*n+4 := by
  have h₁ := sum_card (rowSparse u)
  have h₂ := prod_card (F := ZMod 2) [.sum (rowSparse u)]
  have h₃ := sum_card [(1,ACirc.prod [.sum (rowSparse u)])]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] at h₂ h₃
  have hc := row_sparse_cost u
  change (subterms (.sum [(1,.prod [.sum (rowSparse u)])])).card≤_
  omega

lemma pigeon_card {n : ℕ} (u : Fin (n+1)) : (subterms (pigeonCircuit u)).card≤4*n+2 := by
  have h₁ := sum_map_le (Finset.univ : Finset (Fin n)).toList
    (fun v => (subterms (complement (atom [edge u v]))).card) 4
    (fun v hv => by simpa using complement_atom_card [edge u v])
  simp only [Finset.length_toList,Finset.card_univ,Fintype.card_fin] at h₁
  have h₂ := prod_card ((Finset.univ : Finset (Fin n)).toList.map (fun v => complement (atom [edge u v])))
  have h₃ := sum_card [(1,ACirc.prod ((Finset.univ : Finset (Fin n)).toList.map (fun v => complement (atom [edge u v]))))]
  simp only [List.map_map,Function.comp_def] at h₂
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] at h₃
  change (subterms (.sum [(1,.prod ((Finset.univ : Finset (Fin n)).toList.map
    (fun v => complement (atom [edge u v]))))])).card≤_
  omega

lemma function_length {n : ℕ} (u : Fin (n+1)) : (functionSystem u).length≤n^2 := by
  simp only [functionSystem,List.length_map,Finset.length_toList]
  have hh := Finset.card_le_card (Finset.filter_subset (fun p : Fin n×Fin n => p.1≠p.2) Finset.univ)
  simpa only [functionPairs,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,pow_two] using hh

lemma function_cost {n : ℕ} (u : Fin (n+1)) :
    ((functionSystem u).map (fun b => (subterms (complement b)).card)).sum≤5*(functionSystem u).length := by
  have hh := sum_map_le (functionSystem u) (fun b => (subterms (complement b)).card) 5 (by
    intro b hb
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hb
    simpa using complement_atom_card [edge u p.1,edge u p.2])
  simpa only [Nat.mul_comm] using hh

lemma hole_length (n : ℕ) : (holeSystem n).length≤(n+1)^2*n := by
  simp only [holeSystem,List.length_map,Finset.length_toList]
  have hh := Finset.card_le_card (Finset.filter_subset
    (fun p : (Fin (n+1)×Fin (n+1))×Fin n => p.1.1≠p.1.2) Finset.univ)
  simpa only [holeTriples,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,pow_two] using hh

lemma final_length (n : ℕ) : (finalSystem n).length≤(n+1)+(n+1)^2*n := by
  have hh := hole_length n
  simpa only [finalSystem,List.length_append,List.length_map,Finset.length_toList,Finset.card_univ,
    Fintype.card_fin] using Nat.add_le_add_left hh (n+1)

lemma final_cost (n : ℕ) :
    ((finalSystem n).map (fun b => (subterms (complement b)).card)).sum≤
      (n+1)*(2*n+3)+5*(n+1)^2*n := by
  have hr := sum_map_le (Finset.univ : Finset (Fin (n+1))).toList
    (fun u => (subterms (complement (rowSparse u))).card) (2*n+3) (fun u hu => row_complement_card u)
  simp only [Finset.length_toList,Finset.card_univ,Fintype.card_fin] at hr
  have hh := sum_map_le (holeSystem n) (fun b => (subterms (complement b)).card) 5 (by
    intro b hb
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hb
    simpa using complement_atom_card [edge p.1.1 p.2,edge p.1.2 p.2])
  have hlen := hole_length n
  simp only [finalSystem,List.map_append,List.sum_append,List.map_map,Function.comp_def]
  nlinarith

end SemAC02.Supplement.FunctionalPigeonholeSize
end

section
-- Inlined Solutions.SparseZeroTestDerivation

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.SparseZeroTestDerivation

open ACirc SparseZeroTests SemanticCircuitDerivation

theorem complete {V : Type} (w : ℕ∞) (Ω : Set (V → Bool)) (Ax : Set ((V → Bool) → ZMod 2))
    (π : List (ACirc (ZMod 2) V)) (hπ : Valid (IsSPSP w) Ω Ax π)
    (bs : List (Sparse V)) (hbs : ∀ b∈bs, Bounded w b)
    (hinput : ∀ b∈bs, Infers Ω Ax (fun c => c∈π) (zeroTest [b])) :
    ∃ ss : List (List (Sparse V)),
      Valid (IsSPSP w) Ω Ax (π++ss.map zeroTest) ∧
      zeroTest bs∈ss.map zeroTest ∧
      (∀ s∈ss, s.Sublist bs) ∧ ss.length≤2*bs.length+1 := by
  induction bs with
  | nil =>
    refine ⟨[[]],?_,by simp,by simp,by simp⟩
    simpa only [List.map_cons,List.map_nil] using valid_snoc (IsSPSP w) Ω Ax hπ (zeroTest [])
      (layer [] (by simp)) (Infers.zero (fun x hx => nil_value x))
  | cons b bs ih =>
    obtain ⟨ss,hvalid,htail,hsub,hlen⟩ := ih (fun c hc => hbs c (by simp [hc]))
      (fun c hc => hinput c (by simp [hc]))
    have hb := hbs b (by simp)
    have hi : Infers Ω Ax (fun c => c∈π++ss.map zeroTest) (zeroTest [b]) :=
      inference_mono (fun c hc => List.mem_append_left _ hc) (hinput b (by simp))
    have hs := valid_snoc (IsSPSP w) Ω Ax hvalid (zeroTest [b]) (layer [b] (by simpa using hb)) hi
    have ht : zeroTest bs∈(π++ss.map zeroTest)++[zeroTest [b]] :=
      List.mem_append_left _ (List.mem_append_right _ htail)
    have hsingle : zeroTest [b]∈(π++ss.map zeroTest)++[zeroTest [b]] := by simp
    have hi' : Infers Ω Ax (fun c => c∈(π++ss.map zeroTest)++[zeroTest [b]]) (zeroTest (b::bs)) :=
      Infers.binary (zeroTest bs) (zeroTest [b]) ht hsingle (by
        intro x hx htailzero hbzero
        apply (zero_iff (b::bs) x).mpr
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · simpa only [singleton_value] using hbzero
        · exact (zero_iff bs x).mp htailzero a ha)
    have hf := valid_snoc (IsSPSP w) Ω Ax hs (zeroTest (b::bs)) (layer (b::bs) hbs) hi'
    refine ⟨ss++[[b],b::bs],?_,by simp,?_,?_⟩
    · simpa only [List.map_append,List.map_cons,List.map_nil,List.append_assoc,List.cons_append,List.nil_append] using hf
    · intro s hs'
      rcases List.mem_append.mp hs' with hs' | hs'
      · exact (hsub s hs').cons b
      · rcases List.mem_cons.mp hs' with rfl | hs'
        · exact List.Sublist.cons₂ b (List.nil_sublist bs)
        · have he : s=b::bs := List.mem_singleton.mp hs'
          subst s
          rfl
    · simp only [List.length_append,List.length_cons,List.length_nil]
      omega

end SemAC02.Supplement.SparseZeroTestDerivation
end

section
-- Inlined Solutions.ArithmeticProofCounts

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.ArithmeticProofCounts

open ACirc

lemma csize_cons {F V : Type} (c : ACirc F V) (π : List (ACirc F V)) :
    csize (c::π) ≤ (subterms c).card+csize π := by
  classical
  unfold csize
  rw [List.toFinset_cons,Finset.biUnion_insert]
  exact Finset.card_union_le _ _

theorem csize_map_le {F V I : Type} (π : List I) (f : I → ACirc F V) (B : ℕ)
    (hf : ∀ i ∈ π, (subterms (f i)).card ≤ B) : csize (π.map f) ≤ π.length*B := by
  induction π with
  | nil => simp [csize]
  | cons i π ih =>
    have h := (csize_cons (f i) (π.map f)).trans (Nat.add_le_add
      (hf i (by simp)) (ih (fun j hj => hf j (by simp [hj]))))
    simpa only [List.map_cons,List.length_cons,Nat.add_mul,Nat.one_mul,Nat.add_comm] using h

theorem topS_le_topOcc {F V : Type} [CommRing F] (Ω : Set (V → Bool)) (π : List (ACirc F V)) :
    topS Ω π ≤ topOcc π := by
  classical
  let ts := π.flatMap topTerms
  let G : Finset (Ω → F) := ts.toFinset.image (fun t => fun x : Ω => cval t x.1)
  have hsub : {g : Ω → F | g ≠ 0 ∧ ∃ c ∈ π, ∃ t ∈ topTerms c, g = fun x => cval t x.1} ⊆
      (↑G : Set (Ω → F)) := by
    rintro g ⟨hg,c,hc,t,ht,rfl⟩
    exact Finset.mem_image.mpr ⟨t,List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨c,hc,ht⟩),rfl⟩
  calc
    _ ≤ (↑G : Set (Ω → F)).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet G)
    _ = G.card := Set.ncard_coe_finset _
    _ ≤ ts.toFinset.card := Finset.card_image_le
    _ ≤ ts.length := List.toFinset_card_le ts
    _ = _ := by simp only [ts,List.length_flatMap,topOcc]

end SemAC02.Supplement.ArithmeticProofCounts
end

section
-- Inlined Solutions.SparseZeroTestSize

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.SparseZeroTestSize

open ACirc ArithmeticCircuitBasics SparseZeroTests Classical

noncomputable def baseNodes {V : Type} (bs : List (Sparse V)) : Finset (ACirc (ZMod 2) V) :=
  (bs.map (fun b => subterms (complement b))).foldr (·∪·) ∅

lemma base_card {V : Type} (bs : List (Sparse V)) :
    (baseNodes bs).card≤(bs.map (fun b => (subterms (complement b)).card)).sum := by
  induction bs with
  | nil => simp [baseNodes]
  | cons b bs ih =>
    have hh := Finset.card_union_le (subterms (complement b)) (baseNodes bs)
    simp only [baseNodes,List.map_cons,List.foldr_cons,List.sum_cons] at *
    omega

lemma mem_base {V : Type} (bs : List (Sparse V)) (b : Sparse V) (hb : b∈bs)
    (c : ACirc (ZMod 2) V) (hc : c∈subterms (complement b)) : c∈baseNodes bs := by
  apply (mem_fold_union c _).mpr
  exact ⟨_,List.mem_map.mpr ⟨b,hb,rfl⟩,hc⟩

lemma subterms_test {V : Type} (bs s : List (Sparse V)) (hs : s.Sublist bs)
    (c : ACirc (ZMod 2) V) (hc : c∈subterms (zeroTest s)) :
    c=zeroTest s ∨ c=.prod (s.map complement) ∨ c=.prod [] ∨ c∈baseNodes bs := by
  rcases (mem_subterms_sum c _).mp hc with he | ⟨p,hp,hpc⟩
  · exact Or.inl he
  · rcases List.mem_cons.mp hp with rfl | hp
    · have he : c=.prod [] := by simpa only [subterms,List.attach_nil,List.map_nil,List.foldr_nil,
        Finset.insert_empty,Finset.mem_singleton] using hpc
      exact Or.inr (Or.inr (Or.inl he))
    · have he : p=(1,.prod (s.map complement)) := List.mem_singleton.mp hp
      subst p
      rcases (mem_subterms_prod c _).mp hpc with he | ⟨a,ha,hca⟩
      · exact Or.inr (Or.inl he)
      · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
        exact Or.inr (Or.inr (Or.inr (mem_base bs b (hs.subset hb) c hca)))

lemma csize_append {V : Type} (π ρ : List (ACirc (ZMod 2) V)) : csize (π++ρ)≤csize π+csize ρ := by
  classical
  unfold csize
  rw [List.toFinset_append,Finset.union_biUnion]
  exact Finset.card_union_le _ _

theorem csize_tests {V : Type} (bs : List (Sparse V)) (ss : List (List (Sparse V)))
    (hss : ∀ s∈ss, s.Sublist bs) :
    csize (ss.map zeroTest)≤2*ss.length+1+(bs.map (fun b => (subterms (complement b)).card)).sum := by
  classical
  let R₁ := ss.toFinset.image zeroTest
  let R₂ := ss.toFinset.image (fun s => ACirc.prod (s.map complement))
  let U := ((R₁∪R₂)∪{ACirc.prod []})∪baseNodes bs
  have hsub : (ss.map zeroTest).toFinset.biUnion subterms⊆U := by
    intro c hc
    obtain ⟨a,ha,hca⟩ := Finset.mem_biUnion.mp hc
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    rcases subterms_test bs s (hss s hs) c hca with rfl | rfl | rfl | hc
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨s,List.mem_toFinset.mpr hs,rfl⟩)))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨s,List.mem_toFinset.mpr hs,rfl⟩)))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))
    · exact Finset.mem_union_right _ hc
  have hR₁ : R₁.card ≤ ss.length := Finset.card_image_le.trans (List.toFinset_card_le ss)
  have hR₂ : R₂.card ≤ ss.length := Finset.card_image_le.trans (List.toFinset_card_le ss)
  have hU : U.card≤R₁.card+R₂.card+1+(baseNodes bs).card := by
    have h₁ := Finset.card_union_le R₁ R₂
    have h₂ := Finset.card_union_le (R₁∪R₂) ({ACirc.prod []} : Finset (ACirc (ZMod 2) V))
    have h₃ := Finset.card_union_le ((R₁∪R₂)∪{ACirc.prod []}) (baseNodes bs)
    simp only [Finset.card_singleton] at h₂
    dsimp only [U]
    omega
  have hc := (Finset.card_le_card hsub).trans hU
  have hb := base_card bs
  change ((ss.map zeroTest).toFinset.biUnion subterms).card≤_
  omega

end SemAC02.Supplement.SparseZeroTestSize
end

section
-- Inlined Solutions.SparseZeroTestCompletion

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.SparseZeroTestCompletion

open ACirc SparseZeroTests SemanticCircuitDerivation SparseZeroTestSize

theorem complete {V : Type} (w : ℕ∞) (Ω : Set (V → Bool)) (Ax : Set ((V → Bool) → ZMod 2))
    (π : List (ACirc (ZMod 2) V)) (hπ : Valid (IsSPSP w) Ω Ax π)
    (bs : List (Sparse V)) (hbs : ∀ b∈bs, Bounded w b)
    (hinput : ∀ b∈bs, Infers Ω Ax (fun c => c∈π) (zeroTest [b])) :
    ∃ ρ : List (ACirc (ZMod 2) V), Valid (IsSPSP w) Ω Ax ρ ∧ π.IsPrefix ρ ∧
      zeroTest bs∈ρ ∧ csize ρ≤csize π+4*bs.length+3+
        (bs.map (fun b => (subterms (complement b)).card)).sum := by
  obtain ⟨ss,hss,hmem,hsub,hlen⟩ := SparseZeroTestDerivation.complete w Ω Ax π hπ bs hbs hinput
  refine ⟨π++ss.map zeroTest,hss,⟨_,rfl⟩,List.mem_append_right _ hmem,?_⟩
  have hh := (csize_append π (ss.map zeroTest)).trans
    (Nat.add_le_add_left (csize_tests bs ss hsub) _)
  omega

lemma input_from_value {V : Type} {Ω : Set (V → Bool)} {Ax : Set ((V → Bool) → ZMod 2)}
    {π : List (ACirc (ZMod 2) V)} (b : Sparse V)
    (h : ∃ c∈π, ∀ x∈Ω, cval c x=cval (.sum b) x) :
    Infers Ω Ax (fun c => c∈π) (zeroTest [b]) := by
  obtain ⟨c,hc,hval⟩ := h
  exact Infers.binary c c hc hc (by
    intro x hx hz _
    rw [singleton_value,←hval x hx,hz])

lemma csize_snoc_of_mem {V : Type} (π : List (ACirc (ZMod 2) V)) (c : ACirc (ZMod 2) V)
    (hc : c∈π) : csize (π++[c])=csize π := by
  classical
  unfold csize
  congr 1
  simp only [List.toFinset_append,List.toFinset_cons,List.toFinset_nil,Finset.insert_empty,
    Finset.union_singleton,Finset.insert_eq_of_mem (List.mem_toFinset.mpr hc)]

theorem refute {V : Type} (w : ℕ∞) (Ω : Set (V → Bool)) (Ax : Set ((V → Bool) → ZMod 2))
    (π : List (ACirc (ZMod 2) V)) (hπ : Valid (IsSPSP w) Ω Ax π)
    (bs : List (Sparse V)) (hbs : ∀ b∈bs, Bounded w b)
    (hinput : ∀ b∈bs, Infers Ω Ax (fun c => c∈π) (zeroTest [b]))
    (hunsat : ¬∃ x∈Ω, ∀ b∈bs, cval (.sum b) x=0) :
    ∃ ρ : List (ACirc (ZMod 2) V), IsSemPCRef (IsSPSP w) Ω Ax ρ ∧ π.IsPrefix ρ ∧
      csize ρ≤csize π+4*bs.length+3+(bs.map (fun b => (subterms (complement b)).card)).sum := by
  obtain ⟨ρ,hρ,hpre,hmem,hsize⟩ := complete w Ω Ax π hπ bs hbs hinput
  have hone : ∀ x∈Ω, cval (zeroTest bs) x=1 := by
    intro x hx
    rcases zero_or_one (cval (zeroTest bs) x) with hz | ho
    · exact False.elim (hunsat ⟨x,hx,(zero_iff bs x).mp hz⟩)
    · exact ho
  have hv := valid_snoc (IsSPSP w) Ω Ax hρ (zeroTest bs) (layer bs hbs)
    (Infers.binary _ _ hmem hmem (fun _ _ hz _ => hz))
  refine ⟨ρ++[zeroTest bs],SemanticCircuitDerivation.refutation _ _ _ _ hv
    ⟨zeroTest bs,by simp,hone⟩,hpre.trans ⟨[zeroTest bs],rfl⟩,?_⟩
  rwa [csize_snoc_of_mem ρ _ hmem]

end SemAC02.Supplement.SparseZeroTestCompletion
end

section
-- Inlined Solutions.SemanticCircuitIteration

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.SemanticCircuitIteration

open ACirc SemanticCircuitDerivation

lemma csize_snoc {V : Type} (π : List (ACirc (ZMod 2) V)) (c : ACirc (ZMod 2) V) :
    csize (π++[c])≤csize π+(subterms c).card := by
  have hh := SparseZeroTestSize.csize_append π [c]
  simpa [csize] using hh

theorem iterate {V I : Type} (Cl : ACirc (ZMod 2) V → Prop) (Ω : Set (V → Bool))
    (Ax : Set ((V → Bool) → ZMod 2)) (xs : List I) (target : I → ACirc (ZMod 2) V) (B : ℕ)
    (hstep : ∀ i∈xs, ∀ π : List (ACirc (ZMod 2) V), Valid Cl Ω Ax π →
      ∃ ρ, Valid Cl Ω Ax ρ ∧ π.IsPrefix ρ ∧ target i∈ρ ∧ csize ρ≤csize π+B)
    (π : List (ACirc (ZMod 2) V)) (hπ : Valid Cl Ω Ax π) :
    ∃ ρ, Valid Cl Ω Ax ρ ∧ π.IsPrefix ρ ∧ (∀ i∈xs, target i∈ρ) ∧
      csize ρ≤csize π+xs.length*B := by
  induction xs generalizing π with
  | nil => exact ⟨π,hπ,List.prefix_refl _,by simp,by simp⟩
  | cons i xs ih =>
    obtain ⟨ρ,hρ,hpre,hmem,hsize⟩ := hstep i (by simp) π hπ
    obtain ⟨σ,hσ,hpre',hmem',hsize'⟩ := ih (fun j hj => hstep j (by simp [hj])) ρ hρ
    refine ⟨σ,hσ,hpre.trans hpre',?_,?_⟩
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hpre'.subset hmem
      · exact hmem' j hj
    · simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega

lemma monGate_mono {V : Type} {v w : ℕ∞} (hvw : v≤w) (c : ACirc (ZMod 2) V)
    (hc : IsMonGate v c) : IsMonGate w c := by
  cases c with
  | var i => exact hc.elim
  | const a => exact hc.elim
  | sum ps => exact hc.elim
  | prod cs => exact ⟨hc.1.trans hvw,hc.2⟩

lemma spsp_mono {V : Type} {v w : ℕ∞} (hvw : v≤w) (c : ACirc (ZMod 2) V)
    (hc : IsSPSP v c) : IsSPSP w c := by
  have hsum (P Q : ACirc (ZMod 2) V → Prop) (h : ∀ a, P a → Q a)
      (a : ACirc (ZMod 2) V) (ha : IsSumOf P a) : IsSumOf Q a := by
    cases a with
    | sum ps => exact fun p hp => h p.2 (ha p hp)
    | var i => exact ha.elim
    | const b => exact ha.elim
    | prod cs => exact ha.elim
  have hprod (P Q : ACirc (ZMod 2) V → Prop) (h : ∀ a, P a → Q a)
      (a : ACirc (ZMod 2) V) (ha : IsProdOf P a) : IsProdOf Q a := by
    cases a with
    | prod cs => exact fun a ha' => h a (ha a ha')
    | var i => exact ha.elim
    | const b => exact ha.elim
    | sum ps => exact ha.elim
  exact hsum _ _ (fun a ha => hprod _ _
    (fun b hb => hsum _ _ (monGate_mono hvw) b hb) a ha) c hc

end SemAC02.Supplement.SemanticCircuitIteration
end

section
-- Inlined Solutions.FunctionalPigeonholeRows

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.FunctionalPigeonholeRows

open ACirc SparseZeroTests SemanticCircuitDerivation FunctionalPigeonholeCircuits FunctionalPigeonholeSize

theorem one_row {n : ℕ} (u : Fin (n+1)) (π : List (ACirc (ZMod 2) (Vars n)))
    (hπ : Valid (IsSPSP 2) Set.univ (polyAx (fphpG (completeBip (n+1) n))) π) :
    ∃ ρ, Valid (IsSPSP 2) Set.univ (polyAx (fphpG (completeBip (n+1) n))) ρ ∧
      π.IsPrefix ρ ∧ rowCircuit u∈ρ ∧ csize ρ≤csize π+(9*n^2+6*n+11) := by
  obtain ⟨ρ,hρ,hpre,hA,hsize⟩ := SparseZeroTestCompletion.complete 2 Set.univ
    (polyAx (fphpG (completeBip (n+1) n))) π hπ (functionSystem u) (function_bounded u)
    (fun b hb => FunctionalPigeonholeAxioms.function_input u b hb _)
  have hσ := valid_snoc _ _ _ hρ (pigeonCircuit u) (pigeon_layer u)
    (FunctionalPigeonholeAxioms.pigeon_input u _)
  have hA' : zeroTest (functionSystem u)∈ρ++[pigeonCircuit u] := List.mem_append_left _ hA
  have hP : pigeonCircuit u∈ρ++[pigeonCircuit u] := by simp
  have hτ := valid_snoc _ _ _ hσ (rowCircuit u) (row_layer u)
    (FunctionalPigeonholeAxioms.row_inference u _ hA' hP)
  refine ⟨(ρ++[pigeonCircuit u])++[rowCircuit u],hτ,
    hpre.trans ((show ρ.IsPrefix (ρ++[pigeonCircuit u]) from ⟨_,rfl⟩).trans ⟨_,rfl⟩),by simp,?_⟩
  have h₁ := SemanticCircuitIteration.csize_snoc ρ (pigeonCircuit u)
  have h₂ := SemanticCircuitIteration.csize_snoc (ρ++[pigeonCircuit u]) (rowCircuit u)
  have hρsize : csize ρ≤csize π+9*(functionSystem u).length+3 := by
    calc
      _ ≤ csize π+4*(functionSystem u).length+3+
          ((functionSystem u).map (fun b => (subterms (complement b)).card)).sum := hsize
      _ ≤ csize π+4*(functionSystem u).length+3+5*(functionSystem u).length :=
        Nat.add_le_add_left (function_cost u) _
      _ = _ := by ring
  have hlen := function_length u
  have hpc := pigeon_card u
  have hrc := row_card u
  omega

theorem all_rows (n : ℕ) :
    ∃ π : List (ACirc (ZMod 2) (Vars n)),
      Valid (IsSPSP 2) Set.univ (polyAx (fphpG (completeBip (n+1) n))) π ∧
      (∀ u : Fin (n+1), rowCircuit u∈π) ∧
      csize π≤(n+1)*(9*n^2+6*n+11) := by
  obtain ⟨π,hπ,_,hrows,hsize⟩ := SemanticCircuitIteration.iterate (IsSPSP 2) Set.univ
    (polyAx (fphpG (completeBip (n+1) n))) (Finset.univ : Finset (Fin (n+1))).toList
    rowCircuit (9*n^2+6*n+11) (fun u hu => one_row u) [] (valid_nil _ _ _)
  refine ⟨π,hπ,fun u => hrows u (by simp),?_⟩
  simpa [csize] using hsize

end SemAC02.Supplement.FunctionalPigeonholeRows
end

section
-- Inlined Solutions.FunctionalPigeonholeUpper

set_option maxHeartbeats 2000000

namespace SemAC02.Supplement.FunctionalPigeonholeUpper

open ACirc SparseZeroTests SemanticCircuitDerivation FunctionalPigeonholeCircuits FunctionalPigeonholeSize

theorem cubic (n : ℕ) (hn : 1≤n) :
    ∃ π : List (ACirc (ZMod 2) (Vars n)),
      IsSemPCRef (IsSPSP 2) Set.univ (polyAx (fphpG (completeBip (n+1) n))) π ∧
      csize π≤128*n^3 := by
  obtain ⟨π,hπ,hrows,hsize⟩ := FunctionalPigeonholeRows.all_rows n
  have hi : ∀ b∈finalSystem n,
      Infers Set.univ (polyAx (fphpG (completeBip (n+1) n))) (fun c => c∈π) (zeroTest [b]) := by
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hb
      exact SparseZeroTestCompletion.input_from_value _ ⟨rowCircuit u,hrows u,fun x hx => row_value u x⟩
    · exact FunctionalPigeonholeAxioms.hole_input b hb _
  obtain ⟨ρ,hρ,_,hρsize⟩ := SparseZeroTestCompletion.refute 2 Set.univ
    (polyAx (fphpG (completeBip (n+1) n))) π hπ (finalSystem n) (final_bounded n) hi (by
      rintro ⟨x,hx,hzero⟩
      exact FunctionalPigeonholeAxioms.final_unsat n ⟨x,hzero⟩)
  refine ⟨ρ,hρ,?_⟩
  have hlen := final_length n
  have hcost := final_cost n
  have h13 : n≤n^3 := by simpa only [pow_one] using (Nat.pow_le_pow_right hn (by omega : 1≤3))
  have h23 : n^2≤n^3 := Nat.pow_le_pow_right hn (by omega)
  have h03 : 1≤n^3 := Nat.one_le_pow _ _ hn
  nlinarith

theorem upper_bound :
    ∃ K : ℝ, ∀ n : ℕ, 1≤n →
      ∃ π : List (ACirc (ZMod 2) (Edge (completeBip (n+1) n))),
        IsSemPCRef (IsSPSP 2) Set.univ (polyAx (fphpG (completeBip (n+1) n))) π ∧
        (csize π : ℝ)≤K*(n : ℝ)^3*Real.log ((n : ℝ)+1) ∧
        ∀ w : ℕ, 2≤w → ∀ c∈π, IsSPSP (w : ℕ∞) c := by
  have hlog2 : (0 : ℝ)<Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨128/Real.log 2,?_⟩
  intro n hn
  obtain ⟨π,hπ,hsize⟩ := cubic n hn
  refine ⟨π,hπ,?_,?_⟩
  · have hlog : Real.log (2 : ℝ)≤Real.log ((n : ℝ)+1) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast (show 2≤n+1 by omega))
    have hfactor : (1 : ℝ)≤Real.log ((n : ℝ)+1)/Real.log 2 :=
      (le_div_iff₀ hlog2).mpr (by simpa using hlog)
    calc
      _ ≤ 128*(n : ℝ)^3 := by exact_mod_cast hsize
      _ ≤ 128*(n : ℝ)^3*(Real.log ((n : ℝ)+1)/Real.log 2) :=
        le_mul_of_one_le_right (by positivity) hfactor
      _ = _ := by ring
  · intro w hw c hc
    exact SemanticCircuitIteration.spsp_mono (by exact_mod_cast hw) c (hπ.1 c hc)

end SemAC02.Supplement.FunctionalPigeonholeUpper
end

open SemAC02.Supplement SemAC02.Supplement.ACirc

theorem solution :
    ∃ K : ℝ, ∀ n : ℕ, 1 ≤ n →
      ∃ π : List (ACirc (ZMod 2) (Edge (completeBip (n + 1) n))),
        IsSemPCRef (IsSPSP 2) Set.univ (polyAx (fphpG (completeBip (n + 1) n))) π ∧
        (csize π : ℝ) ≤ K * (n : ℝ) ^ 3 * Real.log ((n : ℝ) + 1) ∧
        ∀ w : ℕ, 2 ≤ w → ∀ c ∈ π, IsSPSP (w : ℕ∞) c  := by
  exact SemAC02.Supplement.FunctionalPigeonholeUpper.upper_bound
