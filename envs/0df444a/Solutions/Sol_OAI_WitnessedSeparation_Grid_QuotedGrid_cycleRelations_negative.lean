-- Prove2me | solution 1 for OAI.WitnessedSeparation.Grid.QuotedGrid.cycleRelations_negative
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T00:23:04.293708+00:00
-- url     : https://prove2.me/submissions/f4f1c706-806b-4e40-a5b5-e31e00eeaf96

import Mathlib
import Definitions.Def_WitnessedChoice
import Definitions.Def_OAIQ4Wc000

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_GridAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WitnessedSeparation.Grid

noncomputable section

open Support

variable {n : ℕ}

theorem pairing_boundary (φ : Vertex n → Scalar) (z : Edge n → Scalar) :
    pairing φ (boundary z) = pairing (gradient φ) z := by
  have hb : boundary z = ∑ e : Edge n, z e •
      ((Pi.single (head e) (1 : Scalar) : Vertex n → Scalar) - Pi.single (tail e) 1) := rfl
  rw [hb]
  simp only [map_sum, map_smul, map_sub, pairing_single, mul_one, smul_eq_mul]
  change (∑ e, z e * (φ (head e) - φ (tail e))) =
    ∑ e, (φ (head e) - φ (tail e)) * z e
  apply Finset.sum_congr rfl
  intro e _
  ring

@[simp] theorem pairing_gradient_flow (φ : Vertex n → Scalar) (k : FlowSpace n) :
    pairing (gradient φ) k.val = 0 := by
  rw [← pairing_boundary, LinearMap.mem_ker.mp k.property, map_zero]

end



open Support

end WitnessedSeparation.Grid

end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_GuardedProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section


namespace WitnessedChoice.BGS
open Classical WitnessedSeparation WitnessedSeparation.Hereditary


namespace QuotedTerm

section

variable {n : ℕ}

variable {A : Type} [Fintype A] (S : Input A) (env : Fin n → HF A)

omit [Fintype A] in
lemma cardHF_singleton (a : HF A) : cardHF (Hereditary.singleton a) = ordinal 1 := by
  simp [cardHF,Hereditary.singleton]

omit [Fintype A] in
lemma cardHF_double_ne (a b : HF A) (h : a ≠ b) :
    cardHF (Hereditary.double a b) ≠ ordinal 1 := by
  simp only [cardHF,Hereditary.double,elements_ofFinset,Finset.card_insert_of_notMem
    (show a ∉ ({b} : Finset (HF A)) by simpa),Finset.card_singleton]
  exact fun hh => by have := ordinal_injective hh; contradiction

@[simp] lemma meaning_fst_pair (a b : QuotedTerm n) :
    (fst (a.pair b)).meaning S env = a.meaning S env := by
  let x := a.meaning S env
  let y := b.meaning S env
  simp only [fst,meaning_unique,meaning_union,meaning_filter,meaning_pair,
    QuotedFormula.meaning_eq,meaning_card,meaning_var,Fin.cons_zero,meaning_nat]
  change uniqueHF (unionHF (ofFinset ((elements (Hereditary.pair x y)).filter
    (fun z => cardHF z = ordinal 1)))) = x
  have hf : (elements (Hereditary.pair x y)).filter (fun z => cardHF z = ordinal 1) =
      {Hereditary.singleton x} := by
    by_cases h : x = y
    · rw [h]
      simp [Hereditary.pair,Hereditary.double,Hereditary.singleton,cardHF]
    · ext z
      simp only [Hereditary.pair,Hereditary.double,elements_ofFinset,Finset.mem_filter,
        Finset.mem_insert,Finset.mem_singleton]
      constructor
      · rintro ⟨hz,hc⟩
        rcases hz with rfl | rfl
        · rfl
        · exact (cardHF_double_ne x y h hc).elim
      · intro hz
        subst z
        exact ⟨Or.inl rfl,cardHF_singleton x⟩
  rw [hf]
  simp only [unionHF,elements_ofFinset,Finset.singleton_biUnion,Hereditary.singleton]
  exact uniqueHF_singleton x

@[simp] lemma meaning_snd_pair (a b : QuotedTerm n) :
    (snd (a.pair b)).meaning S env = b.meaning S env := by
  simp only [snd,cond,QuotedFormula.meaning_eq,meaning_card,meaning_union,meaning_pair,
    meaning_nat,meaning_fst_pair,meaning_diff,meaning_singleton,meaning_unique]
  let x := a.meaning S env
  let y := b.meaning S env
  have hu : unionHF (Hereditary.pair x y) = Hereditary.double x y := by
    simp [unionHF,Hereditary.pair,Hereditary.double,Hereditary.singleton]
  change (if cardHF (unionHF (Hereditary.pair x y)) = ordinal 1 then x else
    uniqueHF (ofFinset ((elements (unionHF (Hereditary.pair x y))).filter
      fun z => z ∉ elements (Hereditary.singleton x)))) = y
  rw [hu]
  by_cases h : x = y
  · rw [h]
    simp [cardHF,Hereditary.double]
  · rw [ite_eq_right (cardHF_double_ne x y h)]
    have hf : (elements (Hereditary.double x y)).filter
        (fun z => z ∉ elements (Hereditary.singleton x)) = {y} := by
      ext z
      simp [Hereditary.double,Hereditary.singleton]
      aesop
    rw [hf]
    exact uniqueHF_singleton y

end

end QuotedTerm


end WitnessedChoice.BGS

end

end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_TreeElimination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

variable {A : Type}

namespace FiniteIteration

variable {X : Type}

lemma run_subset (f : Finset X → Finset X) (C : Finset X)
    (hC : ∀ s, s ⊆ C → f s ⊆ C) (k : ℕ) : run f k ⊆ C := by
  induction k with
  | zero => exact Finset.empty_subset C
  | succ k ih => exact hC _ ih

lemma run_step (f : Finset X → Finset X) (hi : ∀ s, s ⊆ f s) (k : ℕ) :
    run f k ⊆ run f (k+1) := hi _

lemma run_comparison (f : Finset X → Finset X) (hi : ∀ s, s ⊆ f s)
    {k : ℕ} (h : ∀ i < k, run f i ≠ run f (i+1)) : k ≤ (run f k).card := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    have hk := h k (by omega)
    have hc := Finset.card_lt_card ((Finset.ssubset_iff_subset_ne).mpr ⟨run_step f hi k,hk⟩)
    have hh := ih (fun i hi => h i (by omega))
    omega

lemma exists_stationary (f : Finset X → Finset X) (C : Finset X)
    (hi : ∀ s, s ⊆ f s) (hC : ∀ s, s ⊆ C → f s ⊆ C) :
    ∃ t ≤ C.card, run f t = run f (t+1) := by
  by_contra hn
  push Not at hn
  have hs : ∀ i < C.card+1, run f i ≠ run f (i+1) := fun i h => hn i (by omega)
  have hc := run_comparison f hi hs
  have hb := Finset.card_le_card (run_subset f C hC (C.card+1))
  omega

lemma run_stationary_after (f : Finset X → Finset X) {t : ℕ}
    (ht : run f t = run f (t+1)) (k : ℕ) (hk : t ≤ k) : run f k = run f t := by
  obtain ⟨l,rfl⟩ := Nat.exists_eq_add_of_le hk
  induction l with
  | zero => simp
  | succ l ih =>
    change f (run f (t+l)) = run f t
    rw [ih (by omega)]
    exact ht.symm

lemma run_fixed (f : Finset X → Finset X) (C : Finset X)
    (hi : ∀ s, s ⊆ f s) (hC : ∀ s, s ⊆ C → f s ⊆ C) :
    f (run f C.card) = run f C.card := by
  obtain ⟨t,ht,he⟩ := exists_stationary f C hi hC
  exact (run_stationary_after f he (C.card+1) (by omega)).trans
    (run_stationary_after f he C.card ht).symm

lemma run_least (f : Finset X → Finset X) (hm : Monotone f)
    (s : Finset X) (hs : f s ⊆ s) (k : ℕ) : run f k ⊆ s := by
  induction k with
  | zero => exact Finset.empty_subset s
  | succ k ih => exact (hm ih).trans hs

end FiniteIteration

end

end WitnessedChoice.BGS



namespace WitnessedChoice.BGS.BFS

noncomputable section

open Classical SimpleGraph

variable {V : Type} [Fintype V]

lemma update_inflationary (G : SimpleGraph V) (k : ℕ) (R : Finset (Item V k)) : R ⊆ update G k R := by
  intro x hx
  exact (mem_update G k R x).mpr (Or.inl (Or.inl hx))

lemma update_mono (G : SimpleGraph V) (k : ℕ) : Monotone (update G k) := by
  intro R S h x hx
  rcases (mem_update G k R x).mp hx with (hx|hx)|⟨u,j,hm,he,ha⟩
  · exact (mem_update G k S x).mpr (Or.inl (Or.inl (h hx)))
  · exact (mem_update G k S x).mpr (Or.inl (Or.inr hx))
  · exact (mem_update G k S x).mpr (Or.inr ⟨u,j,h hm,he,ha⟩)

lemma closure_fixed (G : SimpleGraph V) (k : ℕ) : update G k (closure G k) = closure G k := by
  exact FiniteIteration.run_fixed (update G k) Finset.univ (update_inflationary G k)
    (fun _ _ => Finset.subset_univ _)

lemma closure_nil (G : SimpleGraph V) (k : ℕ) (v : V) : (v,v,0) ∈ closure G k := by
  rw [← closure_fixed]
  exact (mem_update _ _ _ _).mpr (Or.inl (Or.inr ⟨rfl,rfl⟩))

lemma closure_step (G : SimpleGraph V) {k : ℕ} {v u w : V} {i j : Fin (k+1)}
    (hm : (v,u,j) ∈ closure G k) (he : i.val = j.val+1) (ha : u=w ∨ G.Adj u w) :
    (v,w,i) ∈ closure G k := by
  rw [← closure_fixed]
  exact (mem_update _ _ _ _).mpr (Or.inr ⟨u,j,hm,he,ha⟩)

lemma update_good (G : SimpleGraph V) (k : ℕ) : update G k (good G k) ⊆ good G k := by
  intro x hx
  rcases x with ⟨v,w,i⟩
  simp only [good,Finset.mem_filter,Finset.mem_univ,true_and]
  rcases (mem_update _ _ _ _).mp hx with (hx|⟨hvw,hi⟩)|⟨u,j,hj,he,(hu|ha)⟩
  · simpa only [good,Finset.mem_filter,Finset.mem_univ,true_and] using hx
  · dsimp at hvw hi
    subst w
    exact ⟨.nil,by simp⟩
  · dsimp at hu he
    subst w
    obtain ⟨p,hp⟩ := (show ∃ p : G.Walk v u, p.length ≤ j.val by simpa [good] using hj)
    exact ⟨p,by omega⟩
  · dsimp at he
    obtain ⟨p,hp⟩ := (show ∃ p : G.Walk v u, p.length ≤ j.val by simpa [good] using hj)
    exact ⟨p.concat ha,by simp only [Walk.length_concat]; omega⟩

lemma closure_sound (G : SimpleGraph V) (k : ℕ) : closure G k ⊆ good G k :=
  FiniteIteration.run_least _ (update_mono G k) _ (update_good G k) _

lemma closure_walk (G : SimpleGraph V) {k : ℕ} {v w : V} (p : G.Walk v w)
    (hp : p.length ≤ k) : (v,w,(⟨p.length,by omega⟩ : Fin (k+1))) ∈ closure G k := by
  induction p using Walk.concatRec with
  | Hnil => exact closure_nil G k _
  | @Hconcat u v w p ha ih =>
    apply closure_step G (ih (by simp only [Walk.length_concat] at hp; omega))
    · simp only [Walk.length_concat]
    · exact Or.inr ha

lemma closure_pad (G : SimpleGraph V) {k : ℕ} {v w : V} {j : Fin (k+1)}
    (hj : (v,w,j) ∈ closure G k) (t : ℕ) (ht : j.val+t ≤ k) :
    (v,w,(⟨j.val+t,by omega⟩ : Fin (k+1))) ∈ closure G k := by
  induction t with
  | zero => simpa using hj
  | succ t ih =>
    apply closure_step G (ih (by omega))
    · dsimp; omega
    · exact Or.inl rfl

lemma mem_closure_iff (G : SimpleGraph V) (k : ℕ) (v w : V) (i : Fin (k+1)) :
    (v,w,i) ∈ closure G k ↔ ∃ p : G.Walk v w, p.length ≤ i.val := by
  constructor
  · intro h
    simpa only [good,Finset.mem_filter,Finset.mem_univ,true_and] using closure_sound G k h
  · rintro ⟨p,hp⟩
    have hp' : p.length ≤ k := by omega
    have h := closure_pad G (closure_walk G p hp') (i.val-p.length) (by dsimp; omega)
    have he : (⟨p.length+(i.val-p.length),by omega⟩ : Fin (k+1)) = i := Fin.ext (by dsimp; omega)
    simpa only [he] using h

end

end WitnessedChoice.BGS.BFS



namespace WitnessedChoice.BGS





noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

namespace QuotedTerm

variable {n : ℕ} {A : Type} [Fintype A] (S : Input A) (env : Fin n → HF A)

omit [Fintype A] in
lemma HFTriple_injective {u v i u' v' i' : HF A} :
    HFTriple u v i = HFTriple u' v' i' ↔ u=u' ∧ v=v' ∧ i=i' := by
  simp only [HFTriple,pair_eq_pair]

end QuotedTerm

end





noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

open QuotedTerm

variable {A V : Type} [Fintype A] [Fintype V]

omit [Fintype V] in
lemma distanceCode_injective (code : V → HF A) (hc : Function.Injective code) :
    Function.Injective (distanceCode code) := by
  rintro ⟨u,v,i⟩ ⟨u',v',i'⟩ h
  obtain ⟨hu,hv,hi⟩ := HFTriple_injective.mp h
  have := hc hu
  have := hc hv
  have := Fin.ext (ordinal_injective hi)
  congr

omit [Fintype A] [Fintype V] in
lemma ordinal_mem_elements (i j : ℕ) : ordinal (A := A) i ∈ elements (ordinal j) ↔ i<j := by
  change ordinal i ∈ ordinal (A := A) j ↔ _
  rw [mem_ordinal]
  simp only [ordinal_injective.eq_iff]
  aesop

end





noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary QuotedTerm

variable {A V : Type} [Fintype A] [Fintype V]

lemma coded_closure_mem (code : V → HF A) (hc : Function.Injective code)
    (G : SimpleGraph V) (u v : V) (i : ℕ) (hi : i ≤ Fintype.card A) :
    HFTriple (code u) (code v) (ordinal i) ∈
      elements (ofFinset ((BFS.closure G (Fintype.card A)).image (distanceCode code))) ↔
    ∃ w : G.Walk u v, w.length ≤ i := by
  change distanceCode code (u,v,(⟨i,by omega⟩ : Fin (Fintype.card A+1))) ∈ _ ↔ _
  rw [elements_ofFinset,Finset.mem_image]
  constructor
  · rintro ⟨x,hx,he⟩
    have := distanceCode_injective code hc he
    subst x
    exact (BFS.mem_closure_iff G _ u v _).mp hx
  · intro h
    exact ⟨_,(BFS.mem_closure_iff G _ u v _).mpr h,rfl⟩

lemma coded_closure_mem_dist (code : V → HF A) (hc : Function.Injective code)
    (G : SimpleGraph V) (hG : G.Connected) (u v : V) (i : ℕ) (hi : i ≤ Fintype.card A) :
    HFTriple (code u) (code v) (ordinal i) ∈
      elements (ofFinset ((BFS.closure G (Fintype.card A)).image (distanceCode code))) ↔
    G.dist u v ≤ i := by
  rw [coded_closure_mem code hc G u v i hi]
  constructor
  · rintro ⟨w,hw⟩
    exact (G.dist_le w).trans hw
  · intro hi
    obtain ⟨w,hw⟩ := hG.exists_walk_length_eq_dist u v
    exact ⟨w,hw ▸ hi⟩

namespace QuotedTerm

variable {n : ℕ}

theorem meaning_distanceAt (S : Input A) (env : Fin n → HF A)
    (R ut vt : QuotedTerm n) (code : V → HF A) (hc : Function.Injective code)
    (G : SimpleGraph V) (hG : G.Connected) (u v : V)
    (hR : R.meaning S env = ofFinset ((BFS.closure G (Fintype.card A)).image (distanceCode code)))
    (hu : ut.meaning S env = code u) (hv : vt.meaning S env = code v)
    (hcard : Fintype.card V ≤ Fintype.card A) :
    (distanceAt R ut vt).meaning S env = ordinal (G.dist u v) := by
  obtain ⟨w,hw,hwd⟩ := (hG u v).exists_path_of_dist
  have hd : G.dist u v ≤ Fintype.card A := by
    rw [← hwd]
    exact (Nat.le_of_lt hw.length_lt).trans hcard
  simp only [distanceAt,meaning_unique,meaning_filter,meaning_indices,
    QuotedFormula.meaning_and,QuotedFormula.meaning_mem,meaning_triple,
    meaning_up,hu,hv,hR,meaning_var,Fin.cons_zero,QuotedFormula.meaning_allIn,
    QuotedFormula.meaning_imp,QuotedFormula.meaning_neg,Fin.cons_one]
  have hf : ((elements (ordinal (A := A) (Fintype.card A+1))).filter fun z =>
      HFTriple (code u) (code v) z ∈ elements (ofFinset
        ((BFS.closure G (Fintype.card A)).image (distanceCode code))) ∧
      ∀ y ∈ elements (ordinal (Fintype.card A+1)), y ∈ elements z →
        HFTriple (code u) (code v) y ∉ elements (ofFinset
          ((BFS.closure G (Fintype.card A)).image (distanceCode code)))) =
      {ordinal (G.dist u v)} := by
    ext z
    simp only [Finset.mem_filter,Finset.mem_singleton]
    constructor
    · rintro ⟨hz,hmem,hmin⟩
      obtain ⟨i,hi,rfl⟩ := (mem_ordinal z _).mp hz
      have him := (coded_closure_mem_dist code hc G hG u v i (by omega)).mp hmem
      have hie : i = G.dist u v := by
        by_contra h
        have hlt : G.dist u v < i := by omega
        exact hmin _ ((ordinal_mem_elements _ _).mpr (by omega))
          ((ordinal_mem_elements _ _).mpr hlt)
          ((coded_closure_mem_dist code hc G hG u v _ hd).mpr le_rfl)
      rw [hie]
    · intro hz
      subst z
      refine ⟨(ordinal_mem_elements _ _).mpr (by omega),
        (coded_closure_mem_dist code hc G hG u v _ hd).mpr le_rfl,?_⟩
      intro y hy hlt hm
      obtain ⟨i,hi,rfl⟩ := (mem_ordinal y _).mp hy
      have hil := (ordinal_mem_elements _ _).mp hlt
      have him := (coded_closure_mem_dist code hc G hG u v i (by omega)).mp hm
      omega
  change uniqueHF (ofFinset _) = _
  simp only [HFTriple] at hf
  trans uniqueHF (ofFinset {ordinal (G.dist u v)})
  · congr 2
    ext z
    simpa [HFTriple] using (Finset.ext_iff.mp hf z)
  · exact uniqueHF_singleton _

end QuotedTerm

end





noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

namespace QuotedTerm

variable {A : Type} [Fintype A] {n : ℕ}

lemma firstHF_pair (S : Input A) (x y : HF A) :
    firstHF (Hereditary.pair x y) = x := by
  have h := meaning_fst_pair S (Fin.cons x (Fin.cons y Fin.elim0)) (var 0) (var 1)
  simpa only [meaning_fst,meaning_pair,meaning_var,Fin.cons_zero,Fin.cons_one] using h

lemma secondHF_pair (S : Input A) (x y : HF A) :
    secondHF (Hereditary.pair x y) = y := by
  have h := meaning_snd_pair S (Fin.cons x (Fin.cons y Fin.elim0)) (var 0) (var 1)
  simpa only [meaning_snd,meaning_pair,meaning_var,Fin.cons_zero,Fin.cons_one] using h

lemma meaning_fst_of_eq (S : Input A) (env : Fin n → HF A) (a : QuotedTerm n)
    (x y : HF A) (h : a.meaning S env = Hereditary.pair x y) :
    a.fst.meaning S env = x := by rw [meaning_fst,h,firstHF_pair S]

lemma meaning_snd_of_eq (S : Input A) (env : Fin n → HF A) (a : QuotedTerm n)
    (x y : HF A) (h : a.meaning S env = Hereditary.pair x y) :
    a.snd.meaning S env = y := by rw [meaning_snd,h,secondHF_pair S]

lemma meaning_component_tuple (S : Input A) (env : Fin n → HF A) (a : QuotedTerm n)
    (l : List (HF A)) (h : a.meaning S env = tupleCode l) (i : ℕ) (hi : i < l.length) :
    (a.component i).meaning S env = l[i] := by
  induction l generalizing a i with
  | nil => simp at hi
  | cons x l ih =>
    cases i with
    | zero => exact meaning_fst_of_eq S env a x (tupleCode l) h
    | succ i =>
      have he := meaning_snd_of_eq S env a x (tupleCode l) h
      exact ih a.snd he i (by simpa using hi)

lemma meaning_component_ofFn (S : Input A) (env : Fin n → HF A) (a : QuotedTerm n)
    {k : ℕ} (f : Fin k → HF A) (h : a.meaning S env = tupleCode (List.ofFn f)) (i : Fin k) :
    (a.component i.val).meaning S env = f i := by
  simpa [List.getElem_ofFn] using meaning_component_tuple S env a (List.ofFn f) h i.val
    (by simp)

end QuotedTerm

end

end WitnessedChoice.BGS



namespace WitnessedChoice.TreeTest

noncomputable section

open Classical

namespace RootedTree

variable {V A : Type} (T : RootedTree V)

theorem parent_adj (v : V) (h : v ≠ T.root) : T.Adj v (T.parent v) := Or.inl ⟨h,rfl⟩

end RootedTree

end

end WitnessedChoice.TreeTest

end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_GridGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace WitnessedSeparation.Grid

noncomputable section

open Classical Support

variable {n : ℕ}

lemma faceSide_axis (f : Face n) (i : Fin 4) :
    edgeAxis (faceSide f i) = sideAxis (facePlane f) i := by
  rcases f with ⟨x,y,z⟩ | (⟨x,y,z⟩ | ⟨x,y,z⟩) <;>
    fin_cases i <;> rfl

lemma faceCorner_injective {f g : Face n} (hp : facePlane f = facePlane g)
    (i : Fin 4) (he : faceCorner f i = faceCorner g i) : f = g := by
  rcases f with ⟨x,y,z⟩ | (⟨x,y,z⟩ | ⟨x,y,z⟩) <;>
    rcases g with ⟨a,b,c⟩ | (⟨a,b,c⟩ | ⟨a,b,c⟩) <;>
    simp only [facePlane] at hp
  all_goals first | contradiction | skip
  all_goals fin_cases i <;> simpa [faceCorner] using he

lemma epsilon_ne_zero (v : Vertex n) (e : IncidentEdges v) : epsilon v e.val ≠ 0 := by
  by_cases hh : head e.val = v
  · have ht : tail e.val ≠ v := fun h => head_ne_tail e.val (hh.trans h.symm)
    simp [epsilon,hh,ht]
  · have ht := e.property.resolve_left hh
    simp [epsilon,hh,ht]

end





noncomputable section

open Classical WitnessedChoice.TreeTest

variable {n : ℕ}

namespace ParentEdges

variable {T : RootedTree (Vertex n)} (P : ParentEdges T)

lemma edge_mem (v : Vertex n) (hv : v ≠ T.root) : P.edge v hv ∈ P.treeEdges := by
  exact Finset.mem_image.mpr ⟨⟨v,hv⟩,Finset.mem_univ _,rfl⟩

lemma route_zero_off_tree {e : Edge n} (he : e ∉ P.treeEdges) (v : Vertex n) : P.route v e = 0 := by
  induction v using (measure T.level).wf.induction with
  | h v ih =>
    rw [route]
    split_ifs with hv
    · rfl
    · have hne : e ≠ P.edge v hv := fun h => he (h.symm ▸ P.edge_mem v hv)
      simp only [Pi.add_apply,Pi.single_eq_of_ne hne,zero_add]
      exact ih (T.parent v) (T.parent_lower v hv)

lemma flow_self (e : Edge n) (he : e ∉ P.treeEdges) (a : Scalar) : (P.flow e a).val e = a := by
  simp [flow,fundamental,P.route_zero_off_tree he]

lemma flow_other (e f : Edge n) (hf : f ∉ P.treeEdges) (hne : f ≠ e) (a : Scalar) :
    (P.flow e a).val f = 0 := by
  simp [flow,fundamental,P.route_zero_off_tree hf,Pi.single_eq_of_ne hne]

end ParentEdges

end





noncomputable section

open Classical Support

variable {n : ℕ} {v : Vertex n} {b : Vertex n → Scalar}

lemma incident_on_axis (hn : 1 ≤ n) (v : Vertex n) (a : Fin 3) :
    ∃ e : IncidentEdges v, edgeAxis e.val = a := by
  rcases v with ⟨i,j,k⟩
  fin_cases a
  · by_cases hi : i.val = 0
    · refine ⟨⟨ex ⟨0,by omega⟩ j k,Or.inr ?_⟩,rfl⟩
      simp only [ex,tail,Prod.mk.injEq,and_true]
      apply Fin.ext
      exact hi.symm
    · refine ⟨⟨ex ⟨i.val-1,by omega⟩ j k,Or.inl ?_⟩,rfl⟩
      simp only [ex,head,Prod.mk.injEq,and_true]
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
  · by_cases hj : j.val = 0
    · refine ⟨⟨ey i ⟨0,by omega⟩ k,Or.inr ?_⟩,rfl⟩
      simp only [ey,tail,Prod.mk.injEq,true_and,and_true]
      apply Fin.ext
      exact hj.symm
    · refine ⟨⟨ey i ⟨j.val-1,by omega⟩ k,Or.inl ?_⟩,rfl⟩
      simp only [ey,head,Prod.mk.injEq,true_and,and_true]
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
  · by_cases hk : k.val = 0
    · refine ⟨⟨ez i j ⟨0,by omega⟩,Or.inr ?_⟩,rfl⟩
      simp only [ez,tail,Prod.mk.injEq,true_and]
      apply Fin.ext
      exact hk.symm
    · refine ⟨⟨ez i j ⟨k.val-1,by omega⟩,Or.inl ?_⟩,rfl⟩
      simp only [ez,head,Prod.mk.injEq,true_and]
      apply Fin.ext
      simp only [Fin.val_succ]
      omega

lemma fin_three_other (a b : Fin 3) : ∃ c : Fin 3, c ≠ a ∧ c ≠ b := by
  fin_cases a <;> fin_cases b
  all_goals first
    | exact ⟨0,by decide,by decide⟩
    | exact ⟨1,by decide,by decide⟩
    | exact ⟨2,by decide,by decide⟩

lemma other_incident (hn : 1 ≤ n) (e e' : IncidentEdges v) :
    ∃ h : IncidentEdges v, h ≠ e ∧ h ≠ e' := by
  obtain ⟨a,ha,ha'⟩ := fin_three_other (edgeAxis e.val) (edgeAxis e'.val)
  obtain ⟨h,hh⟩ := incident_on_axis hn v a
  refine ⟨h,?_,?_⟩
  · intro he
    subst h
    exact ha hh.symm
  · intro he
    subst h
    exact ha' hh.symm

lemma extendVertexScalars_charge (e0 : IncidentEdges v) (z : IncidentEdges v → Scalar) :
    (∑ e, epsilon v e.val * extendVertexScalars b v e0 z e) = b v := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ e0)]
  have he : (∑ e ∈ Finset.univ.erase e0,
      epsilon v e.val * extendVertexScalars b v e0 z e) =
      ∑ e ∈ Finset.univ.erase e0, epsilon v e.val * z e := by
    apply Finset.sum_congr rfl
    intro e he
    rw [extendVertexScalars,ite_eq_right (Finset.ne_of_mem_erase he)]
  rw [he,extendVertexScalars,ite_eq_left rfl,mul_inv_cancel_left₀ (epsilon_ne_zero v e0),sub_add_cancel]

lemma exists_configuration_two (hn : 1 ≤ n) (e e' : IncidentEdges v) (hne : e ≠ e')
    (s : LocalGroup e.val) (t : LocalGroup e'.val)
    (hc : ∀ f : Face n, ∀ he : cycle f e.val ≠ 0, ∀ he' : cycle f e'.val ≠ 0,
      s.face ⟨f,he⟩ = t.face ⟨f,he'⟩) :
    ∃ c : Configuration b v, c.state e = s ∧ c.state e' = t := by
  obtain ⟨e0,hr,hr'⟩ := other_incident hn e e'
  let u (f : Face n) : Plane := if h : cycle f e.val ≠ 0 then s.face ⟨f,h⟩
    else if h' : cycle f e'.val ≠ 0 then t.face ⟨f,h'⟩ else 0
  let z (h : IncidentEdges v) : Scalar := if h = e then s.flow else if h = e' then t.flow else 0
  let c : Configuration b v :=
    { state := fun h => ⟨fun f => u f.val,extendVertexScalars b v e0 z h⟩
      compatible := by intro h h' f hf hf'; rfl
      charge := extendVertexScalars_charge e0 z }
  refine ⟨c,?_,?_⟩
  · apply H.ext
    · funext f
      exact dite_eq_left f.property
    · change extendVertexScalars b v e0 z e = s.flow
      simp only [extendVertexScalars,ite_eq_right (Ne.symm hr),z,ite_eq_left rfl]
  · apply H.ext
    · funext f
      change u f.val = t.face f
      dsimp only [u]
      split_ifs with he he'
      · exact hc f.val he f.property
      · rfl
      · exact (he' f.property).elim
    · change extendVertexScalars b v e0 z e' = t.flow
      simp only [extendVertexScalars,ite_eq_right (Ne.symm hr'),z,ite_eq_right (Ne.symm hne),ite_true]

end





noncomputable section

open Classical Support

variable {n : ℕ}

lemma faceBase_injective {f g : Face n} (hp : facePlane f = facePlane g)
    (h : faceBase f = faceBase g) : f = g :=
  faceCorner_injective hp 0 (vertexCoord_injective h)

lemma two_axes_plane : ∀ p q a b : Fin 3, a ≠ b →
    planeAxis p a → planeAxis p b → planeAxis q a → planeAxis q b → p = q := by
  unfold planeAxis
  decide

lemma plane_axis_exhaust : ∀ p a b c : Fin 3, a ≠ b → planeAxis p a → planeAxis p b →
    c = a ∨ c = b ∨ ¬ planeAxis p c := by
  unfold planeAxis
  decide

lemma side_axis_in_plane (f : Face n) (i : Fin 4) :
    planeAxis (facePlane f) (edgeAxis (faceSide f i)) := ⟨i,(faceSide_axis f i).symm⟩

lemma faceBase_on_axis (f : Face n) (i : Fin 4) :
    faceBase f (edgeAxis (faceSide f i)) =
      vertexCoord (tail (faceSide f i)) (edgeAxis (faceSide f i)) := by
  rcases f with ⟨x,y,z⟩ | (⟨x,y,z⟩ | ⟨x,y,z⟩) <;> fin_cases i <;> rfl

lemma faceBase_outside (f : Face n) (i : Fin 4) (a : Fin 3)
    (ha : ¬ planeAxis (facePlane f) a) :
    faceBase f a = vertexCoord (tail (faceSide f i)) a := by
  rcases f with ⟨x,y,z⟩ | (⟨x,y,z⟩ | ⟨x,y,z⟩) <;> fin_cases a
  all_goals first
    | exact (ha ⟨0,rfl⟩).elim
    | exact (ha ⟨1,rfl⟩).elim
    | (fin_cases i <;> rfl)

lemma common_face_unique (e e' : Edge n) (hne : edgeAxis e ≠ edgeAxis e')
    {f g : Face n} (hf : cycle f e ≠ 0) (hf' : cycle f e' ≠ 0)
    (hg : cycle g e ≠ 0) (hg' : cycle g e' ≠ 0) : f = g := by
  obtain ⟨i,hi⟩ := support_cycle f e hf
  obtain ⟨j,hj⟩ := support_cycle f e' hf'
  obtain ⟨k,hk⟩ := support_cycle g e hg
  obtain ⟨l,hl⟩ := support_cycle g e' hg'
  have ha : planeAxis (facePlane f) (edgeAxis e) := hi ▸ side_axis_in_plane f i
  have hb : planeAxis (facePlane f) (edgeAxis e') := hj ▸ side_axis_in_plane f j
  have hc : planeAxis (facePlane g) (edgeAxis e) := hk ▸ side_axis_in_plane g k
  have hd : planeAxis (facePlane g) (edgeAxis e') := hl ▸ side_axis_in_plane g l
  have hp := two_axes_plane _ _ _ _ hne ha hb hc hd
  apply faceBase_injective hp
  funext a
  rcases plane_axis_exhaust _ _ _ a hne ha hb with rfl|rfl|h
  · calc
      faceBase f (edgeAxis e) = vertexCoord (tail e) (edgeAxis e) := by
        simpa only [hi] using faceBase_on_axis f i
      _ = faceBase g (edgeAxis e) := by simpa only [hk] using (faceBase_on_axis g k).symm
  · calc
      faceBase f (edgeAxis e') = vertexCoord (tail e') (edgeAxis e') := by
        simpa only [hj] using faceBase_on_axis f j
      _ = faceBase g (edgeAxis e') := by simpa only [hl] using (faceBase_on_axis g l).symm
  · calc
      faceBase f a = vertexCoord (tail e) a := by simpa only [hi] using faceBase_outside f i a h
      _ = faceBase g a := by simpa only [hk] using (faceBase_outside g k a (hp ▸ h)).symm

end





noncomputable section

open Classical Support

variable {n : ℕ} {b : Vertex n → Scalar}

lemma index_next_adjacent (i : Fin 4) : AdjacentIndex i (i+1) := Or.inl rfl

lemma nonadjacent_next (i j : Fin 4) (h : ¬ AdjacentIndex i j) : AdjacentIndex j (i+1) := by
  revert i j
  unfold AdjacentIndex
  decide

end





noncomputable section

open Classical SimpleGraph

variable {n : ℕ}

lemma path_walk_lower {u v : Fin (n+1)} (w : (pathGraph (n+1)).Walk u v) :
    Nat.dist u.val v.val ≤ w.length := by
  induction w with
  | nil => simp
  | @cons a b c hab w ih =>
    have ha := pathGraph_adj.mp hab
    simp only [Walk.length_cons]
    simp only [Nat.dist] at ih ⊢
    omega

lemma path_walk_upper_le (k : ℕ) : ∀ u v : Fin (n+1), u.val ≤ v.val → v.val-u.val = k →
    ∃ w : (pathGraph (n+1)).Walk u v, w.length = k := by
  induction k with
  | zero =>
    intro u v huv he
    have h : u = v := Fin.ext (by omega)
    subst v
    exact ⟨.nil,rfl⟩
  | succ k ih =>
    intro u v huv he
    let u' : Fin (n+1) := ⟨u.val+1,by omega⟩
    have hadj : (pathGraph (n+1)).Adj u u' := pathGraph_adj.mpr (Or.inl rfl)
    obtain ⟨w,hw⟩ := ih u' v (by dsimp [u']; omega) (by dsimp [u']; omega)
    exact ⟨.cons hadj w,by simp only [Walk.length_cons,hw]⟩

lemma path_dist (u v : Fin (n+1)) : (pathGraph (n+1)).dist u v = Nat.dist u.val v.val := by
  apply Nat.le_antisymm
  · by_cases h : u.val ≤ v.val
    · obtain ⟨w,hw⟩ := path_walk_upper_le (v.val-u.val) u v h rfl
      rw [Nat.dist_eq_sub_of_le h,← hw]
      exact dist_le w
    · have h' : v.val ≤ u.val := by omega
      obtain ⟨w,hw⟩ := path_walk_upper_le (u.val-v.val) v u h' rfl
      rw [Nat.dist_eq_sub_of_le_right h',← hw,← w.length_reverse]
      exact dist_le w.reverse
  · obtain ⟨w,hw⟩ := ((pathGraph_connected n).preconnected u v).exists_walk_length_eq_dist
    rw [← hw]
    exact path_walk_lower w

lemma path_edist (u v : Fin (n+1)) : (pathGraph (n+1)).edist u v = (Nat.dist u.val v.val : ℕ∞) := by
  rw [← ((pathGraph_connected n).preconnected u v).coe_dist_eq_edist,path_dist]

lemma boxGraph_dist (u v : Vertex n) : (boxGraph n).dist u v =
    Nat.dist u.1.val v.1.val + (Nat.dist u.2.1.val v.2.1.val + Nat.dist u.2.2.val v.2.2.val) := by
  have h := ((boxGraph_connected n).preconnected u v).coe_dist_eq_edist
  simp only [boxGraph,edist_boxProd,path_edist,← Nat.cast_add] at h
  exact_mod_cast h

end

end WitnessedSeparation.Grid

end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_AnchoredTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace WitnessedSeparation.Grid

noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

lemma configuration_exists (hn : 1 ≤ n) (v : Vertex n) : Nonempty (Configuration b v) := by
  obtain ⟨e0,_⟩ := incident_on_axis hn v 0
  exact ⟨{ state := fun e => ⟨0,extendVertexScalars b v e0 0 e⟩
           compatible := by intro e e' f hf hf'; rfl
           charge := extendVertexScalars_charge e0 0 }⟩

lemma edgeBlockSet_injective : Function.Injective (edgeBlockSet b) := by
  intro e f h
  have hm : (Sum.inl ⟨e,1⟩ : Atom b) ∈ edgeBlockSet b e := by simp
  rw [h,mem_edgeBlockSet] at hm
  obtain ⟨t,ht⟩ := hm
  exact congrArg Sigma.fst (Sum.inl.inj ht)

lemma vertexBlockSet_injective (hn : 1 ≤ n) : Function.Injective (vertexBlockSet b) := by
  intro v w h
  obtain ⟨s⟩ := configuration_exists (b := b) hn v
  have hm : (Sum.inr ⟨v,s⟩ : Atom b) ∈ vertexBlockSet b v := by simp
  rw [h,mem_vertexBlockSet] at hm
  obtain ⟨t,ht⟩ := hm
  exact congrArg Sigma.fst (Sum.inr.inj ht)

lemma vertexCode_injective (hn : 1 ≤ n) : Function.Injective (vertexCode b) :=
  fun _ _ h => vertexBlockSet_injective hn (stateCode_inj.mp h)

lemma edgeCode_injective : Function.Injective (edgeCode b) :=
  fun _ _ h => edgeBlockSet_injective (stateCode_inj.mp h)

lemma blockIncident_grid (hn : 1 ≤ n) (v : Vertex n) (e : Edge n) :
    blockIncident (atomInput b) (vertexCode b v) (edgeCode b e) ↔ incident v e := by
  simp only [blockIncident,vertexCode,edgeCode,exists_stateCode,mem_vertexBlockSet,
    mem_edgeBlockSet]
  constructor
  · rintro ⟨_,⟨s,rfl⟩,_,⟨t,rfl⟩,h⟩
    rw [inputHF_atoms] at h
    change decide (AtomRelation b .I (.inr ⟨v,s⟩) (.inl ⟨e,t⟩)) = true at h
    have h := of_decide_eq_true h
    cases h with | inc v s e => exact e.property
  · intro h
    obtain ⟨s⟩ := configuration_exists (b := b) hn v
    exact ⟨.inr ⟨v,s⟩,⟨s,rfl⟩,.inl ⟨e,s.state ⟨e,h⟩⟩,⟨_,rfl⟩,
      by rw [inputHF_atoms]; exact decide_eq_true (.inc v s ⟨e,h⟩)⟩

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

lemma vertex_card_le_atoms (hn : 1 ≤ n) : Fintype.card (Vertex n) ≤ Fintype.card (Atom b) := by
  let f (v : Vertex n) : Atom b := .inr ⟨v,(configuration_exists (b := b) hn v).some⟩
  apply Fintype.card_le_of_injective f
  intro v w h
  exact congrArg Sigma.fst (Sum.inr.inj h)

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.TreeTest

variable {n : ℕ}

lemma symEdge_injective : Function.Injective (symEdge (n := n)) := by
  intro e f h
  apply edge_eq_of_endpoints e f
  exact Sym2.eq_iff.mp h

lemma edgeGraph_edgeFinset (T : Finset (Edge n)) :
    (edgeGraph T).edgeFinset = T.image symEdge := by
  apply Finset.ext
  intro q
  induction q using Sym2.inductionOn with
  | _ u v =>
    rw [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet]
    change (∃ e ∈ T, u = tail e ∧ v = head e ∨ v = tail e ∧ u = head e) ↔ _
    simp only [Finset.mem_image,symEdge,Sym2.eq_iff]
    constructor
    · rintro ⟨e,he, (⟨hu,hv⟩ | ⟨hv,hu⟩)⟩
      · exact ⟨e,he,Or.inl ⟨hu.symm,hv.symm⟩⟩
      · exact ⟨e,he,Or.inr ⟨hv.symm,hu.symm⟩⟩
    · rintro ⟨e,he, (⟨hu,hv⟩ | ⟨hv,hu⟩)⟩
      · exact ⟨e,he,Or.inl ⟨hu.symm,hv.symm⟩⟩
      · exact ⟨e,he,Or.inr ⟨hv.symm,hu.symm⟩⟩

lemma edgeGraph_card (T : Finset (Edge n)) :
    Nat.card (edgeGraph T).edgeSet = T.card := by
  rw [Nat.card_eq_fintype_card,←SimpleGraph.edgeFinset_card,edgeGraph_edgeFinset,
    Finset.card_image_of_injective _ symEdge_injective]

namespace ParentEdges

variable {T : RootedTree (Vertex n)} (P : ParentEdges T)

lemma edge_injective : Function.Injective (fun v : {v : Vertex n // v ≠ T.root} => P.edge v.val v.property) := by
  intro v w h
  apply Subtype.ext
  have hv := P.endpoints v.val v.property
  have hw := P.endpoints w.val w.property
  change P.edge v.val v.property = P.edge w.val w.property at h
  rw [h] at hv
  rcases hv with ⟨hv₁,hv₂⟩ | ⟨hv₁,hv₂⟩ <;>
    rcases hw with ⟨hw₁,hw₂⟩ | ⟨hw₁,hw₂⟩
  · exact hv₁.symm.trans hw₁
  · have he₁ := hv₁.symm.trans hw₂
    have he₂ := hw₁.symm.trans hv₂
    have hlv := T.parent_lower v.val v.property
    have hlw := T.parent_lower w.val w.property
    rw [←he₁] at hlw
    rw [←he₂] at hlv
    omega
  · have he₁ := hv₁.symm.trans hw₂
    have he₂ := hw₁.symm.trans hv₂
    have hlv := T.parent_lower v.val v.property
    have hlw := T.parent_lower w.val w.property
    rw [←he₁] at hlw
    rw [←he₂] at hlv
    omega
  · exact hv₁.symm.trans hw₁

lemma graph_adj (u v : Vertex n) : (edgeGraph P.treeEdges).Adj u v ↔ T.Adj u v := by
  simp only [edgeGraph,treeEdges,Finset.mem_image,Finset.mem_univ,true_and,exists_exists_eq_and]
  constructor
  · rintro ⟨w,h⟩
    rcases P.endpoints w.val w.property with ⟨hh,ht⟩ | ⟨ht,hh⟩
    · rw [hh,ht] at h
      rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact Or.inr ⟨w.property,rfl⟩
      · exact Or.inl ⟨w.property,rfl⟩
    · rw [hh,ht] at h
      rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact Or.inl ⟨w.property,rfl⟩
      · exact Or.inr ⟨w.property,rfl⟩
  · rintro (⟨hu,rfl⟩ | ⟨hv,rfl⟩)
    · refine ⟨⟨u,hu⟩,?_⟩
      rcases P.endpoints u hu with ⟨hh,ht⟩ | ⟨ht,hh⟩
      · exact Or.inr ⟨ht.symm,hh.symm⟩
      · exact Or.inl ⟨ht.symm,hh.symm⟩
    · refine ⟨⟨v,hv⟩,?_⟩
      rcases P.endpoints v hv with ⟨hh,ht⟩ | ⟨ht,hh⟩
      · exact Or.inl ⟨ht.symm,hh.symm⟩
      · exact Or.inr ⟨ht.symm,hh.symm⟩

lemma graph_reachable_root (v : Vertex n) : (edgeGraph P.treeEdges).Reachable v T.root := by
  induction v using (measure T.level).wf.induction with
  | h v ih =>
    by_cases hv : v = T.root
    · subst v; exact .rfl
    · exact ((P.graph_adj v (T.parent v)).mpr (T.parent_adj v hv)).reachable.trans
        (ih (T.parent v) (T.parent_lower v hv))

lemma graph_connected : (edgeGraph P.treeEdges).Connected where
  preconnected u v := (P.graph_reachable_root u).trans (P.graph_reachable_root v).symm
  nonempty := ⟨T.root⟩

lemma card_treeEdges : P.treeEdges.card + 1 = Fintype.card (Vertex n) := by
  simp only [treeEdges,Finset.card_image_of_injective _ P.edge_injective,Finset.card_univ]
  have h := Fintype.card_subtype_compl (fun v : Vertex n => v = T.root)
  have hc : Fintype.card {v : Vertex n // v = T.root} = 1 := by simp
  rw [hc] at h
  change Fintype.card {v : Vertex n // v ≠ T.root} = _ at h
  have hp : 0 < Fintype.card (Vertex n) := Fintype.card_pos_iff.mpr ⟨T.root⟩
  omega

lemma graph_isTree : (edgeGraph P.treeEdges).IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  exact ⟨P.graph_connected,by rw [edgeGraph_card,Nat.card_eq_fintype_card]; exact P.card_treeEdges⟩

end ParentEdges

end

end WitnessedSeparation.Grid


section

namespace WitnessedSeparation.Grid

noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

namespace QuotedGrid

open QuotedTerm QuotedFormula

variable {k : ℕ}

lemma meaning_incident (env : Fin k → HF (Atom b)) (vt et : QuotedTerm k)
    (u : Vertex n) (e : Edge n) (hu : vt.meaning (atomInput b) env = vertexCode b u)
    (he : et.meaning (atomInput b) env = edgeCode b e) (hn : 1 ≤ n) :
    (QuotedFormula.incident vt et).meaning (atomInput b) env ↔ incident u e := by
  rw [QuotedFormula.meaning_incident,hu,he]
  exact blockIncident_grid hn u e

end QuotedGrid

end

end WitnessedSeparation.Grid

end


namespace WitnessedSeparation.Grid





noncomputable section

open Classical Support

variable {n : ℕ} {b : Vertex n → Scalar}

namespace CycleFrame

variable (C : CycleFrame n)

lemma incident_ends (i : Fin 4) : incident (C.vertex i) (C.edge i) ∧ incident (C.vertex (i+1)) (C.edge i) :=
  indexed_cycle_incident C.vertex C.edge C.endpoints i

lemma consecutive_axis_ne (i : Fin 4) : edgeAxis (C.edge i) ≠ edgeAxis (C.edge (i+1)) := by
  have hadd : Function.Injective (fun j : Fin 4 => i+j) := by
    have h : ∀ i j k : Fin 4, i+j=i+k → j=k := by decide
    exact h i
  have hh := square_consecutive_perpendicular (fun j => C.vertex (i+j)) (fun j => C.edge (i+j))
    (C.vertex_injective.comp hadd) (fun j => by simpa only [add_assoc] using C.endpoints (i+j))
  simpa only [add_zero] using hh

lemma adjacent_axis_ne (i j : Fin 4) (h : AdjacentIndex i j) : edgeAxis (C.edge i) ≠ edgeAxis (C.edge j) := by
  rcases h with rfl | rfl
  · exact C.consecutive_axis_ne i
  · exact (C.consecutive_axis_ne j).symm

lemma support_iff (e : Edge n) : cycle C.face e ≠ 0 ↔ ∃ i, e = C.edge i := by
  choose J hJ using fun i => support_cycle C.face (C.edge i) (C.on_face i)
  have hJi : Function.Injective J := by
    intro i j hh
    apply C.edge_injective
    exact (hJ i).symm.trans (hh ▸ hJ j)
  constructor
  · intro he
    obtain ⟨k,hk⟩ := support_cycle C.face e he
    obtain ⟨i,rfl⟩ := Finite.surjective_of_injective hJi k
    exact ⟨i,hk.symm.trans (hJ i)⟩
  · rintro ⟨i,rfl⟩
    exact C.on_face i

lemma face_unique (f : Face n) (hf : ∀ i, cycle f (C.edge i) ≠ 0) : C.face = f :=
  common_face_unique (C.edge 0) (C.edge 1) (C.consecutive_axis_ne 0)
    (C.on_face 0) (C.on_face 1) (hf 0) (hf 1)

lemma joint_incident (i j : Fin 4) (h : AdjacentIndex i j) :
    incident (C.joint i j) (C.edge i) ∧ incident (C.joint i j) (C.edge j) := by
  unfold joint
  split_ifs with he
  · subst j
    exact ⟨(C.incident_ends i).2,(C.incident_ends (i+1)).1⟩
  · have hi : i=j+1 := h.resolve_left he
    subst i
    exact ⟨(C.incident_ends (j+1)).1,(C.incident_ends j).2⟩

lemma across_iff (hn : 1 ≤ n) (i j : Fin 4) (h : AdjacentIndex i j)
    (s : LocalGroup (C.edge i)) (t : LocalGroup (C.edge j)) :
    C.Across (b := b) i j s t ↔ s.face ⟨C.face,C.on_face i⟩ = t.face ⟨C.face,C.on_face j⟩ := by
  constructor
  · rintro ⟨hi,hj,c,hs,ht⟩
    simpa only [hs,ht] using c.compatible ⟨_,hi⟩ ⟨_,hj⟩ C.face (C.on_face i) (C.on_face j)
  · intro hs
    obtain ⟨hi,hj⟩ := C.joint_incident i j h
    have he : (⟨C.edge i,hi⟩ : IncidentEdges (C.joint i j)) ≠ ⟨C.edge j,hj⟩ := by
      intro hh
      exact C.adjacent_axis_ne i j h (congrArg (edgeAxis ∘ Subtype.val) hh)
    obtain ⟨c,hc,hc'⟩ := exists_configuration_two (b := b) hn ⟨_,hi⟩ ⟨_,hj⟩ he s t (by
      intro f hfi hfj
      have hf := common_face_unique _ _ (C.adjacent_axis_ne i j h) (C.on_face i) (C.on_face j) hfi hfj
      subst f
      exact hs)
    exact ⟨hi,hj,c,hc,hc'⟩

lemma match_iff (hn : 1 ≤ n) (i j : Fin 4) (s : LocalGroup (C.edge i)) (t : LocalGroup (C.edge j)) :
    C.Match (b := b) i j s t ↔ s.face ⟨C.face,C.on_face i⟩ = t.face ⟨C.face,C.on_face j⟩ := by
  unfold Match
  split_ifs with h
  · exact C.across_iff hn i j h s t
  · simp only [C.across_iff hn i (i+1) (index_next_adjacent i),
      C.across_iff hn j (i+1) (nonadjacent_next i j h)]
    constructor
    · rintro ⟨q,hs,ht⟩
      exact hs.trans ht.symm
    · intro he
      exact ⟨⟨fun _ => s.face ⟨C.face,C.on_face i⟩,0⟩,rfl,he.symm⟩

end CycleFrame

@[simp] lemma standardFrame_face (f : Face n) : (standardFrame f).face = f :=
  (standardFrame f).face_unique f (cycle_faceSide f)

end

end WitnessedSeparation.Grid

end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_CycleTranslation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace WitnessedSeparation.Grid

noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

lemma endpoints_incident_iff (e : Edge n) (u v : Vertex n) :
    ((u = tail e ∧ v = head e) ∨ (v = tail e ∧ u = head e)) ↔
      u ≠ v ∧ incident u e ∧ incident v e := by
  constructor
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · exact ⟨(head_ne_tail e).symm,Or.inr rfl,Or.inl rfl⟩
    · exact ⟨head_ne_tail e,Or.inl rfl,Or.inr rfl⟩
  · rintro ⟨hne,(hu|hu),(hv|hv)⟩
    · exact (hne (hu.symm.trans hv)).elim
    · exact Or.inr ⟨hv.symm,hu.symm⟩
    · exact Or.inl ⟨hu.symm,hv.symm⟩
    · exact (hne (hu.symm.trans hv)).elim

namespace QuotedGrid

open QuotedTerm QuotedFormula SourceSyntax

variable {k : ℕ}

lemma adjacent_index_iff (i j : Fin 4) : (j=next4 i ∨ j=prev4 i) ↔ AdjacentIndex i j := by
  rw [next4_eq_add,prev4_eq_add]
  revert i j
  unfold AdjacentIndex
  decide

lemma meaning_fv_pair (env : Fin k → HF (Atom b)) (ft : QuotedTerm k)
    (v : Fin 4 → Vertex n) (e : Fin 4 → Edge n)
    (hf : ft.meaning (atomInput b) env = Hereditary.pair (tupleCode (List.ofFn (vertexCode b ∘ v)))
      (tupleCode (List.ofFn (edgeCode b ∘ e)))) (i : Fin 4) :
    (fv ft i).meaning (atomInput b) env = vertexCode b (v i) := by
  exact meaning_component_ofFn _ _ _ _ (meaning_fst_of_eq _ _ _ _ _ hf) i

lemma meaning_fe_pair (env : Fin k → HF (Atom b)) (ft : QuotedTerm k)
    (v : Fin 4 → Vertex n) (e : Fin 4 → Edge n)
    (hf : ft.meaning (atomInput b) env = Hereditary.pair (tupleCode (List.ofFn (vertexCode b ∘ v)))
      (tupleCode (List.ofFn (edgeCode b ∘ e)))) (i : Fin 4) :
    (fe ft i).meaning (atomInput b) env = edgeCode b (e i) := by
  exact meaning_component_ofFn _ _ _ _ (meaning_snd_of_eq _ _ _ _ _ hf) i

end QuotedGrid

end

end WitnessedSeparation.Grid

end


namespace WitnessedSeparation.Grid

noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

namespace QuotedGrid

open QuotedTerm QuotedFormula SourceSyntax

variable {k : ℕ}

lemma meaning_hasEndpoints (env : Fin k → HF (Atom b)) (et ut vt : QuotedTerm k)
    (e : Edge n) (u v : Vertex n)
    (he : et.meaning (atomInput b) env = edgeCode b e)
    (hu : ut.meaning (atomInput b) env = vertexCode b u)
    (hv : vt.meaning (atomInput b) env = vertexCode b v) (hn : 1 ≤ n) :
    (hasEndpoints et ut vt).meaning (atomInput b) env ↔
      ((u=tail e ∧ v=head e) ∨ (v=tail e ∧ u=head e)) := by
  simp only [hasEndpoints,meaning_and,meaning_neg,meaning_eq,hu,hv,
    (vertexCode_injective hn).eq_iff,meaning_incident env ut et u e hu he hn,
    meaning_incident env vt et v e hv he hn]
  exact (endpoints_incident_iff e u v).symm

end QuotedGrid

end

end WitnessedSeparation.Grid


namespace WitnessedSeparation.Grid

noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

lemma mem_edgeCode_iff (e : Edge n) (z : HF (Atom b)) :
    z ∈ elements (edgeCode b e) ↔ ∃ s : LocalGroup e, z = atom (.inl ⟨e,s⟩) := by
  simp only [edgeCode,stateCode,elements_ofFinset,Finset.mem_image,mem_edgeBlockSet]
  constructor
  · rintro ⟨a,⟨s,rfl⟩,rfl⟩
    exact ⟨s,rfl⟩
  · rintro ⟨s,rfl⟩
    exact ⟨_,⟨s,rfl⟩,rfl⟩

lemma mem_vertexCode_iff (v : Vertex n) (z : HF (Atom b)) :
    z ∈ elements (vertexCode b v) ↔ ∃ s : Configuration b v, z = atom (.inr ⟨v,s⟩) := by
  simp only [vertexCode,stateCode,elements_ofFinset,Finset.mem_image,mem_vertexBlockSet]
  constructor
  · rintro ⟨a,⟨s,rfl⟩,rfl⟩
    exact ⟨s,rfl⟩
  · rintro ⟨s,rfl⟩
    exact ⟨_,⟨s,rfl⟩,rfl⟩

lemma exists_edgeCode (e : Edge n) (P : HF (Atom b) → Prop) :
    (∃ z ∈ elements (edgeCode b e), P z) ↔ ∃ s : LocalGroup e, P (atom (.inl ⟨e,s⟩)) := by
  simp only [mem_edgeCode_iff]
  constructor
  · rintro ⟨_,⟨s,rfl⟩,h⟩
    exact ⟨s,h⟩
  · rintro ⟨s,h⟩
    exact ⟨_,⟨s,rfl⟩,h⟩

lemma exists_vertexCode (v : Vertex n) (P : HF (Atom b) → Prop) :
    (∃ z ∈ elements (vertexCode b v), P z) ↔ ∃ s : Configuration b v, P (atom (.inr ⟨v,s⟩)) := by
  simp only [mem_vertexCode_iff]
  constructor
  · rintro ⟨_,⟨s,rfl⟩,h⟩
    exact ⟨s,h⟩
  · rintro ⟨s,h⟩
    exact ⟨_,⟨s,rfl⟩,h⟩

@[simp] lemma atom_mem_edgeCode (e d : Edge n) (s : LocalGroup e) :
    atom (.inl ⟨e,s⟩) ∈ elements (edgeCode b d) ↔ e=d := by
  rw [mem_edgeCode_iff]
  constructor
  · rintro ⟨t,ht⟩
    exact congrArg Sigma.fst (Sum.inl.inj (atom_injective ht))
  · rintro rfl
    exact ⟨s,rfl⟩

lemma input_inc_iff (v : Vertex n) (c : Configuration b v) (e : Edge n) (s : LocalGroup e) :
    inputHF (atomInput b) .I (atom (.inr ⟨v,c⟩)) (atom (.inl ⟨e,s⟩)) = true ↔
      ∃ h : incident v e, c.state ⟨e,h⟩ = s := by
  rw [inputHF_atoms]
  change decide (AtomRelation b .I (.inr ⟨v,c⟩) (.inl ⟨e,s⟩)) = true ↔ _
  rw [decide_eq_true_eq]
  constructor
  · intro h
    cases h with | inc v c e => exact ⟨e.property,rfl⟩
  · rintro ⟨h,rfl⟩
    exact .inc v c ⟨e,h⟩

namespace QuotedGrid

open QuotedTerm QuotedFormula SourceSyntax

variable {k : ℕ}

lemma meaning_adjacentMatch (env : Fin k → HF (Atom b)) (ft st tt : QuotedTerm k)
    (C : CycleFrame n) (i j : Fin 4) (s : LocalGroup (C.edge i)) (t : LocalGroup (C.edge j))
    (hf : ft.meaning (atomInput b) env = frameCode b C)
    (hs : st.meaning (atomInput b) env = atom (.inl ⟨C.edge i,s⟩))
    (ht : tt.meaning (atomInput b) env = atom (.inl ⟨C.edge j,t⟩)) :
    (adjacentMatch ft st tt i j).meaning (atomInput b) env ↔ C.Across (b := b) i j s t := by
  have hv := meaning_fv_pair env ft C.vertex C.edge hf
  have he := meaning_fe_pair env ft C.vertex C.edge hf
  have hj : C.vertex (if j=next4 i then j else i) = C.joint i j := by
    by_cases h : j=i+1 <;> simp [next4_eq_add,CycleFrame.joint,h]
  simp only [adjacentMatch,meaning_allList,List.mem_cons,List.mem_nil_iff,forall_eq_or_imp,
    forall_false,implies_true,and_true,meaning_mem,hs,ht,he,atom_mem_edgeCode,meaning_existsIn,hv,hj,
    exists_vertexCode,meaning_and,meaning_input,meaning_var,
    Fin.cons_zero,QuotedTerm.meaning_up,input_inc_iff,true_and]
  constructor
  · rintro ⟨c,⟨hi,hs⟩,⟨hj,ht⟩⟩
    exact ⟨hi,hj,c,hs,ht⟩
  · rintro ⟨hi,hj,c,hs,ht⟩
    exact ⟨c,⟨hi,hs⟩,⟨hj,ht⟩⟩

lemma meaning_matchFace (env : Fin k → HF (Atom b)) (ft st tt : QuotedTerm k)
    (C : CycleFrame n) (i j : Fin 4) (s : LocalGroup (C.edge i)) (t : LocalGroup (C.edge j))
    (hf : ft.meaning (atomInput b) env = frameCode b C)
    (hs : st.meaning (atomInput b) env = atom (.inl ⟨C.edge i,s⟩))
    (ht : tt.meaning (atomInput b) env = atom (.inl ⟨C.edge j,t⟩)) :
    (matchFace ft st tt).meaning (atomInput b) env ↔ C.Match (b := b) i j s t := by
  have he := meaning_fe_pair env ft C.vertex C.edge hf
  simp only [matchFace,meaning_anyFin,meaning_and,meaning_mem,hs,ht,he,
    atom_mem_edgeCode,C.edge_injective.eq_iff,exists_and_left,exists_eq_left']
  simp only [adjacent_index_iff]
  unfold CycleFrame.Match
  split_ifs with h
  · exact meaning_adjacentMatch env ft st tt C i j s t hf hs ht
  · simp only [meaning_existsIn,he,next4_eq_add,_root_.OAI.WitnessedSeparation.Grid.exists_edgeCode,
      meaning_and]
    apply exists_congr
    intro q
    exact and_congr (meaning_adjacentMatch (Fin.cons _ env) ft.up st.up (var 0) C i (i+1) s q hf hs rfl)
      (meaning_adjacentMatch (Fin.cons _ env) ft.up tt.up (var 0) C j (i+1) t q hf ht rfl)

end QuotedGrid

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.TreeTest

variable {n : ℕ}

lemma edgeGraph_erase (T : Finset (Edge n)) (h : Edge n) :
    edgeGraph (T.erase h) = (edgeGraph T).deleteEdges {symEdge h} := by
  apply SimpleGraph.edgeSet_injective
  rw [SimpleGraph.edgeSet_deleteEdges]
  apply Set.ext
  intro q
  rw [← SimpleGraph.mem_edgeFinset,edgeGraph_edgeFinset]
  simp only [Set.mem_sdiff, Set.mem_singleton_iff]
  rw [← SimpleGraph.mem_edgeFinset,edgeGraph_edgeFinset]
  simp only [Finset.mem_image,Finset.mem_erase]
  constructor
  · rintro ⟨e,⟨he,heT⟩,rfl⟩
    exact ⟨⟨e,heT,rfl⟩,fun hh => he (symEdge_injective hh)⟩
  · rintro ⟨⟨e,heT,rfl⟩,he⟩
    exact ⟨e,⟨fun hh => he (congrArg symEdge hh),heT⟩,rfl⟩

lemma cut_cover (T : Finset (Edge n)) (hT : (edgeGraph T).Connected) (h : Edge n) (v : Vertex n) :
    (edgeGraph (T.erase h)).Reachable (head h) v ∨
      (edgeGraph (T.erase h)).Reachable (tail h) v := by
  have transport {u v : Vertex n} (p : (edgeGraph T).Walk u v) :
      ((edgeGraph (T.erase h)).Reachable (head h) u ∨
       (edgeGraph (T.erase h)).Reachable (tail h) u) →
      ((edgeGraph (T.erase h)).Reachable (head h) v ∨
       (edgeGraph (T.erase h)).Reachable (tail h) v) := by
    induction p with
    | nil => exact id
    | @cons u w v hadj p ih =>
      intro hu
      apply ih
      obtain ⟨e,he,hh⟩ := hadj
      by_cases heh : e = h
      · subst e
        rcases hh with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact Or.inl .rfl
        · exact Or.inr .rfl
      · have hw : (edgeGraph (T.erase h)).Adj u w := ⟨e,Finset.mem_erase.mpr ⟨heh,he⟩,hh⟩
        exact hu.imp (fun x => x.trans hw.reachable) (fun x => x.trans hw.reachable)
  exact transport (hT (head h) v).some (Or.inl .rfl)

namespace ParentEdges

variable {T : RootedTree (Vertex n)} (P : ParentEdges T)

lemma cut_separated (h : Edge n) (hh : h ∈ P.treeEdges) :
    ¬(P.cut h).Reachable (tail h) (head h) := by
  have ha : (edgeGraph P.treeEdges).Adj (tail h) (head h) := ⟨h,hh,Or.inl ⟨rfl,rfl⟩⟩
  have hb := (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp P.graph_isTree.isAcyclic) ha
  simpa only [SimpleGraph.isBridge_iff,cut,edgeGraph_erase,symEdge] using hb

lemma cut_reachable_iff (h : Edge n) (_hh : h ∈ P.treeEdges) (u v : Vertex n) :
    (P.cut h).Reachable u v ↔
      ((P.cut h).Reachable (head h) u ↔ (P.cut h).Reachable (head h) v) := by
  constructor
  · intro huv
    exact ⟨fun hu => hu.trans huv,fun hv => hv.trans huv.symm⟩
  · intro huv
    rcases cut_cover P.treeEdges P.graph_connected h u with hu | hu
    · exact hu.symm.trans (huv.mp hu)
    · rcases cut_cover P.treeEdges P.graph_connected h v with hv | hv
      · exact (huv.mpr hv).symm.trans hv
      · exact hu.symm.trans hv

lemma cutIndicator_head (h : Edge n) : P.cutIndicator h (head h) = 1 := by
  simp [cutIndicator,SimpleGraph.Reachable.rfl]

lemma cutIndicator_tail (h : Edge n) (hh : h ∈ P.treeEdges) : P.cutIndicator h (tail h) = 0 := by
  rw [cutIndicator,ite_eq_right (fun hth => P.cut_separated h hh hth.symm)]

lemma cutIndicator_eq (h : Edge n) {u v : Vertex n} (huv : (P.cut h).Reachable u v) :
    P.cutIndicator h u = P.cutIndicator h v := by
  have he : (P.cut h).Reachable (head h) u ↔ (P.cut h).Reachable (head h) v :=
    ⟨fun hu => hu.trans huv, fun hv => hv.trans huv.symm⟩
  simp only [cutIndicator,he]

lemma cut_gradient_self (h : Edge n) (hh : h ∈ P.treeEdges) :
    gradient (P.cutIndicator h) h = 1 := by
  rw [gradient,P.cutIndicator_head,P.cutIndicator_tail h hh,sub_zero]

lemma cut_gradient_other (h f : Edge n) (hf : f ∈ P.treeEdges) (hne : f ≠ h) :
    gradient (P.cutIndicator h) f = 0 := by
  have ha : (P.cut h).Adj (tail f) (head f) := ⟨f,Finset.mem_erase.mpr ⟨hne,hf⟩,Or.inl ⟨rfl,rfl⟩⟩
  rw [gradient,P.cutIndicator_eq h ha.reachable,sub_self]

lemma flow_cut (e : Edge n) (he : e ∉ P.treeEdges) (a : Scalar)
    (h : Edge n) (hh : h ∈ P.treeEdges) :
    (P.flow e a).val h =
      (P.cutIndicator h (tail e) - P.cutIndicator h (head e)) * a := by
  have hhe : h ≠ e := by intro hhe; subst h; exact he hh
  have hp := pairing_gradient_flow (P.cutIndicator h) (P.flow e a)
  change (∑ f, gradient (P.cutIndicator h) f * (P.flow e a).val f) = 0 at hp
  have hs : (∑ f, gradient (P.cutIndicator h) f * (P.flow e a).val f) =
      gradient (P.cutIndicator h) h * (P.flow e a).val h +
      gradient (P.cutIndicator h) e * (P.flow e a).val e := by
    apply Fintype.sum_eq_add _ _ hhe
    rintro f ⟨hfh,hfe⟩
    by_cases hf : f ∈ P.treeEdges
    · rw [P.cut_gradient_other h f hf hfh,zero_mul]
    · rw [P.flow_other e f hf hfe a,mul_zero]
  rw [hs,P.cut_gradient_self h hh,one_mul,P.flow_self e he a,gradient] at hp
  linear_combination hp

end ParentEdges

end

end WitnessedSeparation.Grid


section

namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary QuotedTerm

namespace QuotedFormula

variable {k : ℕ} {A V : Type} [Fintype A] [Fintype V]

lemma meaning_connected (S : Input A) (env : Fin k → HF A)
    (RT ut vt : QuotedTerm k) (code : V → HF A) (hc : Function.Injective code)
    (G : SimpleGraph V) (u v : V)
    (hR : RT.meaning S env = ofFinset ((BFS.closure G (Fintype.card A)).image (distanceCode code)))
    (hu : ut.meaning S env = code u) (hv : vt.meaning S env = code v)
    (hcard : Fintype.card V ≤ Fintype.card A) :
    (connected RT ut vt).meaning S env ↔ G.Reachable u v := by
  simp only [connected,meaning_mem,meaning_triple,hu,hv,meaning_card,meaning_atoms,hR]
  rw [show cardHF (stateCode (Finset.univ : Finset A)) = ordinal (Fintype.card A) by
    simp [cardHF,stateCode,Finset.card_image_of_injective _ atom_injective]]
  change HFTriple (code u) (code v) (ordinal (Fintype.card A)) ∈
    elements (ofFinset ((BFS.closure G (Fintype.card A)).image (distanceCode code))) ↔ _
  rw [coded_closure_mem code hc G u v _ le_rfl]
  constructor
  · rintro ⟨w,_⟩
    exact ⟨w⟩
  · intro h
    obtain ⟨w,hw⟩ := h.exists_isPath
    exact ⟨w,(Nat.le_of_lt hw.length_lt).trans hcard⟩

end QuotedFormula

end

end WitnessedChoice.BGS

namespace WitnessedSeparation.Grid

noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

namespace QuotedGrid

open QuotedTerm QuotedFormula SourceSyntax

variable {k : ℕ}

lemma meaning_connWithout (env : Fin k → HF (Atom b)) (HT ht ut vt : QuotedTerm k)
    (T : Finset (Edge n)) (h : Edge n) (u v : Vertex n)
    (hH : HT.meaning (atomInput b) env = connTableCode b T)
    (hh : ht.meaning (atomInput b) env = edgeCode b h)
    (hu : ut.meaning (atomInput b) env = vertexCode b u)
    (hv : vt.meaning (atomInput b) env = vertexCode b v) (hn : 1 ≤ n) :
    (connWithout HT ht ut vt).meaning (atomInput b) env ↔
      h ∈ T ∧ (edgeGraph (T.erase h)).Reachable u v := by
  have hm (e : Edge n) := QuotedFormula.meaning_connected (atomInput b)
    (Fin.cons (Hereditary.pair (edgeCode b e) (distancesCode b (edgeGraph (T.erase e)))) env)
    (var 0).snd ut.up vt.up (vertexCode b) (vertexCode_injective hn) (edgeGraph (T.erase e)) u v
    (meaning_snd_of_eq _ _ _ _ _ rfl) hu hv (vertex_card_le_atoms hn)
  simp only [connWithout,meaning_existsIn,hH,connTableCode,elements_ofFinset,Finset.mem_image,
    exists_exists_and_eq_and,meaning_and,meaning_eq,meaning_fst,meaning_var,Fin.cons_zero,
    firstHF_pair (atomInput b),QuotedTerm.meaning_up,hh,edgeCode_injective.eq_iff,hm]
  constructor
  · rintro ⟨a,ha,rfl,hr⟩
    exact ⟨ha,hr⟩
  · rintro ⟨hh,hr⟩
    exact ⟨h,hh,rfl,hr⟩

end QuotedGrid

end

end WitnessedSeparation.Grid

end


namespace WitnessedSeparation.Grid





noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary QuotedTerm

variable {n : ℕ} {b : Vertex n → Scalar}

lemma mem_traversalCode (T : Finset (Edge n)) (e : Edge n) (u v : Vertex n) (z : HF (Atom b)) :
    z ∈ elements (traversalCode b T e u v) ↔ ∃ h a c,
      Traverses T e u v h a c ∧ HFTriple (edgeCode b h) (vertexCode b a) (vertexCode b c) = z := by
  simp only [traversalCode,elements_ofFinset,Finset.mem_image,Finset.mem_filter,
    Finset.mem_univ,true_and,Prod.exists]

namespace QuotedGrid

open QuotedTerm QuotedFormula SourceSyntax

variable {k : ℕ}

lemma meaning_traversal (env : Fin k → HF (Atom b)) (VT TT HT et ut vt : QuotedTerm k)
    (T : Finset (Edge n)) (e : Edge n) (u v : Vertex n)
    (hV : VT.meaning (atomInput b) env = ofFinset (Finset.univ.image (vertexCode b)))
    (hT : TT.meaning (atomInput b) env = ofFinset (T.image (edgeCode b)))
    (hH : HT.meaning (atomInput b) env = connTableCode b T)
    (he : et.meaning (atomInput b) env = edgeCode b e)
    (hu : ut.meaning (atomInput b) env = vertexCode b u)
    (hv : vt.meaning (atomInput b) env = vertexCode b v) (hn : 1 ≤ n) :
    (traversal VT TT HT et ut vt).meaning (atomInput b) env = traversalCode b T e u v := by
  have hend (h : Edge n) (a c : Vertex n) := meaning_hasEndpoints
    (Fin.cons (vertexCode b c) (Fin.cons (vertexCode b a) (Fin.cons (edgeCode b h) env)))
    (var 2) (var 1) (var 0) h a c rfl rfl rfl hn
  have h0 (h : Edge n) (a c : Vertex n) := meaning_connWithout
    (Fin.cons (vertexCode b c) (Fin.cons (vertexCode b a) (Fin.cons (edgeCode b h) env)))
    HT.up.up.up (var 2) vt.up.up.up ut.up.up.up T h v u hH rfl hv hu hn
  have h1 (h : Edge n) (a c : Vertex n) := meaning_connWithout
    (Fin.cons (vertexCode b c) (Fin.cons (vertexCode b a) (Fin.cons (edgeCode b h) env)))
    HT.up.up.up (var 2) vt.up.up.up (var 1) T h v a hH rfl hv rfl hn
  have h2 (h : Edge n) (a c : Vertex n) := meaning_connWithout
    (Fin.cons (vertexCode b c) (Fin.cons (vertexCode b a) (Fin.cons (edgeCode b h) env)))
    HT.up.up.up (var 2) ut.up.up.up (var 0) T h u c hH rfl hu rfl hn
  rw [traversal,meaning_cup]
  apply ofFinset_inj.mpr
  ext z
  simp only [meaning_singleton,Hereditary.singleton,meaning_triple,he,hu,hv,
    elements_ofFinset,Finset.mem_union,Finset.mem_singleton,meaning_bind,
    QuotedTerm.meaning_up,hT,hV,Finset.mem_biUnion,Finset.mem_image,Finset.mem_univ,true_and,
    meaning_map,QuotedTerm.meaning_filter,Finset.mem_filter,
    meaning_var,Fin.cons_zero,Fin.cons_one,fin_cons_two]
  constructor
  · rintro (hz | ⟨_,⟨h,hh,rfl⟩,_,⟨a,rfl⟩,_,⟨⟨c,rfl⟩,hq⟩,hz⟩)
    · exact ⟨(e,u,v),Or.inl ⟨rfl,rfl,rfl⟩,hz.symm⟩
    · simp only [meaning_allList,List.mem_cons,List.not_mem_nil,forall_eq_or_imp,
        forall_false,implies_true,and_true,meaning_neg,hend,h0,h1,h2] at hq
      exact ⟨(h,a,c),Or.inr ⟨hh,hq.1,fun hr => hq.2.1 ⟨hh,hr⟩,hq.2.2.1.2,hq.2.2.2.2⟩,hz⟩
  · rintro ⟨⟨h,a,c⟩,htr,hz⟩
    rcases htr with ⟨rfl,rfl,rfl⟩ | ⟨hh,hends,hvu,hva,huc⟩
    · exact Or.inl hz.symm
    · refine Or.inr ⟨edgeCode b h,⟨h,hh,rfl⟩,vertexCode b a,⟨a,rfl⟩,
        vertexCode b c,⟨⟨c,rfl⟩,?_⟩,hz⟩
      simpa only [meaning_allList,List.mem_cons,List.not_mem_nil,forall_eq_or_imp,
        forall_false,implies_true,and_true,meaning_neg,hend,h0,h1,h2] using
        (show ((a=tail h ∧ c=head h) ∨ (c=tail h ∧ a=head h)) ∧
          ¬(h ∈ T ∧ (edgeGraph (T.erase h)).Reachable v u) ∧
          (h ∈ T ∧ (edgeGraph (T.erase h)).Reachable v a) ∧
          (h ∈ T ∧ (edgeGraph (T.erase h)).Reachable u c) from
            ⟨hends,fun hr => hvu hr.2,⟨hh,hva⟩,⟨hh,huc⟩⟩)

end QuotedGrid

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

namespace QuotedGrid

open QuotedTerm QuotedFormula SourceSyntax

variable {k : ℕ}

lemma meaning_side (env : Fin k → HF (Atom b)) (ft et : QuotedTerm k)
    (C : CycleFrame n) (e : Edge n)
    (hf : ft.meaning (atomInput b) env = frameCode b C)
    (he : et.meaning (atomInput b) env = edgeCode b e) :
    (side ft et).meaning (atomInput b) env ↔ cycle C.face e ≠ 0 := by
  simp only [side,meaning_anyFin,meaning_eq,he,meaning_fe_pair env ft C.vertex C.edge hf,
    edgeCode_injective.eq_iff]
  exact (C.support_iff e).symm

lemma meaning_matchFace_atoms (env : Fin k → HF (Atom b)) (ft st tt : QuotedTerm k)
    (C : CycleFrame n) (e d : Edge n) (s : LocalGroup e) (t : LocalGroup d)
    (hf : ft.meaning (atomInput b) env = frameCode b C)
    (hs : st.meaning (atomInput b) env = atom (.inl ⟨e,s⟩))
    (ht : tt.meaning (atomInput b) env = atom (.inl ⟨d,t⟩))
    (he : cycle C.face e ≠ 0) (hd : cycle C.face d ≠ 0) (hn : 1 ≤ n) :
    (matchFace ft st tt).meaning (atomInput b) env ↔ s.face ⟨C.face,he⟩ = t.face ⟨C.face,hd⟩ := by
  obtain ⟨i,rfl⟩ := (C.support_iff e).mp he
  obtain ⟨j,rfl⟩ := (C.support_iff d).mp hd
  exact (meaning_matchFace env ft st tt C i j s t hf hs ht).trans (C.match_iff hn i j s t)

lemma meaning_baseEq (env : Fin k → HF (Atom b)) (F et st tt : QuotedTerm k)
    (e : Edge n) (s t : LocalGroup e)
    (hF : ∀ z, z ∈ elements (F.meaning (atomInput b) env) ↔ ∃ C : CycleFrame n, frameCode b C = z)
    (he : et.meaning (atomInput b) env = edgeCode b e)
    (hs : st.meaning (atomInput b) env = atom (.inl ⟨e,s⟩))
    (ht : tt.meaning (atomInput b) env = atom (.inl ⟨e,t⟩)) (hn : 1 ≤ n) :
    (baseEq F et st tt).meaning (atomInput b) env ↔ s.face = t.face := by
  have hside (C : CycleFrame n) := meaning_side (Fin.cons (frameCode b C) env) (var 0) et.up C e rfl he
  simp only [baseEq,meaning_allIn,hF,forall_exists_index,forall_apply_eq_imp_iff,meaning_imp,hside]
  constructor
  · intro h
    funext f
    have hf : cycle (standardFrame f.val).face e ≠ 0 := by simpa using f.property
    simpa only [standardFrame_face] using (meaning_matchFace_atoms (Fin.cons (frameCode b (standardFrame f.val)) env)
      (var 0) st.up tt.up _ e e s t rfl hs ht hf hf hn).mp (h _ hf)
  · intro h C hC
    apply (meaning_matchFace_atoms (Fin.cons (frameCode b C) env) (var 0) st.up tt.up C e e s t rfl hs ht hC hC hn).mpr
    exact congrFun h ⟨C.face,hC⟩

end QuotedGrid

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary QuotedTerm

variable {n : ℕ} {b : Vertex n → Scalar}

lemma exists_traversalCode (T : Finset (Edge n)) (e : Edge n) (u v : Vertex n)
    (Q : HF (Atom b) → Prop) :
    (∃ z ∈ elements (traversalCode b T e u v), Q z) ↔
      ∃ h a c, Traverses T e u v h a c ∧ Q (HFTriple (edgeCode b h) (vertexCode b a) (vertexCode b c)) := by
  constructor
  · rintro ⟨z,hz,hQ⟩
    obtain ⟨h,a,c,htr,rfl⟩ := (mem_traversalCode T e u v z).mp hz
    exact ⟨h,a,c,htr,hQ⟩
  · rintro ⟨h,a,c,htr,hQ⟩
    exact ⟨_,(mem_traversalCode T e u v _).mpr ⟨h,a,c,htr,rfl⟩,hQ⟩

lemma input_z_iff (e : Edge n) (s t : LocalGroup e) (δ : Scalar) :
    inputHF (atomInput b) (.Z δ) (atom (.inl ⟨e,s⟩)) (atom (.inl ⟨e,t⟩)) = true ↔
      (s⁻¹*t).flow = δ := by
  rw [inputHF_atoms]
  change decide (AtomRelation b (.Z δ) (.inl ⟨e,s⟩) (.inl ⟨e,t⟩)) = true ↔ _
  rw [decide_eq_true_eq]
  constructor
  · intro h; cases h with | z e s t δ h => exact h
  · intro h; exact .z e s t δ h

namespace QuotedGrid

open QuotedFormula SourceSyntax

variable {k : ℕ}

lemma meaning_traversalEdge (env : Fin k → HF (Atom b)) (Γ ht : QuotedTerm k)
    (T : Finset (Edge n)) (e : Edge n) (u v : Vertex n) (h : Edge n)
    (hΓ : Γ.meaning (atomInput b) env = traversalCode b T e u v)
    (hh : ht.meaning (atomInput b) env = edgeCode b h) :
    (traversalEdge Γ ht).meaning (atomInput b) env ↔ ∃ a c, Traverses T e u v h a c := by
  simp only [traversalEdge,meaning_existsIn,hΓ,exists_traversalCode,
    meaning_eq,meaning_fst,meaning_var,Fin.cons_zero,HFTriple,firstHF_pair (atomInput b),
    QuotedTerm.meaning_up,hh,edgeCode_injective.eq_iff]
  constructor
  · rintro ⟨d,a,c,htr,rfl⟩
    exact ⟨a,c,htr⟩
  · rintro ⟨a,c,htr⟩
    exact ⟨h,a,c,htr,rfl⟩

lemma meaning_directedZ (env : Fin k → HF (Atom b)) (R Γ ot ht st tt : QuotedTerm k)
    (T : Finset (Edge n)) (e : Edge n) (u v : Vertex n) (o : Vertex n)
    (h : Edge n) (s t : LocalGroup h)
    (hR : R.meaning (atomInput b) env = distancesCode b (boxGraph n))
    (hΓ : Γ.meaning (atomInput b) env = traversalCode b T e u v)
    (ho : ot.meaning (atomInput b) env = vertexCode b o)
    (hh : ht.meaning (atomInput b) env = edgeCode b h)
    (hs : st.meaning (atomInput b) env = atom (.inl ⟨h,s⟩))
    (ht' : tt.meaning (atomInput b) env = atom (.inl ⟨h,t⟩)) (hn : 1 ≤ n) :
    (directedZ R Γ ot ht st tt).meaning (atomInput b) env ↔ ∃ a c,
      Traverses T e u v h a c ∧
        if (boxGraph n).dist o a < (boxGraph n).dist o c then
          (s⁻¹*t).flow = 1 else (s⁻¹*t).flow = 2 := by
  have hd1 (d : Edge n) (a c : Vertex n) :
      (distanceAt R.up ot.up (var 0).snd.fst).meaning (atomInput b)
        (Fin.cons (HFTriple (edgeCode b d) (vertexCode b a) (vertexCode b c)) env) =
      ordinal ((boxGraph n).dist o a) := by
    have hRu : R.up.meaning (atomInput b)
        (Fin.cons (HFTriple (edgeCode b d) (vertexCode b a) (vertexCode b c)) env) =
        distancesCode b (boxGraph n) := hR
    have hov : ot.up.meaning (atomInput b)
        (Fin.cons (HFTriple (edgeCode b d) (vertexCode b a) (vertexCode b c)) env) = vertexCode b o := ho
    have hav : ((var 0).snd.fst : QuotedTerm (k+1)).meaning (atomInput b)
        (Fin.cons (HFTriple (edgeCode b d) (vertexCode b a) (vertexCode b c)) env) = vertexCode b a := by
      simp only [meaning_fst,meaning_snd,meaning_var,Fin.cons_zero,HFTriple,
        secondHF_pair (atomInput b),firstHF_pair (atomInput b)]
    exact meaning_distanceAt (atomInput b) _ R.up ot.up (var 0).snd.fst
      (vertexCode b) (vertexCode_injective hn) (boxGraph n) (boxGraph_connected n) o a
      hRu hov hav (vertex_card_le_atoms hn)
  have hd2 (d : Edge n) (a c : Vertex n) :
      (distanceAt R.up ot.up (var 0).snd.snd).meaning (atomInput b)
        (Fin.cons (HFTriple (edgeCode b d) (vertexCode b a) (vertexCode b c)) env) =
      ordinal ((boxGraph n).dist o c) := by
    have hRu : R.up.meaning (atomInput b)
        (Fin.cons (HFTriple (edgeCode b d) (vertexCode b a) (vertexCode b c)) env) =
        distancesCode b (boxGraph n) := hR
    have hov : ot.up.meaning (atomInput b)
        (Fin.cons (HFTriple (edgeCode b d) (vertexCode b a) (vertexCode b c)) env) = vertexCode b o := ho
    have hcv : ((var 0).snd.snd : QuotedTerm (k+1)).meaning (atomInput b)
        (Fin.cons (HFTriple (edgeCode b d) (vertexCode b a) (vertexCode b c)) env) = vertexCode b c := by
      simp only [meaning_snd,meaning_var,Fin.cons_zero,HFTriple,secondHF_pair (atomInput b)]
    exact meaning_distanceAt (atomInput b) _ R.up ot.up (var 0).snd.snd
      (vertexCode b) (vertexCode_injective hn) (boxGraph n) (boxGraph_connected n) o c
      hRu hov hcv (vertex_card_le_atoms hn)
  simp only [HFTriple] at hd1 hd2
  simp only [directedZ,meaning_existsIn,hΓ,exists_traversalCode,
    meaning_and,meaning_eq,meaning_fst,meaning_var,Fin.cons_zero,HFTriple,firstHF_pair (atomInput b),
    QuotedTerm.meaning_up,hh,edgeCode_injective.eq_iff,meaning_or,meaning_mem,meaning_neg,
    meaning_input,hs,ht',input_z_iff]
  constructor
  · rintro ⟨d,a,c,htr,hd,hZ⟩
    subst d
    refine ⟨a,c,htr,?_⟩
    change (_ ∧ _) ∨ (¬_ ∧ _) at hZ
    rw [hd1,hd2,ordinal_mem_elements] at hZ
    split_ifs with hl
    · exact hZ.elim And.right (fun hz => False.elim (hz.1 hl))
    · exact hZ.elim (fun hz => False.elim (hl hz.1)) And.right
  · rintro ⟨a,c,htr,hZ⟩
    refine ⟨h,a,c,htr,rfl,?_⟩
    rw [hd1,hd2,ordinal_mem_elements]
    split_ifs at hZ with hl
    · exact Or.inl ⟨hl,hZ⟩
    · exact Or.inr ⟨hl,hZ⟩

end QuotedGrid

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.TreeTest

variable {n : ℕ}

namespace ParentEdges

variable {T : RootedTree (Vertex n)} (P : ParentEdges T)

lemma cut_reachable_tail_iff (h : Edge n) (hh : h ∈ P.treeEdges) (v : Vertex n) :
    (P.cut h).Reachable v (tail h) ↔ ¬(P.cut h).Reachable (head h) v := by
  constructor
  · intro hv hh'
    exact P.cut_separated h hh (hh'.trans hv).symm
  · intro hv
    rcases cut_cover P.treeEdges P.graph_connected h v with h' | h'
    · exact False.elim (hv h')
    · exact h'.symm

lemma cut_reachable_head_iff (h : Edge n) (v : Vertex n) :
    (P.cut h).Reachable v (head h) ↔ (P.cut h).Reachable (head h) v :=
  ⟨SimpleGraph.Reachable.symm,SimpleGraph.Reachable.symm⟩

lemma traverses_forward (e : Edge n) (he : e ∉ P.treeEdges) (h : Edge n) :
    Traverses P.treeEdges e (tail e) (head e) h (tail h) (head h) ↔
      (P.flow e 1).val h = 1 := by
  by_cases hhe : h=e
  · subst h
    simp [Traverses,he,P.flow_self e he]
  by_cases hh : h ∈ P.treeEdges
  · have hf := P.flow_cut e he 1 h hh
    have hr := P.cut_reachable_iff h hh (head e) (tail e)
    have ht := P.cut_reachable_tail_iff h hh (head e)
    have hu := P.cut_reachable_head_iff h (tail e)
    change _ ↔ _ at hr ht hu
    simp only [Traverses,hhe,false_and,false_or,hh,true_and,
      and_self,true_or,head_ne_tail h,Ne.symm (head_ne_tail h)]
    change (¬(P.cut h).Reachable (head e) (tail e) ∧
      (P.cut h).Reachable (head e) (tail h) ∧ (P.cut h).Reachable (tail e) (head h)) ↔ _
    rw [hr,ht,hu,hf,mul_one]
    unfold cutIndicator
    by_cases ha : (P.cut h).Reachable (head h) (tail e) <;>
      by_cases hb : (P.cut h).Reachable (head h) (head e) <;> simp [ha,hb] ; decide
  · rw [P.flow_other e h hh hhe 1]
    simp [Traverses,hhe,hh]

lemma traverses_reverse (e : Edge n) (he : e ∉ P.treeEdges) (h : Edge n) :
    Traverses P.treeEdges e (tail e) (head e) h (head h) (tail h) ↔
      (P.flow e 1).val h = -1 := by
  by_cases hhe : h=e
  · subst h
    simp [Traverses,he,P.flow_self e he,head_ne_tail] ; decide
  by_cases hh : h ∈ P.treeEdges
  · have hf := P.flow_cut e he 1 h hh
    have hr := P.cut_reachable_iff h hh (head e) (tail e)
    have ht := P.cut_reachable_tail_iff h hh (tail e)
    have hu := P.cut_reachable_head_iff h (head e)
    simp only [Traverses,hhe,false_and,false_or,hh,true_and,and_self,
      or_true,head_ne_tail h,Ne.symm (head_ne_tail h)]
    change (¬(P.cut h).Reachable (head e) (tail e) ∧
      (P.cut h).Reachable (head e) (head h) ∧ (P.cut h).Reachable (tail e) (tail h)) ↔ _
    rw [hr,ht,hu,hf,mul_one]
    unfold cutIndicator
    by_cases ha : (P.cut h).Reachable (head h) (tail e) <;>
      by_cases hb : (P.cut h).Reachable (head h) (head e) <;> simp [ha,hb] ; decide
  · rw [P.flow_other e h hh hhe 1]
    simp [Traverses,hhe,hh]

lemma traverses_endpoints {e h : Edge n} {u v : Vertex n}
    (htr : Traverses P.treeEdges e (tail e) (head e) h u v) :
    (u=tail h ∧ v=head h) ∨ (v=tail h ∧ u=head h) := by
  rcases htr with ⟨rfl,rfl,rfl⟩ | ⟨_,hh,_⟩
  · exact Or.inl ⟨rfl,rfl⟩
  · exact hh

end ParentEdges

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS WitnessedChoice.TreeTest Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

lemma scalar_cases (a : Scalar) : a=0 ∨ a=1 ∨ a= -1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

namespace ParentEdges

variable {T : RootedTree (Vertex n)} (P : ParentEdges T)

lemma traverses_iff_nonzero (e : Edge n) (he : e ∉ P.treeEdges) (h : Edge n) :
    (∃ a c, Traverses P.treeEdges e (tail e) (head e) h a c) ↔ (P.flow e 1).val h ≠ 0 := by
  constructor
  · rintro ⟨a,c,htr⟩
    rcases P.traverses_endpoints htr with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · rw [(P.traverses_forward e he h).mp htr]; decide
    · rw [(P.traverses_reverse e he h).mp htr]; decide
  · intro hne
    rcases scalar_cases ((P.flow e 1).val h) with hz | hp | hm
    · exact False.elim (hne hz)
    · exact ⟨tail h,head h,(P.traverses_forward e he h).mpr hp⟩
    · exact ⟨head h,tail h,(P.traverses_reverse e he h).mpr hm⟩

end ParentEdges

lemma local_central_iff (h : Edge n) (s t : LocalGroup h) (z : Scalar) :
    t = (⟨0,z⟩ : LocalGroup h) * s ↔ s.face = t.face ∧ (s⁻¹*t).flow = z := by
  constructor
  · rintro rfl
    simp only [Support.H.mul_face,zero_add,true_and,Support.H.mul_flow,Support.H.inv_flow,
      Support.H.inv_face,Support.correction_zero_left,add_zero,Support.correction_neg_left,
      Support.correction_self,neg_zero]
    abel
  · rintro ⟨hf,hz⟩
    apply Support.H.ext
    · simpa only [Support.H.mul_face,zero_add] using hf.symm
    · simp only [Support.H.mul_flow,Support.H.inv_flow,Support.H.inv_face,←hf,
        Support.correction_neg_left,Support.correction_self,neg_zero,add_zero] at hz
      simp only [Support.H.mul_flow,Support.correction_zero_left,add_zero]
      rw [←hz]
      abel

end

end WitnessedSeparation.Grid

end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_TreeCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace WitnessedSeparation.Grid

noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS WitnessedChoice.TreeTest Hereditary RelationPools

variable {n : ℕ} {b : Vertex n → Scalar}

lemma mem_edgeActionRelation (g : BoxGroup n) (a c : Atom b) :
    (a,c) ∈ edgeActionRelation g ↔
      ∃ (e : Edge n) (s : LocalGroup e), a = .inl ⟨e,s⟩ ∧ c = .inl ⟨e,restrictGroup e g*s⟩ := by
  simp only [edgeActionRelation,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨⟨e,s⟩,h⟩
    cases h
    exact ⟨e,s,rfl,rfl⟩
  · rintro ⟨e,s,rfl,rfl⟩
    exact ⟨⟨e,s⟩,rfl⟩

namespace QuotedGrid

open QuotedTerm QuotedFormula SourceSyntax

variable {k : ℕ} {T : RootedTree (Vertex n)}

lemma exists_edgeCode (Q : HF (Atom b) → Prop) :
    (∃ z ∈ elements (ofFinset (Finset.univ.image (edgeCode b))), Q z) ↔
      ∃ e : Edge n, Q (edgeCode b e) := by
  simp only [elements_ofFinset,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨z,⟨e,rfl⟩,h⟩
    exact ⟨e,h⟩
  · rintro ⟨e,h⟩
    exact ⟨_,⟨e,rfl⟩,h⟩

end QuotedGrid

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS WitnessedChoice.TreeTest Hereditary RelationPools

variable {n : ℕ} {b : Vertex n → Scalar}

lemma mem_configActionRelation (g : BoxGroup n) (a c : Atom b) :
    (a,c) ∈ configActionRelation g ↔
      ∃ (v : Vertex n) (s : Configuration b v), a = .inr ⟨v,s⟩ ∧ c = .inr ⟨v,actConfiguration g s⟩ := by
  simp only [configActionRelation,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨⟨v,s⟩,h⟩
    cases h
    exact ⟨v,s,rfl,rfl⟩
  · rintro ⟨v,s,rfl,rfl⟩
    exact ⟨⟨v,s⟩,rfl⟩

lemma edge_config_union (g : BoxGroup n) :
    edgeActionRelation (b := b) g ∪ configActionRelation g = graph (actionPerm g) := by
  ext ⟨a,c⟩
  simp only [Finset.mem_union,mem_edgeActionRelation,mem_configActionRelation,mem_graph]
  cases a with
  | inl r =>
    rcases r with ⟨e,s⟩
    simp only [Sum.inl.injEq,Sum.inl_ne_inr,false_and,exists_false,or_false]
    constructor
    · rintro ⟨d,t,h,rfl⟩
      cases h
      rfl
    · intro h
      exact ⟨e,s,rfl,h.symm⟩
  | inr r =>
    rcases r with ⟨v,s⟩
    simp only [Sum.inr.injEq,Sum.inr_ne_inl,false_and,exists_false,false_or]
    constructor
    · rintro ⟨w,t,h,rfl⟩
      cases h
      rfl
    · intro h
      exact ⟨v,s,rfl,h.symm⟩

namespace QuotedGrid

open QuotedTerm QuotedFormula SourceSyntax

variable {k : ℕ}

lemma exists_vertexBlockCode (Q : HF (Atom b) → Prop) :
    (∃ z ∈ elements (ofFinset (Finset.univ.image (vertexCode b))), Q z) ↔
      ∃ v : Vertex n, Q (vertexCode b v) := by
  simp only [elements_ofFinset,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨z,⟨v,rfl⟩,h⟩
    exact ⟨v,h⟩
  · rintro ⟨v,h⟩
    exact ⟨_,⟨v,rfl⟩,h⟩

lemma all_edgeBlockCode (Q : HF (Atom b) → Prop) :
    (∀ z ∈ elements (ofFinset (Finset.univ.image (edgeCode b))), Q z) ↔
      ∀ e : Edge n, Q (edgeCode b e) := by
  simp only [elements_ofFinset,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · intro h e
    exact h _ ⟨e,rfl⟩
  · rintro h z ⟨e,rfl⟩
    exact h e

lemma pair_atoms_relationCode (r : Relation (Atom b)) (a c : Atom b) :
    Hereditary.pair (atom a) (atom c) ∈ elements (relationCode r) ↔ (a,c) ∈ r :=
  mem_elements_relationCode r a c

lemma meaning_cycleX (env : Fin k → HF (Atom b)) (V E cY : QuotedTerm k) (g : BoxGroup n)
    (hV : V.meaning (atomInput b) env = ofFinset (Finset.univ.image (vertexCode b)))
    (hE : E.meaning (atomInput b) env = ofFinset (Finset.univ.image (edgeCode b)))
    (hY : cY.meaning (atomInput b) env = relationCode (edgeActionRelation g)) (hn : 1 ≤ n) :
    (cycleX V E cY).meaning (atomInput b) env = relationCode (configActionRelation g) := by
  rw [cycleX,meaning_relation]
  apply congrArg relationCode
  ext ⟨a,c⟩
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,meaning_existsIn,QuotedTerm.meaning_up,
    hV,exists_vertexBlockCode,meaning_allList,List.mem_cons,List.mem_nil_iff,forall_eq_or_imp,
    forall_false,implies_true,and_true,meaning_mem,meaning_var,Fin.cons_zero,Fin.cons_one,fin_cons_two,
    mem_vertexCode_iff,mem_configActionRelation]
  constructor
  · rintro ⟨v,⟨s,hs⟩,⟨t,ht⟩,hm⟩
    have hs' := atom_injective hs
    have ht' := atom_injective ht
    subst a
    subst c
    refine ⟨v,s,rfl,?_⟩
    apply congrArg (fun t : Configuration b v => (Sum.inr ⟨v,t⟩ : Atom b))
    apply Configuration.ext
    intro e
    simp only [meaning_allIn,QuotedTerm.meaning_up,hE,all_edgeBlockCode] at hm
    have hh := hm e.val
    rw [meaning_imp,meaning_incident _ _ _ v e.val rfl rfl hn] at hh
    have he := hh e.property
    simp only [meaning_existsIn,meaning_var,Fin.cons_zero,Fin.cons_one,
      WitnessedSeparation.Grid.exists_edgeCode,meaning_allList,List.mem_cons,List.mem_nil_iff,
      forall_eq_or_imp,forall_false,implies_true,and_true,meaning_input,
      fin_cons_two,fin_cons_three,fin_cons_four,fin_cons_five,Fin.cons_zero,QuotedTerm.meaning_up,input_inc_iff,
      meaning_link,hY,pair_atoms_relationCode] at he
    obtain ⟨r,q,⟨hr,hsr⟩,⟨hq,htq⟩,hrel⟩ := he
    rw [mem_edgeActionRelation] at hrel
    obtain ⟨d,u,hru,hqu⟩ := hrel
    have hru' := Sum.inl.inj hru
    cases hru'
    have heq := eq_of_heq (Sigma.mk.inj (Sum.inl.inj hqu)).2
    change t.state e = restrictGroup e.val g*s.state e
    rw [hsr,htq,heq]
  · rintro ⟨v,s,rfl,rfl⟩
    refine ⟨v,⟨s,rfl⟩,⟨actConfiguration g s,rfl⟩,?_⟩
    simp only [meaning_allIn,QuotedTerm.meaning_up,hE,all_edgeBlockCode]
    intro e
    rw [meaning_imp,meaning_incident _ _ _ v e rfl rfl hn]
    intro he
    simp only [meaning_existsIn,meaning_var,Fin.cons_zero,Fin.cons_one,
      WitnessedSeparation.Grid.exists_edgeCode,meaning_allList,List.mem_cons,List.mem_nil_iff,
      forall_eq_or_imp,forall_false,implies_true,and_true,meaning_input,
      fin_cons_two,fin_cons_three,fin_cons_four,fin_cons_five,Fin.cons_zero,QuotedTerm.meaning_up,input_inc_iff,
      meaning_link,hY,pair_atoms_relationCode]
    exact ⟨s.state ⟨e,he⟩,restrictGroup e g*s.state ⟨e,he⟩,
      ⟨he,rfl⟩,⟨he,rfl⟩,(mem_edgeActionRelation _ _ _).mpr ⟨e,_,rfl,rfl⟩⟩

end QuotedGrid

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS WitnessedChoice.TreeTest Hereditary

variable {n : ℕ}

lemma dist_opposite_tail (h : Edge n) :
    (boxGraph n).dist oppositeVertex (tail h) = (boxGraph n).dist oppositeVertex (head h) + 1 := by
  rcases h with ⟨i,j,k⟩ | (⟨i,j,k⟩ | ⟨i,j,k⟩)
  all_goals
    simp only [boxGraph_dist,oppositeVertex,tail,head,Fin.val_last,Fin.val_succ,Fin.val_castSucc]
    repeat' rw [Nat.dist_eq_sub_of_le_right (by omega)]
    omega

namespace ParentEdges

variable {T : RootedTree (Vertex n)} (P : ParentEdges T)

lemma flow_neg_one (e h : Edge n) : (P.flow e (-1)).val h = -(P.flow e 1).val h := by
  simp only [flow,fundamental,Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
    neg_mul,one_mul,Pi.single_apply]
  split_ifs <;> ring

lemma traverses_iff_neg_nonzero (e : Edge n) (he : e ∉ P.treeEdges) (h : Edge n) :
    (∃ a c, Traverses P.treeEdges e (tail e) (head e) h a c) ↔ (P.flow e (-1)).val h ≠ 0 := by
  rw [P.flow_neg_one,neg_ne_zero,P.traverses_iff_nonzero e he h]

lemma opposite_directed_flow_iff (e : Edge n) (he : e ∉ P.treeEdges) (h : Edge n) (z : Scalar) :
    (∃ a c, Traverses P.treeEdges e (tail e) (head e) h a c ∧
      if (boxGraph n).dist oppositeVertex a < (boxGraph n).dist oppositeVertex c then z=1 else z=2) ↔
      (P.flow e (-1)).val h ≠ 0 ∧ z=(P.flow e (-1)).val h := by
  have hlt := dist_opposite_tail h
  have hm : (2 : Scalar) = -1 := by decide
  constructor
  · rintro ⟨a,c,htr,hz⟩
    have hne := (P.traverses_iff_neg_nonzero e he h).mp ⟨a,c,htr⟩
    refine ⟨hne,?_⟩
    rw [P.flow_neg_one]
    rcases P.traverses_endpoints htr with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · rw [(P.traverses_forward e he h).mp htr]
      simpa only [ite_eq_right (show ¬(boxGraph n).dist oppositeVertex (tail h) <
        (boxGraph n).dist oppositeVertex (head h) by omega),hm] using hz
    · rw [(P.traverses_reverse e he h).mp htr,neg_neg]
      simpa only [ite_eq_left (show (boxGraph n).dist oppositeVertex (head h) <
        (boxGraph n).dist oppositeVertex (tail h) by omega)] using hz
  · rintro ⟨hne,rfl⟩
    rw [P.flow_neg_one,neg_ne_zero] at hne
    rcases scalar_cases ((P.flow e 1).val h) with hz | hp | hm'
    · exact False.elim (hne hz)
    · refine ⟨tail h,head h,(P.traverses_forward e he h).mpr hp,?_⟩
      rw [ite_eq_right (by omega),P.flow_neg_one,hp,hm]
    · refine ⟨head h,tail h,(P.traverses_reverse e he h).mpr hm',?_⟩
      rw [ite_eq_left (by omega),P.flow_neg_one,hm',neg_neg]

end ParentEdges

end



noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS WitnessedChoice.TreeTest Hereditary RelationPools

variable {n : ℕ} {b : Vertex n → Scalar}

namespace QuotedGrid

open QuotedTerm QuotedFormula SourceSyntax

variable {k : ℕ} {T : RootedTree (Vertex n)}

lemma meaning_reverseCycleY_move (env : Fin k → HF (Atom b)) (F R Γ ot ht st tt : QuotedTerm k)
    (P : ParentEdges T) (e : Edge n) (he : e ∉ P.treeEdges) (h : Edge n) (s t : LocalGroup h)
    (hF : ∀ z, z ∈ elements (F.meaning (atomInput b) env) ↔ ∃ C : CycleFrame n, frameCode b C = z)
    (hR : R.meaning (atomInput b) env = distancesCode b (boxGraph n))
    (hΓ : Γ.meaning (atomInput b) env = traversalCode b P.treeEdges e (tail e) (head e))
    (ho : ot.meaning (atomInput b) env = vertexCode b oppositeVertex)
    (hh : ht.meaning (atomInput b) env = edgeCode b h)
    (hs : st.meaning (atomInput b) env = atom (.inl ⟨h,s⟩))
    (ht' : tt.meaning (atomInput b) env = atom (.inl ⟨h,t⟩)) (hn : 1 ≤ n) :
    (((traversalEdge Γ ht).neg.and (eq st tt)).or
      ((traversalEdge Γ ht).and ((baseEq F ht st tt).and (directedZ R Γ ot ht st tt)))).meaning (atomInput b) env ↔
      t = restrictGroup h (⟨0,P.flow e (-1)⟩ : BoxGroup n)*s := by
  rw [meaning_or,meaning_and,meaning_neg,meaning_and,meaning_and,
    meaning_traversalEdge env Γ ht P.treeEdges e (tail e) (head e) h hΓ hh,
    P.traverses_iff_neg_nonzero e he h,
    meaning_baseEq env F ht st tt h s t hF hh hs ht' hn,
    meaning_directedZ env R Γ ot ht st tt P.treeEdges e (tail e) (head e) oppositeVertex h s t
      hR hΓ ho hh hs ht' hn,
    P.opposite_directed_flow_iff e he h (s⁻¹*t).flow,meaning_eq,hs,ht']
  have ha : atom (Sum.inl ⟨h,s⟩ : Atom b) = atom (.inl ⟨h,t⟩) ↔ s=t := by
    simp only [atom_injective.eq_iff,Sum.inl.injEq,Sigma.mk.inj_iff,heq_eq_eq,true_and]
  rw [ha]
  change _ ↔ t = (⟨0,(P.flow e (-1)).val h⟩ : LocalGroup h)*s
  rw [local_central_iff]
  by_cases hz : (P.flow e (-1)).val h = 0
  · simp only [hz,not_false_eq_true,true_and,ne_eq,not_true_eq_false,false_and,or_false]
    constructor
    · rintro rfl
      simp
    · rintro ⟨hf,htf⟩
      have hh := (local_central_iff h s t 0).mpr ⟨hf,htf⟩
      simpa only [show (⟨0,0⟩ : LocalGroup h)=1 from rfl,one_mul] using hh.symm
  · tauto

lemma meaning_reverseCycleY (env : Fin k → HF (Atom b)) (E F R Γ ot : QuotedTerm k)
    (P : ParentEdges T) (e : Edge n) (he : e ∉ P.treeEdges)
    (hE : E.meaning (atomInput b) env = ofFinset (Finset.univ.image (edgeCode b)))
    (hF : ∀ z, z ∈ elements (F.meaning (atomInput b) env) ↔ ∃ C : CycleFrame n, frameCode b C = z)
    (hR : R.meaning (atomInput b) env = distancesCode b (boxGraph n))
    (hΓ : Γ.meaning (atomInput b) env = traversalCode b P.treeEdges e (tail e) (head e))
    (ho : ot.meaning (atomInput b) env = vertexCode b oppositeVertex) (hn : 1 ≤ n) :
    (cycleY E F R Γ ot).meaning (atomInput b) env =
      relationCode (edgeActionRelation (b := b) (⟨0,P.flow e (-1)⟩ : BoxGroup n)) := by
  rw [cycleY,meaning_relation]
  apply congrArg relationCode
  ext ⟨a,c⟩
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,meaning_existsIn,QuotedTerm.meaning_up,
    hE,exists_edgeCode,
    meaning_allList,List.mem_cons,List.mem_nil_iff,forall_eq_or_imp,forall_false,implies_true,and_true,
    meaning_mem,meaning_var,Fin.cons_zero,Fin.cons_one,fin_cons_two,mem_edgeCode_iff,
    mem_edgeActionRelation]
  constructor
  · rintro ⟨h,⟨s,hs⟩,⟨t,ht⟩,hm⟩
    have hs' := atom_injective hs
    have ht' := atom_injective ht
    subst a
    subst c
    have hmove := (meaning_reverseCycleY_move
      (Fin.cons (edgeCode b h) (Fin.cons (atom (.inl ⟨h,t⟩)) (Fin.cons (atom (.inl ⟨h,s⟩)) env)))
      F.up.up.up R.up.up.up Γ.up.up.up ot.up.up.up (var 0) (var 2) (var 1)
      P e he h s t hF hR hΓ ho rfl rfl rfl hn).mp hm
    exact ⟨h,s,rfl,congrArg (fun t : LocalGroup h => (Sum.inl ⟨h,t⟩ : Atom b)) hmove⟩
  · rintro ⟨h,s,rfl,rfl⟩
    refine ⟨h,⟨s,rfl⟩,⟨restrictGroup h (⟨0,P.flow e (-1)⟩ : BoxGroup n)*s,rfl⟩,?_⟩
    exact (meaning_reverseCycleY_move
      (Fin.cons (edgeCode b h) (Fin.cons (atom (.inl ⟨h,restrictGroup h (⟨0,P.flow e (-1)⟩ : BoxGroup n)*s⟩))
        (Fin.cons (atom (.inl ⟨h,s⟩)) env)))
      F.up.up.up R.up.up.up Γ.up.up.up ot.up.up.up (var 0) (var 2) (var 1)
      P e he h s _ hF hR hΓ ho rfl rfl rfl hn).mpr rfl

end QuotedGrid

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS WitnessedChoice.TreeTest Hereditary RelationPools

variable {n : ℕ} {b : Vertex n → Scalar}

namespace QuotedGrid

open QuotedTerm QuotedFormula SourceSyntax

variable {k : ℕ}

lemma meaning_cycleRelation_of_Y (env : Fin k → HF (Atom b)) (V E F R Γ ot : QuotedTerm k)
    (g : BoxGroup n)
    (hV : V.meaning (atomInput b) env = ofFinset (Finset.univ.image (vertexCode b)))
    (hE : E.meaning (atomInput b) env = ofFinset (Finset.univ.image (edgeCode b)))
    (hY : (cycleY E F R Γ ot).meaning (atomInput b) env = relationCode (edgeActionRelation g))
    (hn : 1 ≤ n) :
    (cycleRelation V E F R Γ ot).meaning (atomInput b) env = relationCode (graph (actionPerm g)) := by
  rw [cycleRelation,meaning_cup,hY,meaning_cycleX env V E _ g hV hE hY hn]
  simpa only [relationCode,elements_ofFinset,←Finset.image_union] using
    congrArg relationCode (edge_config_union (b := b) g)

lemma cycleRelations_mem (env : Fin k → HF (Atom b)) (V E F R T H N : QuotedTerm k)
    (Ts : Finset (Edge n)) (Ns : Finset (Edge n)) (e : Edge n) (o : Vertex n) (g : BoxGroup n)
    (hV : V.meaning (atomInput b) env = ofFinset (Finset.univ.image (vertexCode b)))
    (hE : E.meaning (atomInput b) env = ofFinset (Finset.univ.image (edgeCode b)))
    (hT : T.meaning (atomInput b) env = ofFinset (Ts.image (edgeCode b)))
    (hH : H.meaning (atomInput b) env = connTableCode b Ts)
    (hN : N.meaning (atomInput b) env = ofFinset (Ns.image (edgeCode b)))
    (he : e ∈ Ns)
    (hY : ∀ (env' : Fin (k+4) → HF (Atom b)) (Γ : QuotedTerm (k+4)),
      F.up.up.up.up.meaning (atomInput b) env' = F.meaning (atomInput b) env →
      R.up.up.up.up.meaning (atomInput b) env' = R.meaning (atomInput b) env →
      E.up.up.up.up.meaning (atomInput b) env' = E.meaning (atomInput b) env →
      Γ.meaning (atomInput b) env' = traversalCode b Ts e (tail e) (head e) →
      (var 0 : QuotedTerm (k+4)).meaning (atomInput b) env' = vertexCode b o →
      (cycleY E.up.up.up.up F.up.up.up.up R.up.up.up.up Γ (var 0)).meaning (atomInput b) env' =
        relationCode (edgeActionRelation g)) (hn : 1 ≤ n) :
    relationCode (graph (actionPerm g)) ∈ elements ((cycleRelations V E F R T H N).meaning (atomInput b) env) := by
  simp only [cycleRelations,meaning_cup,elements_ofFinset,Finset.mem_union,meaning_bind,
    QuotedTerm.meaning_up,hN,hV,Finset.mem_biUnion,Finset.mem_image,Finset.mem_univ,true_and,
    meaning_map,QuotedTerm.meaning_filter,Finset.mem_filter]
  apply Or.inr
  refine ⟨edgeCode b e,⟨e,he,rfl⟩,vertexCode b (tail e),⟨tail e,rfl⟩,
    vertexCode b (head e),⟨head e,rfl⟩,vertexCode b o,⟨⟨o,rfl⟩,?_⟩,?_⟩
  · exact (meaning_hasEndpoints _ _ _ _ e (tail e) (head e) rfl rfl rfl hn).mpr (Or.inl ⟨rfl,rfl⟩)
  · have htr := meaning_traversal
      (Fin.cons (vertexCode b o) (Fin.cons (vertexCode b (head e))
        (Fin.cons (vertexCode b (tail e)) (Fin.cons (edgeCode b e) env))))
      V.up.up.up.up T.up.up.up.up H.up.up.up.up (var 3) (var 2) (var 1)
      Ts e (tail e) (head e) hV hT hH rfl rfl rfl hn
    exact meaning_cycleRelation_of_Y _ _ _ _ _ _ _ g hV hE (hY _ _ rfl rfl rfl htr rfl) hn

end QuotedGrid

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS WitnessedChoice.TreeTest Hereditary RelationPools

variable {n : ℕ} {b : Vertex n → Scalar}

namespace QuotedGrid

open QuotedTerm QuotedFormula SourceSyntax

variable {k : ℕ} {T₀ : RootedTree (Vertex n)}

attribute [local irreducible] SourceSyntax.cycleRelations SourceSyntax.cycleY

lemma cycleRelations_negative_oai (env : Fin k → HF (Atom b)) (V E F R T H N : QuotedTerm k)
    (P : ParentEdges T₀) (Ns : Finset (Edge n))
    (hV : V.meaning (atomInput b) env = ofFinset (Finset.univ.image (vertexCode b)))
    (hE : E.meaning (atomInput b) env = ofFinset (Finset.univ.image (edgeCode b)))
    (hF : ∀ z, z ∈ elements (F.meaning (atomInput b) env) ↔ ∃ C : CycleFrame n, frameCode b C = z)
    (hR : R.meaning (atomInput b) env = distancesCode b (boxGraph n))
    (hT : T.meaning (atomInput b) env = ofFinset (P.treeEdges.image (edgeCode b)))
    (hH : H.meaning (atomInput b) env = connTableCode b P.treeEdges)
    (hN : N.meaning (atomInput b) env = ofFinset (Ns.image (edgeCode b)))
    (e : Edge n) (he : e ∈ Ns) (hne : e ∉ P.treeEdges) (hn : 1 ≤ n) :
    relationCode (graph (actionPerm (b := b) (⟨0,P.flow e (-1)⟩ : BoxGroup n))) ∈
      elements ((cycleRelations V E F R T H N).meaning (atomInput b) env) := by
  refine cycleRelations_mem env V E F R T H N P.treeEdges Ns e oppositeVertex
    (⟨0,P.flow e (-1)⟩ : BoxGroup n) hV hE hT hH hN he ?_ hn
  intro env' Γ hF' hR' hE' hΓ ho
  have hfe : ∀ z, z ∈ elements (F.up.up.up.up.meaning (atomInput b) env') ↔
      ∃ C : CycleFrame n, frameCode b C = z := fun z => by rw [hF']; exact hF z
  exact meaning_reverseCycleY env' E.up.up.up.up F.up.up.up.up R.up.up.up.up Γ (var 0) P e hne (hE'.trans hE) hfe (hR'.trans hR) hΓ ho hn

end QuotedGrid

end





end WitnessedSeparation.Grid

end OAI
end

theorem solution : type_of% @OAI.WitnessedSeparation.Grid.QuotedGrid.cycleRelations_negative_oai := @OAI.WitnessedSeparation.Grid.QuotedGrid.cycleRelations_negative_oai
