-- Prove2me | solution 1 for OAI.WitnessedSeparation.Grid.QuotedGrid.selection_transitive
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T00:31:20.618635+00:00
-- url     : https://prove2.me/submissions/3b908096-aaaa-457c-b64b-c606abc8eca5

import Mathlib
import Definitions.Def_WitnessedChoice
import Definitions.Def_OAIQ4Wc000
import Theorems.Thm_OAI_WitnessedSeparation_Grid_QuotedGrid_fundamentalPool_in_cycles
import Theorems.Thm_OAI_WitnessedSeparation_Grid_QuotedGrid_selection_candidates

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_SupportGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WitnessedSeparation

namespace Support

variable {F K : Type} [Fintype F] [AddCommGroup K] [Module Scalar K]

namespace H

variable (cycle : F → K)

theorem ambient_card [FiniteDimensional Scalar K] :
    Nat.card (H cycle) = 3 ^ (Module.finrank Scalar (F → Plane) + Module.finrank Scalar K) := by
  rw [Nat.card_congr (productEquiv cycle), Nat.card_prod,
    Module.natCard_eq_pow_finrank (K := Scalar) (V := F → Plane),
    Module.natCard_eq_pow_finrank (K := Scalar) (V := K)]
  have h : Nat.card Scalar = 3 := by simp [Scalar, Nat.card_eq_fintype_card]
  rw [h, ← pow_add]

end H

end Support

end WitnessedSeparation

end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_GridAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WitnessedSeparation.Grid

variable {n : ℕ}

theorem head_injective_on_axis {e e' : Edge n}
    (ha : edgeAxis e = edgeAxis e') (hh : head e = head e') : e = e' := by
  rcases e with ⟨i,j,k⟩ | (⟨i,j,k⟩ | ⟨i,j,k⟩)
  all_goals rcases e' with ⟨i',j',k'⟩ | (⟨i',j',k'⟩ | ⟨i',j',k'⟩)
  all_goals simp_all [edgeAxis,head]

theorem tail_injective_on_axis {e e' : Edge n}
    (ha : edgeAxis e = edgeAxis e') (hh : tail e = tail e') : e = e' := by
  rcases e with ⟨i,j,k⟩ | (⟨i,j,k⟩ | ⟨i,j,k⟩)
  all_goals rcases e' with ⟨i',j',k'⟩ | (⟨i',j',k'⟩ | ⟨i',j',k'⟩)
  all_goals simp_all [edgeAxis,tail]

theorem degree_le_six (v : Vertex n) :
    Fintype.card {e : Edge n // head e = v ∨ tail e = v} ≤ 6 := by
  classical
  let f : {e : Edge n // head e = v ∨ tail e = v} → Fin 3 × Bool :=
    fun e => (edgeAxis e.val, decide (head e.val = v))
  have hf : Function.Injective f := by
    intro e e' heq
    have ha : edgeAxis e.val = edgeAxis e'.val := congrArg Prod.fst heq
    have hb : decide (head e.val = v) = decide (head e'.val = v) := congrArg Prod.snd heq
    apply Subtype.ext
    by_cases he : head e.val = v
    · have he' : head e'.val = v := by simpa only [he,decide_true,true_eq_decide_iff] using hb
      exact head_injective_on_axis ha (he.trans he'.symm)
    · have he' : head e'.val ≠ v := by simpa only [he,decide_false,false_eq_decide_iff] using hb
      exact tail_injective_on_axis ha
        ((e.property.resolve_left he).trans (e'.property.resolve_left he').symm)
  have h := Fintype.card_le_of_injective f hf
  simpa using h

end WitnessedSeparation.Grid

end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_Syntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

variable {A : Type} [Fintype A]

lemma Term.eval_letIn (S : Input A) (p : Polynomial ℝ) {n : ℕ}
    (v : Term n) (b : Term (n+1)) (env : Fin n → HF A) {x y : HF A}
    (hv : v.eval S p env = some x) (hb : b.eval S p (Fin.cons x env) = some y) :
    (v.letIn b).eval S p env = some y := by
  simp only [Term.letIn,eval,eval_singleton S p v env hv,Option.bind_some]
  have he : collect (Hereditary.singleton x) (fun z => Formula.truth.eval S p (Fin.cons z env))
      (fun z => b.eval S p (Fin.cons z env)) = some (Hereditary.singleton y) := by
    simp [collect,Formula.eval_truth,Hereditary.singleton,hb]
  rw [he,Option.map_some,uniqueHF_singleton]

end

end WitnessedChoice.BGS

end

end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_QuotedSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace WitnessedChoice.RelationPools

noncomputable section

open Classical

variable {A : Type} [Fintype A]

lemma identity_mem_localPool (B : ℕ) : graph (1 : Equiv.Perm A) ∈ localPool B := by
  exact Finset.mem_insert_self _ _

lemma localPool_contains {B : ℕ} (g : Equiv.Perm A)
    (hb : (Finset.univ.filter (fun a => g a ≠ a)).card ≤ B) : graph g ∈ localPool B := by
  let s : Finset A := Finset.univ.filter (fun a => g a ≠ a)
  by_cases hs : s.Nonempty
  · obtain ⟨a0, ha0⟩ := hs
    let e : s ≃ Fin s.card := Fintype.equivFinOfCardEq (by simp)
    let p : Fin B → A := fun i => if hi : i.val < s.card then (e.symm ⟨i.val,hi⟩).val else a0
    let q : Fin B → A := g ∘ p
    have cover : ∀ a ∈ s, ∃ i, p i = a := by
      intro a ha
      let j := e ⟨a,ha⟩
      let i : Fin B := ⟨j.val, lt_of_lt_of_le j.isLt hb⟩
      refine ⟨i,?_⟩
      dsimp [p]
      rw [dite_eq_left j.isLt]
      exact congrArg Subtype.val (e.symm_apply_apply ⟨a,ha⟩)
    have he : localRelation p q = graph g := by
      ext ab
      rcases ab with ⟨a,b⟩
      simp only [localRelation, Finset.mem_union, Finset.mem_image,
        Finset.mem_univ, true_and, Finset.mem_filter, Prod.mk.injEq, mem_graph]
      constructor
      · rintro (⟨i, hi, rfl⟩ | ⟨u, hu, rfl, rfl⟩)
        · rw [← hi]; rfl
        · by_contra hn
          obtain ⟨i,hi⟩ := cover u (by simpa [s] using hn)
          exact hu i hi.symm
      · intro hg
        by_cases ha : a ∈ s
        · obtain ⟨i,hi⟩ := cover a ha
          exact Or.inl ⟨i,hi,by dsimp [q,Function.comp_apply]; rw [hi,hg]⟩
        · right
          have hga : g a = a := by simpa [s] using ha
          refine ⟨a,?_,rfl,hga.symm.trans hg⟩
          intro i hai
          have hp : p i ∈ s := by
            dsimp [p]
            split
            · exact (e.symm _).property
            · exact ha0
          exact ha (hai ▸ hp)
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨(p,q),Finset.mem_univ _,he⟩
  · have hg : g = 1 := by
      apply Equiv.ext
      intro a
      by_contra hn
      exact hs ⟨a,by simpa [s] using hn⟩
    rw [hg]
    exact identity_mem_localPool B

end

end WitnessedChoice.RelationPools



namespace WitnessedChoice.BGS





noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary RelationPools

namespace QuotedTerm

variable {n : ℕ}

variable {A : Type} [Fintype A] (S : Input A) (env : Fin n → HF A)

lemma meaning_edgeRow (a : QuotedTerm n) (x : A) (ha : a.meaning S env = atom x) :
    (edgeRow a).meaning S env = stateCode (WitnessedChoice.edgeRow S x) := by
  simp only [edgeRow,meaning_filter,meaning_edgeAtoms,stateCode,elements_ofFinset,
    QuotedFormula.meaning_input,meaning_up,meaning_var,Fin.cons_zero,ha]
  apply ofFinset_inj.mpr
  ext z
  simp only [Finset.mem_filter,Finset.mem_image,WitnessedChoice.edgeRow]
  constructor
  · rintro ⟨⟨b,hb,rfl⟩,hr⟩
    exact ⟨b,⟨hb,by simpa only [inputHF_atoms] using hr⟩,rfl⟩
  · rintro ⟨b,⟨hb,hr⟩,rfl⟩
    exact ⟨⟨b,hb,rfl⟩,by simpa only [inputHF_atoms] using hr⟩

lemma meaning_vertexRow (a : QuotedTerm n) (x : A) (ha : a.meaning S env = atom x) :
    (vertexRow a).meaning S env = stateCode (WitnessedChoice.vertexRow S x) := by
  simp only [vertexRow,meaning_filter,meaning_configAtoms,stateCode,elements_ofFinset,
    QuotedFormula.meaning_input,meaning_up,meaning_var,Fin.cons_zero,ha]
  apply ofFinset_inj.mpr
  ext z
  simp only [Finset.mem_filter,Finset.mem_image,WitnessedChoice.vertexRow]
  constructor
  · rintro ⟨⟨b,hb,rfl⟩,hr⟩
    exact ⟨b,⟨hb,by simpa only [inputHF_atoms] using hr⟩,rfl⟩
  · rintro ⟨b,⟨hb,hr⟩,rfl⟩
    exact ⟨⟨b,hb,rfl⟩,by simpa only [inputHF_atoms] using hr⟩

@[simp] lemma meaning_edgeBlocks : (edgeBlocks : QuotedTerm n).meaning S env =
    ofFinset ((WitnessedChoice.edgeBlocks S).image stateCode) := by
  simp only [edgeBlocks,meaning_map,meaning_edgeAtoms,stateCode,elements_ofFinset,
    Finset.image_image,WitnessedChoice.edgeBlocks,Function.comp_def]
  congr 2
  funext x
  exact meaning_edgeRow S (Fin.cons (atom x) env) (.var 0) x rfl

@[simp] lemma meaning_vertexBlocks : (vertexBlocks : QuotedTerm n).meaning S env =
    ofFinset ((WitnessedChoice.vertexBlocks S).image stateCode) := by
  simp only [vertexBlocks,meaning_map,meaning_configAtoms,stateCode,elements_ofFinset,
    Finset.image_image,WitnessedChoice.vertexBlocks,Function.comp_def]
  congr 2
  funext x
  exact meaning_vertexRow S (Fin.cons (atom x) env) (.var 0) x rfl

@[simp] lemma meaning_blocks : (blocks : QuotedTerm n).meaning S env =
    ofFinset ((WitnessedChoice.blocks S).image stateCode) := by
  simp only [blocks,meaning_cup,meaning_edgeBlocks,meaning_vertexBlocks,elements_ofFinset,WitnessedChoice.blocks]
  apply ofFinset_inj.mpr
  ext z
  simp only [Finset.mem_union,Finset.mem_image]
  aesop

end QuotedTerm

end





end WitnessedChoice.BGS

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


namespace CPTTerm

variable {n m : ℕ} {A : Type} [Fintype A]

lemma eval_value (t : CPTTerm n) (S : Input A) (p : Polynomial ℝ) (env : Fin n → HF A) :
    t.code.eval S p env = some (t.value S p env) := (t.code.total S p t.count env).choose_spec

lemma value_eq (t : CPTTerm n) (S : Input A) (p : Polynomial ℝ) (env : Fin n → HF A) {x : HF A}
    (h : t.code.eval S p env = some x) : t.value S p env = x :=
  Option.some.inj ((t.eval_value S p env).symm.trans h)

@[simp] lemma value_quoted (t : QuotedTerm n) (S : Input A) (p : Polynomial ℝ) (env : Fin n → HF A) :
    (quoted t).value S p env = t.meaning S env := (quoted t).value_eq S p env (t.correct S p env)

@[simp] lemma value_rename (t : CPTTerm n) (f : Fin n → Fin m) (S : Input A)
    (p : Polynomial ℝ) (env : Fin m → HF A) :
    (t.rename f).value S p env = t.value S p (env ∘ f) := by
  apply value_eq
  exact (t.code.eval_rename S p t.count f env).trans (t.eval_value S p _)

@[simp] lemma value_up (t : CPTTerm n) (S : Input A) (p : Polynomial ℝ) (env : Fin n → HF A) (x) :
    t.up.value S p (Fin.cons x env) = t.value S p env := value_rename _ _ _ _ _

@[simp] lemma value_letIn (t : CPTTerm n) (b : CPTTerm (n+1)) (S : Input A)
    (p : Polynomial ℝ) (env : Fin n → HF A) :
    (t.letIn b).value S p env = b.value S p (Fin.cons (t.value S p env) env) := by
  apply value_eq
  exact Term.eval_letIn S p t.code b.code env (t.eval_value S p env) (b.eval_value S p _)

lemma eval_iterate (b : CPTTerm (n+1)) (S : Input A) (p : Polynomial ℝ) (env : Fin n → HF A) :
    b.iterate.code.eval S p env = ordinaryIteration (resource p (Fintype.card A))
      (fun x => some (b.value S p (Fin.cons x env))) := by
  simp only [iterate,Term.eval,b.eval_value]

end CPTTerm

namespace CPTFormula

variable {n m : ℕ} {A : Type} [Fintype A]

lemma eval_value (t : CPTFormula n) (S : Input A) (p : Polynomial ℝ) (env : Fin n → HF A) :
    t.code.eval S p env = some (t.value S p env) := (t.code.total S p t.count env).choose_spec

lemma value_eq (t : CPTFormula n) (S : Input A) (p : Polynomial ℝ) (env : Fin n → HF A) {x : Bool}
    (h : t.code.eval S p env = some x) : t.value S p env = x :=
  Option.some.inj ((t.eval_value S p env).symm.trans h)

@[simp] lemma value_quoted (t : QuotedFormula n) (S : Input A) (p : Polynomial ℝ) (env : Fin n → HF A) :
    (quoted t).value S p env = decide (t.meaning S env) := (quoted t).value_eq S p env (t.correct S p env)

end CPTFormula


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

variable {n : ℕ}

variable {A : Type} [Fintype A]

lemma mem_tupleProduct (k : ℕ) (r : QuotedTerm n) (S : Input A) (env : Fin n → HF A) (z : HF A) :
    z ∈ elements ((tupleProduct k r).meaning S env) ↔
      ∃ f : Fin k → HF A, (∀ i, f i ∈ elements (r.meaning S env)) ∧ tupleCode (List.ofFn f) = z := by
  induction k generalizing n z with
  | zero =>
    simp only [tupleProduct,meaning_singleton,meaning_empty,Hereditary.singleton,elements_ofFinset,
      Finset.mem_singleton,List.ofFn_zero,tupleCode]
    constructor
    · intro h; exact ⟨Fin.elim0,fun i => Fin.elim0 i,h.symm⟩
    · rintro ⟨f,hf,he⟩; exact he.symm
  | succ k ih =>
    simp only [tupleProduct,meaning_bind,meaning_map,meaning_pair,meaning_var,Fin.cons_zero,
      Fin.cons_one,elements_ofFinset,Finset.mem_biUnion,Finset.mem_image,ih,meaning_up]
    constructor
    · rintro ⟨a,ha,b,⟨f,hf,hb⟩,he⟩
      refine ⟨Fin.cons a f,?_,?_⟩
      · intro i; refine Fin.cases ha hf i
      · simp only [List.ofFn_succ,Fin.cons_zero,Fin.cons_succ,tupleCode]
        rw [hb,he]
    · rintro ⟨f,hf,he⟩
      refine ⟨f 0,hf 0,tupleCode (List.ofFn (fun i => f i.succ)),?_,?_⟩
      · exact ⟨fun i => f i.succ,fun i => hf i.succ,rfl⟩
      · simpa only [List.ofFn_succ,tupleCode] using he

end QuotedTerm


namespace CPTTerm

variable {n : ℕ} {A : Type} [Fintype A]

theorem value_comprehend (r : CPTTerm n) (body : CPTTerm (n+1)) (guard : CPTFormula (n+1))
    (S : Input A) (p : Polynomial ℝ) (env : Fin n → HF A) :
    (r.comprehend body guard).value S p env = ofFinset
      (((elements (r.value S p env)).filter fun x => guard.value S p (Fin.cons x env) = true).image
        fun x => body.value S p (Fin.cons x env)) := by
  apply value_eq
  exact Term.eval_comprehend S p r.code body.code guard.code env (r.eval_value S p env)
    (fun x => body.eval_value S p _) (fun x => guard.eval_value S p _)

@[simp] theorem value_map (r : CPTTerm n) (body : CPTTerm (n+1))
    (S : Input A) (p : Polynomial ℝ) (env : Fin n → HF A) :
    (r.map body).value S p env = ofFinset ((elements (r.value S p env)).image
      fun x => body.value S p (Fin.cons x env)) := by
  rw [map,value_comprehend]
  simp only [CPTFormula.value_quoted,QuotedFormula.truth,QuotedFormula.meaning_eq,
    decide_true,Finset.filter_true]

end CPTTerm


section

open RelationPools

variable {A : Type} [Fintype A]

namespace CPTTerm

variable {n : ℕ}

@[simp] lemma value_normalizeCandidates (t : CPTTerm n) (S : Input A) (p : Polynomial ℝ) (env : Fin n → HF A) :
    t.normalizeCandidates.value S p env = stateCode
      (decodeState (t.value S p env) ∩ WitnessedChoice.edgeAtoms S) := by
  simp [normalizeCandidates]

@[simp] lemma value_normalizeRelations (t : CPTTerm n) (S : Input A) (p : Polynomial ℝ) (env : Fin n → HF A) :
    t.normalizeRelations.value S p env = ofFinset
      (((elements (t.value S p env)).image decodeRelation).image relationCode) := by
  simp [normalizeRelations]

end CPTTerm

end


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

lemma TC_ofFinset_mono {s t : Finset (HF A)} (h : s ⊆ t) :
    TC (ofFinset s) ⊆ TC (ofFinset t) := by
  simp only [TC,elements_ofFinset]
  exact Finset.biUnion_subset_biUnion_of_subset_left _ h

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

variable {A : Type}

theorem iterationLoop_stationary (p : ℕ) (f : HF A → HF A)
    (step : HF A → Result (HF A)) (heval : ∀ x, step x = some (f x))
    (t fuel : ℕ) (hfu : t < fuel) (x : HF A)
    (hsize : ∀ k ≤ t, (TC ((f^[k]) x)).card ≤ p)
    (hstop : f ((f^[t]) x) = (f^[t]) x) :
    iterationLoop p step fuel x = some ((f^[t]) x) := by
  have hx : (TC x).card ≤ p := by simpa using hsize 0 (Nat.zero_le t)
  induction t generalizing fuel x with
  | zero =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [Function.iterate_zero, id_eq] at hstop ⊢
      rw [iterationLoop,ite_eq_left hx,heval,Option.bind_some,ite_eq_left hstop.symm]
  | succ t ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      rw [iterationLoop,ite_eq_left hx,heval,Option.bind_some]
      by_cases h : x = f x
      · rw [ite_eq_left h]
        congr 1
        exact ((show Function.IsFixedPt f x from h.symm).iterate (t+1)).symm
      · rw [ite_eq_right h]
        rw [Function.iterate_succ_apply]
        apply ih fuel (by omega) (f x)
        · intro k hk
          rw [← Function.iterate_succ_apply]
          exact hsize (k+1) (by omega)
        · simpa only [Function.iterate_succ_apply] using hstop
        · simpa using hsize 1 (by omega)

theorem ordinaryIteration_stationary (p : ℕ) (f : HF A → HF A)
    (step : HF A → Result (HF A)) (heval : ∀ x, step x = some (f x))
    (t : ℕ) (ht : t ≤ p)
    (hsize : ∀ k ≤ t, (TC ((f^[k]) emptyHF)).card ≤ p)
    (hstop : f ((f^[t]) emptyHF) = (f^[t]) emptyHF) :
    ordinaryIteration p step = some ((f^[t]) emptyHF) :=
  iterationLoop_stationary p f step heval t (p+1) (by omega) emptyHF hsize hstop

end



noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

variable {A X : Type} [Fintype X]

theorem ordinaryIteration_encoded (p : ℕ) (code : X → HF A)
    (f : Finset X → Finset X) (F : HF A → HF A) (step : HF A → Result (HF A))
    (hstep : ∀ x, step x = some (F x))
    (hcode : ∀ s, F (ofFinset (s.image code)) = ofFinset ((f s).image code))
    (hi : ∀ s, s ⊆ f s) (htime : Fintype.card X ≤ p)
    (hspace : (TC (ofFinset (Finset.univ.image code))).card ≤ p) :
    ordinaryIteration p step = some (ofFinset
      ((FiniteIteration.run f (Fintype.card X)).image code)) := by
  have he (k : ℕ) : (F^[k]) emptyHF = ofFinset ((FiniteIteration.run f k).image code) := by
    induction k with
    | zero => simp only [Function.iterate_zero,id_eq,FiniteIteration.run,Finset.image_empty,emptyHF]
    | succ k ih =>
      rw [Function.iterate_succ_apply',ih,hcode]
      rfl
  have hf : F ((F^[Fintype.card X]) emptyHF) = (F^[Fintype.card X]) emptyHF := by
    rw [he,hcode]
    have hh := FiniteIteration.run_fixed f (Finset.univ : Finset X) hi
      (fun _ _ => Finset.subset_univ _)
    simpa only [Finset.card_univ] using
      congrArg (fun s => ofFinset (s.image code)) hh
  have hs (k : ℕ) : (TC ((F^[k]) emptyHF)).card ≤ p := by
    rw [he]
    exact (Finset.card_le_card (TC_ofFinset_mono (Finset.image_subset_image
      (Finset.subset_univ _)))).trans hspace
  have h := ordinaryIteration_stationary p F step hstep (Fintype.card X) htime (fun k _ => hs k) hf
  rwa [he] at h

end





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

lemma distanceStep_encoded {n : ℕ} (S : Input A) (env : Fin n → HF A)
    (VT J R : QuotedTerm n) (code : V → HF A) (hc : Function.Injective code)
    (G : SimpleGraph V)
    (hV : VT.meaning S env = ofFinset (Finset.univ.image code))
    (hJ : ∀ u v, blockAdjacent S (J.meaning S env) (code u) (code v) ↔ G.Adj u v)
    (r : Finset (BFS.Item V (Fintype.card A)))
    (hR : R.meaning S env = ofFinset (r.image (distanceCode code))) :
    (distanceStep VT J R).meaning S env =
      ofFinset ((BFS.update G (Fintype.card A) r).image (distanceCode code)) := by
  simp only [distanceStep,meaning_cup,hR,elements_ofFinset]
  apply ofFinset_inj.mpr
  ext z
  simp only [Finset.mem_union,Finset.mem_image,mem_distanceBase,mem_distanceFresh,
    hV,hR,elements_ofFinset,Finset.mem_univ,true_and]
  constructor
  · rintro ((⟨x,hx,hz⟩ | ⟨_,⟨v,rfl⟩,hz⟩) | ⟨_,⟨v,rfl⟩,_,⟨w,rfl⟩,i,hi,hs,hm,hz⟩)
    · exact ⟨x,(BFS.mem_update _ _ _ _).mpr (Or.inl (Or.inl hx)),hz⟩
    · exact ⟨(v,v,0),(BFS.mem_update _ _ _ _).mpr (Or.inl (Or.inr ⟨rfl,rfl⟩)),hz⟩
    · obtain ⟨j,hj,rfl⟩ := (mem_ordinal i (Fintype.card A+1)).mp hi
      change ordinal (j+1) ∈ elements (ordinal (A := A) (Fintype.card A+1)) at hs
      have hs' := (ordinal_mem_elements (A := A) _ _).mp hs
      obtain ⟨_,⟨u,rfl⟩,hm,ha⟩ := hm
      obtain ⟨y,hy,he⟩ := hm
      rcases y with ⟨v',u',i'⟩
      obtain ⟨hev,heu,hei⟩ := HFTriple_injective.mp he
      have ev := hc hev
      have eu := hc heu
      have ei := ordinal_injective hei
      dsimp at ev eu ei
      subst v'
      subst u'
      have hadj : u=w ∨ G.Adj u w := by
        rcases ha with ha | ha
        · exact Or.inl (hc ha)
        · exact Or.inr ((hJ u w).mp (by
            simpa only [QuotedFormula.meaning_adjacent,meaning_up,meaning_var,
              Fin.cons_zero,Fin.cons_one,blockAdjacent,blockIncident] using ha))
      refine ⟨(v,w,⟨j+1,hs'⟩),(BFS.mem_update _ _ _ _).mpr
        (Or.inr ⟨u,i',hy,?_,hadj⟩),hz⟩
      dsimp
      omega
  · rintro ⟨x,hx,rfl⟩
    rcases x with ⟨v,w,i⟩
    rcases (BFS.mem_update _ _ _ _).mp hx with (hx | ⟨he,hi⟩) | ⟨u,j,hj,he,ha⟩
    · exact Or.inl (Or.inl ⟨(v,w,i),hx,rfl⟩)
    · dsimp at he hi
      subst w
      have hi' : i = 0 := Fin.ext hi
      subst i
      exact Or.inl (Or.inr ⟨code v,⟨v,rfl⟩,rfl⟩)
    · apply Or.inr
      refine ⟨code v,⟨v,rfl⟩,code w,⟨w,rfl⟩,ordinal j.val,
        (ordinal_mem_elements (A := A) _ _).mpr j.isLt,?_,?_,?_⟩
      · change ordinal (j.val+1) ∈ elements (ordinal (A := A) (Fintype.card A+1))
        apply (ordinal_mem_elements (A := A) _ _).mpr
        dsimp at he
        omega
      · refine ⟨code u,⟨u,rfl⟩,⟨(v,u,j),hj,rfl⟩,?_⟩
        rcases ha with rfl | ha
        · exact Or.inl rfl
        · apply Or.inr
          simpa only [QuotedFormula.meaning_adjacent,meaning_up,meaning_var,Fin.cons_zero,
            Fin.cons_one,blockAdjacent,blockIncident] using (hJ u w).mpr ha
      · change HFTriple (code v) (code w) (ordinal (j.val+1)) =
          HFTriple (code v) (code w) (ordinal i.val)
        congr 2
        exact he.symm

end





noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

namespace CPTTerm

variable {n : ℕ} {A V : Type} [Fintype A] [Fintype V]

theorem distance_value (VT J : CPTTerm n) (S : Input A) (p : Polynomial ℝ)
    (env : Fin n → HF A) (code : V → HF A) (hc : Function.Injective code)
    (G : SimpleGraph V)
    (hV : VT.value S p env = ofFinset (Finset.univ.image code))
    (hJ : ∀ u v, blockAdjacent S (J.value S p env) (code u) (code v) ↔ G.Adj u v)
    (htime : Fintype.card (BFS.Item V (Fintype.card A)) ≤ resource p (Fintype.card A))
    (hspace : (TC (ofFinset (Finset.univ.image (distanceCode code)))).card ≤
      resource p (Fintype.card A)) :
    (distance VT J).value S p env =
      ofFinset ((BFS.closure G (Fintype.card A)).image (distanceCode code)) := by
  simp only [distance,value_letIn,value_up]
  apply value_eq
  rw [eval_iterate]
  apply ordinaryIteration_encoded _ (distanceCode code) (BFS.update G (Fintype.card A)) _ _
    (fun _ => rfl) _ (BFS.update_inflationary G _) htime hspace
  intro r
  simp only [value_quoted]
  apply distanceStep_encoded S _ (.var 2) (.var 1) (.var 0) code hc G
  · exact hV
  · exact hJ
  · rfl

end CPTTerm

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

lemma faceSide_injective {f g : Face n} (hp : facePlane f = facePlane g)
    (i : Fin 4) (he : faceSide f i = faceSide g i) : f = g := by
  rcases f with ⟨x,y,z⟩ | (⟨x,y,z⟩ | ⟨x,y,z⟩) <;>
    rcases g with ⟨a,b,c⟩ | (⟨a,b,c⟩ | ⟨a,b,c⟩) <;>
    simp only [facePlane] at hp
  all_goals first | contradiction | skip
  all_goals fin_cases i <;> simpa [faceSide,ex,ey,ez] using he

lemma edgeFaces_card_le_four (e : Edge n) : Fintype.card (EdgeFaces e) ≤ 4 := by
  let chooseSide (f : EdgeFaces e) : Fin 4 := (support_cycle f.val e f.property).choose
  have hs (f : EdgeFaces e) : faceSide f.val (chooseSide f) = e :=
    (support_cycle f.val e f.property).choose_spec
  let key (f : EdgeFaces e) : {k : Fin 3 × Fin 4 // sideAxis k.1 k.2 = edgeAxis e} :=
    ⟨(facePlane f.val,chooseSide f), (faceSide_axis f.val (chooseSide f)).symm.trans (congrArg edgeAxis (hs f))⟩
  have hi : Function.Injective key := by
    intro f g h
    have h' := congrArg Subtype.val h
    have hp := congrArg Prod.fst h'
    have hc := congrArg Prod.snd h'
    apply Subtype.ext
    apply faceSide_injective hp (chooseSide f)
    change chooseSide f = chooseSide g at hc
    exact (hs f).trans (by rw [hc,hs g])
  have ht : Fintype.card {k : Fin 3 × Fin 4 // sideAxis k.1 k.2 = edgeAxis e} = 4 := by
    generalize edgeAxis e = a
    fin_cases a <;> decide
  simpa only [ht] using Fintype.card_le_of_injective key hi

lemma faceCorner_injective {f g : Face n} (hp : facePlane f = facePlane g)
    (i : Fin 4) (he : faceCorner f i = faceCorner g i) : f = g := by
  rcases f with ⟨x,y,z⟩ | (⟨x,y,z⟩ | ⟨x,y,z⟩) <;>
    rcases g with ⟨a,b,c⟩ | (⟨a,b,c⟩ | ⟨a,b,c⟩) <;>
    simp only [facePlane] at hp
  all_goals first | contradiction | skip
  all_goals fin_cases i <;> simpa [faceCorner] using he

lemma faceSide_endpoints (f : Face n) (i : Fin 4) (v : Vertex n)
    (hv : incident v (faceSide f i)) : ∃ j, faceCorner f j = v := by
  rcases f with ⟨x,y,z⟩ | (⟨x,y,z⟩ | ⟨x,y,z⟩) <;> fin_cases i
  all_goals
    rcases hv with h | h
    all_goals first
      | exact ⟨0,h⟩
      | exact ⟨1,h⟩
      | exact ⟨2,h⟩
      | exact ⟨3,h⟩

lemma vertexFaces_card_le_twelve (v : Vertex n) : Fintype.card (VertexFaces v) ≤ 12 := by
  have hc (f : VertexFaces v) : ∃ i, faceCorner f.val i = v := by
    obtain ⟨e,he⟩ := f.property
    obtain ⟨i,hi⟩ := support_cycle f.val e.val he
    exact faceSide_endpoints f.val i v (hi ▸ e.property)
  let key (f : VertexFaces v) : Fin 3 × Fin 4 := (facePlane f.val,(hc f).choose)
  have hi : Function.Injective key := by
    intro f g h
    have hp := congrArg Prod.fst h
    have hk := congrArg Prod.snd h
    apply Subtype.ext
    apply faceCorner_injective hp (hc f).choose
    change (hc f).choose = (hc g).choose at hk
    exact (hc f).choose_spec.trans (by rw [hk,(hc g).choose_spec])
  simpa using Fintype.card_le_of_injective key hi

lemma localGroup_card_le_upper (e : Edge n) : Fintype.card (LocalGroup e) ≤ 3^9 := by
  have hc : Fintype.card (LocalGroup e) = 3 ^ (2 * Fintype.card (EdgeFaces e) + 1) := by
    rw [← Nat.card_eq_fintype_card,Support.H.ambient_card]
    congr 1
    rw [Module.finrank_pi_fintype]
    simp [Support.Plane,Support.Scalar,Module.finrank_prod,Nat.mul_comm]
  rw [hc]
  exact Nat.pow_le_pow_right (by omega) (by have := edgeFaces_card_le_four e; omega)

lemma exists_incident (hn : 1 ≤ n) (v : Vertex n) : Nonempty (IncidentEdges v) := by
  rcases v with ⟨i,j,k⟩
  by_cases hi : i.val < n
  · refine ⟨⟨ex ⟨i.val,hi⟩ j k,Or.inr ?_⟩⟩
    simp only [ex,tail,Prod.mk.injEq,and_true]
    exact Fin.ext rfl
  · refine ⟨⟨ex ⟨n-1,by omega⟩ j k,Or.inl ?_⟩⟩
    simp only [ex,head,Prod.mk.injEq,and_true]
    apply Fin.ext
    simp only [Fin.val_succ]
    omega

lemma epsilon_ne_zero (v : Vertex n) (e : IncidentEdges v) : epsilon v e.val ≠ 0 := by
  by_cases hh : head e.val = v
  · have ht : tail e.val ≠ v := fun h => head_ne_tail e.val (hh.trans h.symm)
    simp [epsilon,hh,ht]
  · have ht := e.property.resolve_left hh
    simp [epsilon,hh,ht]

variable {b : Vertex n → Scalar} {v : Vertex n}

lemma Configuration.faceValue_eq (s : Configuration b v) (e : IncidentEdges v)
    (f : EdgeFaces e.val) :
    s.faceValue ⟨f.val,⟨e,f.property⟩⟩ = (s.state e).face f := by
  exact s.compatible _ e f.val _ f.property

lemma Configuration.code_injective (e0 : IncidentEdges v) :
    Function.Injective (Configuration.code (b := b) e0) := by
  intro s t h
  have hf (e : IncidentEdges v) : (s.state e).face = (t.state e).face := by
    funext f
    rw [←s.faceValue_eq e f,←t.faceValue_eq e f]
    exact congrFun (congrArg Prod.fst h) ⟨f.val,⟨e,f.property⟩⟩
  have hz (e : IncidentEdges v) (he : e ≠ e0) : (s.state e).flow = (t.state e).flow :=
    congrFun (congrArg Prod.snd h) ⟨e,he⟩
  have hz0 : (s.state e0).flow = (t.state e0).flow := by
    have hsum := s.charge.trans t.charge.symm
    change (∑ e : IncidentEdges v, epsilon v e.val * (s.state e).flow) =
      ∑ e : IncidentEdges v, epsilon v e.val * (t.state e).flow at hsum
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ e0),
      ← Finset.add_sum_erase _ (fun e : IncidentEdges v => epsilon v e.val * (t.state e).flow)
        (Finset.mem_univ e0)] at hsum
    have hr : (∑ e ∈ Finset.univ.erase e0, epsilon v e.val * (s.state e).flow) =
        ∑ e ∈ Finset.univ.erase e0, epsilon v e.val * (t.state e).flow := by
      apply Finset.sum_congr rfl
      intro e he
      rw [hz e (Finset.ne_of_mem_erase he)]
    rw [hr] at hsum
    exact mul_left_cancel₀ (epsilon_ne_zero v e0) (add_right_cancel hsum)
  apply Configuration.ext
  intro e
  apply Support.H.ext (hf e)
  by_cases he : e = e0
  · subst e
    exact hz0
  · exact hz e he

lemma configuration_card_le_upper (hn : 1 ≤ n) (b : Vertex n → Scalar) (v : Vertex n) :
    Fintype.card (Configuration b v) ≤ 3^29 := by
  classical
  let e0 := Classical.choice (exists_incident hn v)
  rw [← Nat.card_eq_fintype_card]
  have hcard := Nat.card_le_card_of_injective _ (Configuration.code_injective (b := b) e0)
  have he : Nat.card {e : IncidentEdges v // e ≠ e0} ≤ 5 := by
    rw [Nat.card_eq_fintype_card]
    have hc := Fintype.card_subtype_compl (fun e : IncidentEdges v => e = e0)
    have hdeg : Fintype.card (IncidentEdges v) ≤ 6 := degree_le_six v
    have hone : Fintype.card {e : IncidentEdges v // e = e0} = 1 := by simp
    rw [hone] at hc
    rw [hc]
    omega
  have hc : Nat.card ((VertexFaces v → Plane) ×
      ({e : IncidentEdges v // e ≠ e0} → Scalar)) =
      3 ^ (2 * Nat.card (VertexFaces v) + Nat.card {e : IncidentEdges v // e ≠ e0}) := by
    simp only [Nat.card_prod,Nat.card_fun,Plane,Support.Scalar,Scalar]
    have hz : Nat.card (ZMod 3) = 3 := by simp [Nat.card_eq_fintype_card]
    rw [hz]
    rw [←pow_two,←pow_mul,←pow_add]
  rw [hc] at hcard
  exact hcard.trans (Nat.pow_le_pow_right (by omega) (by
    have hh : Nat.card (VertexFaces v) ≤ 12 := by
      simpa only [Nat.card_eq_fintype_card] using vertexFaces_card_le_twelve v
    omega))

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

end





noncomputable section

open Classical Support WitnessedChoice

variable {n : ℕ} {b : Vertex n → Scalar}

lemma actionPerm_fullAut (g : BoxGroup n) : actionPerm (b := b) g ∈ fullAut (atomInput b) := by
  intro r x y
  exact congrArg (fun p => @decide p (Classical.propDecidable p))
    (propext (AtomRelation.map_iff g r x y))

lemma edgeFootprint_card (F : Finset (Face n)) : (edgeFootprint F).card ≤ 4*F.card := by
  calc
    _ ≤ ∑ f ∈ F, (Finset.univ.image (faceSide f)).card := Finset.card_biUnion_le
    _ ≤ ∑ _ ∈ F, 4 := Finset.sum_le_sum fun f _ => (Finset.card_image_le).trans (by simp)
    _ = _ := by simp [Nat.mul_comm]

lemma vertexFootprint_card (F : Finset (Face n)) : (vertexFootprint F).card ≤ 4*F.card := by
  calc
    _ ≤ ∑ f ∈ F, (Finset.univ.image (faceCorner f)).card := Finset.card_biUnion_le
    _ ≤ ∑ _ ∈ F, 4 := Finset.sum_le_sum fun f _ => (Finset.card_image_le).trans (by simp)
    _ = _ := by simp [Nat.mul_comm]

lemma mem_edgeFootprint {F : Finset (Face n)} {f : Face n} (hf : f ∈ F)
    {e : Edge n} (he : cycle f e ≠ 0) : e ∈ edgeFootprint F := by
  obtain ⟨i,hi⟩ := support_cycle f e he
  exact Finset.mem_biUnion.mpr ⟨f,hf,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩⟩

lemma mem_vertexFootprint {F : Finset (Face n)} {f : Face n} (hf : f ∈ F)
    {v : Vertex n} (e : IncidentEdges v) (he : cycle f e.val ≠ 0) : v ∈ vertexFootprint F := by
  obtain ⟨i,hi⟩ := support_cycle f e.val he
  obtain ⟨j,hj⟩ := faceSide_endpoints f i v (hi ▸ e.property)
  exact Finset.mem_biUnion.mpr ⟨f,hf,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,hj⟩⟩

lemma affectedAtoms_card_le (hn : 1 ≤ n) (E : Finset (Edge n)) (V : Finset (Vertex n)) :
    (affectedAtoms b E V).card ≤ E.card*3^9 + V.card*3^29 := by
  apply (Finset.card_union_le _ _).trans
  apply Nat.add_le_add
  · calc
      _ ≤ ∑ e ∈ E, (edgeBlockSet b e).card := Finset.card_biUnion_le
      _ ≤ ∑ _ ∈ E, 3^9 := Finset.sum_le_sum fun e _ =>
          Finset.card_image_le.trans (by simpa using localGroup_card_le_upper e)
      _ = _ := by simp
  · calc
      _ ≤ ∑ v ∈ V, (vertexBlockSet b v).card := Finset.card_biUnion_le
      _ ≤ ∑ _ ∈ V, 3^29 := Finset.sum_le_sum fun v _ =>
          Finset.card_image_le.trans (by simpa using configuration_card_le_upper hn b v)
      _ = _ := by simp

lemma faceTranslation_moved_subset (a : Face n → Plane) (F : Finset (Face n))
    (ha : ∀ f, a f ≠ 0 → f ∈ F) :
    (Finset.univ.filter fun x : Atom b => actionPerm (⟨a,0⟩ : BoxGroup n) x ≠ x) ⊆
      affectedAtoms b (edgeFootprint F) (vertexFootprint F) := by
  intro x hx
  have hmove := (Finset.mem_filter.mp hx).2
  rcases x with ⟨e,s⟩ | ⟨v,s⟩
  · have he : e ∈ edgeFootprint F := by
      by_contra hn
      have hr : restrictGroup e (⟨a,0⟩ : BoxGroup n) = 1 := by
        apply Support.H.ext
        · funext f
          by_contra h
          exact hn (mem_edgeFootprint (ha f.val h) f.property)
        · rfl
      apply hmove
      change (Sum.inl ⟨e,restrictGroup e (⟨a,0⟩ : BoxGroup n) * s⟩ : Atom b) = _
      simp only [hr,one_mul]
    exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
      ⟨e,he,Finset.mem_image.mpr ⟨s,Finset.mem_univ _,rfl⟩⟩)
  · have hv : v ∈ vertexFootprint F := by
      by_contra hn
      have hr (e : IncidentEdges v) : restrictGroup e.val (⟨a,0⟩ : BoxGroup n) = 1 := by
        apply Support.H.ext
        · funext f
          by_contra h
          exact hn (mem_vertexFootprint (ha f.val h) e f.property)
        · rfl
      apply hmove
      change (Sum.inr ⟨v,actConfiguration (⟨a,0⟩ : BoxGroup n) s⟩ : Atom b) = _
      congr 1
      congr 1
      apply Configuration.ext
      intro e
      change restrictGroup e.val (⟨a,0⟩ : BoxGroup n) * s.state e = s.state e
      rw [hr e,one_mul]
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨v,hv,Finset.mem_image.mpr ⟨s,Finset.mem_univ _,rfl⟩⟩)

lemma faceTranslation_in_localPool_bound (B : ℕ) (hB : 16*(3^9+3^29) ≤ B) (hn : 1 ≤ n) (a : Face n → Plane)
    (F : Finset (Face n)) (hF : F.card ≤ 4) (ha : ∀ f, a f ≠ 0 → f ∈ F) :
    RelationPools.graph (actionPerm (b := b) (⟨a,0⟩ : BoxGroup n)) ∈
      RelationPools.localPool B := by
  apply RelationPools.localPool_contains
  calc
    _ ≤ (affectedAtoms b (edgeFootprint F) (vertexFootprint F)).card :=
      Finset.card_le_card (faceTranslation_moved_subset a F ha)
    _ ≤ (edgeFootprint F).card*3^9 + (vertexFootprint F).card*3^29 := affectedAtoms_card_le hn _ _
    _ ≤ 16*3^9 + 16*3^29 := Nat.add_le_add
        (Nat.mul_le_mul_right _ ((edgeFootprint_card F).trans (by omega)))
        (Nat.mul_le_mul_right _ ((vertexFootprint_card F).trans (by omega)))
    _ = 16*(3^9+3^29) := by rw [Nat.mul_add]
    _ ≤ B := hB

lemma faceTranslation_in_localPool (hn : 1 ≤ n) (a : Face n → Plane)
    (F : Finset (Face n)) (hF : F.card ≤ 4) (ha : ∀ f, a f ≠ 0 → f ∈ F) :
    RelationPools.graph (actionPerm (b := b) (⟨a,0⟩ : BoxGroup n)) ∈
      RelationPools.localPool RelationPools.localBound :=
  faceTranslation_in_localPool_bound RelationPools.localBound (by rw [RelationPools.localBound]) hn a F hF ha

end





noncomputable section

open Classical Support WitnessedChoice

variable {n : ℕ} {b : Vertex n → Scalar}

lemma faceDelta_support (e : Edge n) (s t : LocalGroup e) :
    ∀ f, faceDelta e s t f ≠ 0 → f ∈ Finset.univ.filter (fun f => cycle f e ≠ 0) := by
  intro f hf
  simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using
    (show cycle f e ≠ 0 from fun h => hf (by simp [faceDelta,h]))

lemma faceDelta_zero_on_past {x : Finset (Σ e : Edge n, LocalGroup e)}
    {e : Edge n} {s t : LocalGroup e} (hs : AcceptsFaces x e s) (ht : AcceptsFaces x e t)
    {r : Σ e : Edge n, LocalGroup e} (hr : r ∈ x) (f : EdgeFaces r.1) :
    faceDelta e s t f.val = 0 := by
  by_cases he : cycle f.val e ≠ 0
  · rw [faceDelta,dite_eq_left he,ht r hr f.val he f.property,hs r hr f.val he f.property,sub_self]
  · simp only [faceDelta,dite_eq_right he]

lemma faceDelta_fix_past {x : Finset (Σ e : Edge n, LocalGroup e)}
    {e : Edge n} {s t : LocalGroup e} (hs : AcceptsFaces x e s) (ht : AcceptsFaces x e t)
    {r : Σ e : Edge n, LocalGroup e} (hr : r ∈ x) :
    actionPerm (b := b) (⟨faceDelta e s t,0⟩ : BoxGroup n) (.inl r) = .inl r := by
  have hg : restrictGroup r.1 (⟨faceDelta e s t,0⟩ : BoxGroup n) = 1 := by
    apply Support.H.ext
    · funext f
      exact faceDelta_zero_on_past hs ht hr f
    · rfl
  change (Sum.inl ⟨r.1,restrictGroup r.1 (⟨faceDelta e s t,0⟩ : BoxGroup n) * r.2⟩ : Atom b) = _
  rw [hg,one_mul]

lemma faceDelta_hits_vectors (e : Edge n) (s t : LocalGroup e) :
    (restrictGroup e (⟨faceDelta e s t,0⟩ : BoxGroup n) * s).face = t.face := by
  funext f
  change faceDelta e s t f.val + s.face f = t.face f
  rw [faceDelta,dite_eq_left f.property,sub_add_cancel]

lemma faceDelta_in_localPool (hn : 1 ≤ n) (e : Edge n) (s t : LocalGroup e) :
    RelationPools.graph (actionPerm (b := b) (⟨faceDelta e s t,0⟩ : BoxGroup n)) ∈
      RelationPools.localPool RelationPools.localBound := by
  have hF : (Finset.univ.filter (fun f => cycle f e ≠ 0)).card ≤ 4 := by
    simpa only [← Fintype.card_subtype] using edgeFaces_card_le_four e
  exact faceTranslation_in_localPool hn _ _ hF (faceDelta_support e s t)

lemma central_after_local (e : Edge n) (s t : LocalGroup e) (k : FlowSpace n)
    (hk : k.val e = t.flow - (restrictGroup e (⟨faceDelta e s t,0⟩ : BoxGroup n) * s).flow) :
    actionPerm (b := b) (⟨0,k⟩ : BoxGroup n)
      (actionPerm (⟨faceDelta e s t,0⟩ : BoxGroup n) (.inl ⟨e,s⟩)) = .inl ⟨e,t⟩ := by
  change (Sum.inl ⟨e, restrictGroup e (⟨0,k⟩ : BoxGroup n) *
    (restrictGroup e (⟨faceDelta e s t,0⟩ : BoxGroup n) * s)⟩ : Atom b) = _
  congr 1
  congr 1
  apply Support.H.ext
  · funext f
    change 0 + (faceDelta e s t f.val + s.face f) = t.face f
    rw [zero_add]
    exact congrFun (faceDelta_hits_vectors e s t) f
  · change k.val e + (restrictGroup e (⟨faceDelta e s t,0⟩ : BoxGroup n) * s).flow +
        correction (localCycle e) 0 (restrictGroup e (⟨faceDelta e s t,0⟩ : BoxGroup n) * s).face = t.flow
    rw [correction_zero_left,add_zero,hk,sub_add_cancel]

lemma central_fix_edge (k : FlowSpace n) (e : Edge n) (s : LocalGroup e) (hk : k.val e = 0) :
    actionPerm (b := b) (⟨0,k⟩ : BoxGroup n) (.inl ⟨e,s⟩) = .inl ⟨e,s⟩ := by
  have hh : restrictGroup e (⟨0,k⟩ : BoxGroup n) = 1 := by
    apply Support.H.ext
    · rfl
    · exact hk
  change (Sum.inl ⟨e,restrictGroup e (⟨0,k⟩ : BoxGroup n) * s⟩ : Atom b) = _
  rw [hh,one_mul]

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


namespace WitnessedChoice

noncomputable section

open Classical

namespace AnchoredTree

variable {V : Type} [Fintype V]

omit [Fintype V] in
lemma root_lt (G : SimpleGraph V) (hG : G.Connected) (α : Fin 4 → V)
    (v : V) (hv : v ≠ α 0) : key G α (α 0) < key G α v := by
  refine ⟨0,?_,?_⟩
  · intro j hj; exact (Fin.not_lt_zero j hj).elim
  · change G.dist (α 0) (α 0) < G.dist (α 0) v
    rw [G.dist_self]
    exact Nat.pos_of_ne_zero (fun h => hv ((hG (α 0) v).dist_eq_zero_iff.mp h).symm)

omit [Fintype V] in
lemma least_iff_root (G : SimpleGraph V) (hG : G.Connected) (α : Fin 4 → V) (v : V) :
    (∀ w, ¬key G α w < key G α v) ↔ v = α 0 := by
  constructor
  · intro h; by_contra hn; exact h _ (root_lt G hG α v hn)
  · rintro rfl w hw
    by_cases h : w = α 0
    · subst w; exact lt_irrefl _ hw
    · exact (lt_asymm hw (root_lt G hG α w h))

lemma parent_iff (G : SimpleGraph V) (hG : G.Connected) (α : Fin 4 → V)
    (hα : Resolving G α) (v w : V) :
    (Eligible G (α 0) v w ∧ ∀ z, Eligible G (α 0) v z → ¬key G α z < key G α w) ↔
      v ≠ α 0 ∧ (rooted G hG α).parent v = w := by
  constructor
  · rintro ⟨hw,hm⟩
    have hv : v ≠ α 0 := by intro hh; have hd := hw.2; rw [hh,G.dist_self] at hd; omega
    refine ⟨hv,?_⟩
    have hp := parent_property G hG α v hv
    apply hα
    exact le_antisymm (le_of_not_gt (hp.2 w hw)) (le_of_not_gt (hm _ hp.1))
  · rintro ⟨hv,rfl⟩
    exact parent_property G hG α v hv

end AnchoredTree

end

end WitnessedChoice



namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary QuotedTerm

namespace QuotedFormula

variable {A V : Type} [Fintype A] [Fintype V] {k : ℕ}

lemma meaning_vertexLt (S : Input A) (env : Fin k → HF A)
    (ats R ut vt : QuotedTerm k) (code : V → HF A) (hc : Function.Injective code)
    (G : SimpleGraph V) (hG : G.Connected) (α : Fin 4 → V) (u v : V)
    (hα : ats.meaning S env = tupleCode (List.ofFn (code ∘ α)))
    (hR : R.meaning S env = ofFinset ((BFS.closure G (Fintype.card A)).image (distanceCode code)))
    (hu : ut.meaning S env = code u) (hv : vt.meaning S env = code v)
    (hcard : Fintype.card V ≤ Fintype.card A) :
    (vertexLt ats R ut vt).meaning S env ↔ AnchoredTree.key G α u < AnchoredTree.key G α v := by
  have hdU (i : Fin 4) : (distanceAt R (ats.component i.val) ut).meaning S env = ordinal (G.dist (α i) u) :=
    meaning_distanceAt S env R _ _ code hc G hG _ _ hR
      (meaning_component_ofFn S env ats (code ∘ α) hα i) hu hcard
  have hdV (i : Fin 4) : (distanceAt R (ats.component i.val) vt).meaning S env = ordinal (G.dist (α i) v) :=
    meaning_distanceAt S env R _ _ code hc G hG _ _ hR
      (meaning_component_ofFn S env ats (code ∘ α) hα i) hv hcard
  simp only [vertexLt,meaning_anyFin,meaning_and,meaning_allFin,meaning_mem,hdU,hdV,
    ordinal_mem_elements]
  change (∃ i : Fin 4, (∀ j : Fin 4, _) ∧ _) ↔ _
  have hm (i j : Fin 4) :
      (if j.val < i.val then eq (distanceAt R (ats.component j.val) ut)
        (distanceAt R (ats.component j.val) vt) else truth).meaning S env ↔
      (j < i → G.dist (α j) u = G.dist (α j) v) := by
    split_ifs with h
    · simp only [meaning_eq,hdU,hdV,ordinal_injective.eq_iff]
      simp only [Fin.lt_def,h,true_implies]
    · simp [truth, Fin.lt_def, h]
  simp only [hm]
  rfl

end QuotedFormula

end

end WitnessedChoice.BGS



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

lemma edgeRow_grid (e : Edge n) (s : LocalGroup e) :
    WitnessedChoice.edgeRow (atomInput b) (.inl ⟨e,s⟩) = edgeBlockSet b e := by
  ext a
  simp only [WitnessedChoice.edgeRow,WitnessedChoice.edgeAtoms,Finset.mem_filter,
    Finset.mem_univ,true_and,atomInput,decide_eq_true_eq,mem_edgeBlockSet]
  constructor
  · rintro ⟨_,h⟩
    cases h with | eb e s t => exact ⟨t,rfl⟩
  · rintro ⟨t,rfl⟩
    exact ⟨.ed e t,.eb e s t⟩

lemma vertexRow_grid (v : Vertex n) (s : Configuration b v) :
    WitnessedChoice.vertexRow (atomInput b) (.inr ⟨v,s⟩) = vertexBlockSet b v := by
  ext a
  simp only [WitnessedChoice.vertexRow,WitnessedChoice.configAtoms,Finset.mem_filter,
    Finset.mem_univ,true_and,atomInput,decide_eq_true_eq,mem_vertexBlockSet]
  constructor
  · rintro ⟨_,h⟩
    cases h with | vb v s t => exact ⟨t,rfl⟩
  · rintro ⟨t,rfl⟩
    exact ⟨.cf v t,.vb v s t⟩

lemma edgeBlocks_grid : WitnessedChoice.edgeBlocks (atomInput b) =
    Finset.univ.image (edgeBlockSet b) := by
  ext d
  simp only [WitnessedChoice.edgeBlocks,Finset.mem_image,WitnessedChoice.edgeAtoms,
    Finset.mem_filter,Finset.mem_univ,true_and,atomInput,decide_eq_true_eq]
  constructor
  · rintro ⟨a,h,rfl⟩
    cases h with | ed e s => exact ⟨e,(edgeRow_grid e s).symm⟩
  · rintro ⟨e,rfl⟩
    exact ⟨.inl ⟨e,1⟩,.ed e 1,edgeRow_grid e 1⟩

lemma vertexBlocks_grid (hn : 1 ≤ n) : WitnessedChoice.vertexBlocks (atomInput b) =
    Finset.univ.image (vertexBlockSet b) := by
  ext d
  simp only [WitnessedChoice.vertexBlocks,Finset.mem_image,WitnessedChoice.configAtoms,
    Finset.mem_filter,Finset.mem_univ,true_and,atomInput,decide_eq_true_eq]
  constructor
  · rintro ⟨a,h,rfl⟩
    cases h with | cf v s => exact ⟨v,(vertexRow_grid v s).symm⟩
  · rintro ⟨v,rfl⟩
    obtain ⟨s⟩ := configuration_exists (b := b) hn v
    exact ⟨.inr ⟨v,s⟩,.cf v s,vertexRow_grid v s⟩

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

lemma edgeGraph_univ : edgeGraph (Finset.univ : Finset (Edge n)) = boxGraph n := by
  ext u v
  simp only [edgeGraph,Finset.mem_univ,true_and,boxGraph_adj_iff]

lemma blockAdjacent_edges (hn : 1 ≤ n) (T : Finset (Edge n)) (u v : Vertex n) :
    blockAdjacent (atomInput b) (ofFinset (T.image (edgeCode b))) (vertexCode b u) (vertexCode b v) ↔
      (edgeGraph T).Adj u v := by
  simp only [blockAdjacent,(vertexCode_injective hn).ne_iff,elements_ofFinset,
    Finset.mem_image,exists_exists_and_eq_and,blockIncident_grid hn,edgeGraph]
  constructor
  · rintro ⟨hne,e,he,hu,hv⟩
    refine ⟨e,he,?_⟩
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · exact (hne (hu.symm.trans hv)).elim
    · exact Or.inr ⟨hv.symm,hu.symm⟩
    · exact Or.inl ⟨hu.symm,hv.symm⟩
    · exact (hne (hu.symm.trans hv)).elim
  · rintro ⟨e,he,(⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)⟩
    · exact ⟨(head_ne_tail e).symm,e,he,Or.inr rfl,Or.inl rfl⟩
    · exact ⟨head_ne_tail e,e,he,Or.inl rfl,Or.inr rfl⟩

lemma vertex_card_le_atoms (hn : 1 ≤ n) : Fintype.card (Vertex n) ≤ Fintype.card (Atom b) := by
  let f (v : Vertex n) : Atom b := .inr ⟨v,(configuration_exists (b := b) hn v).some⟩
  apply Fintype.card_le_of_injective f
  intro v w h
  exact congrArg Sigma.fst (Sum.inr.inj h)

lemma quoted_vertexBlocks {k : ℕ} (hn : 1 ≤ n) (env : Fin k → HF (Atom b)) :
    (QuotedTerm.vertexBlocks : QuotedTerm k).meaning (atomInput b) env =
      ofFinset (Finset.univ.image (vertexCode b)) := by
  rw [QuotedTerm.meaning_vertexBlocks,vertexBlocks_grid hn,Finset.image_image]
  rfl

lemma quoted_edgeBlocks {k : ℕ} (env : Fin k → HF (Atom b)) :
    (QuotedTerm.edgeBlocks : QuotedTerm k).meaning (atomInput b) env =
      ofFinset (Finset.univ.image (edgeCode b)) := by
  rw [QuotedTerm.meaning_edgeBlocks,edgeBlocks_grid,Finset.image_image]
  rfl

end





end WitnessedSeparation.Grid


section

namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary QuotedTerm

namespace QuotedFormula

variable {A V : Type} [Fintype A] [Fintype V] {k : ℕ}

lemma meaning_leastVertex (S : Input A) (env : Fin k → HF A)
    (ats VT R vt : QuotedTerm k) (code : V → HF A) (hc : Function.Injective code)
    (G : SimpleGraph V) (hG : G.Connected) (α : Fin 4 → V) (v : V)
    (hα : ats.meaning S env = tupleCode (List.ofFn (code ∘ α)))
    (hV : VT.meaning S env = ofFinset (Finset.univ.image code))
    (hR : R.meaning S env = ofFinset ((BFS.closure G (Fintype.card A)).image (distanceCode code)))
    (hv : vt.meaning S env = code v) (hcard : Fintype.card V ≤ Fintype.card A) :
    (leastVertex ats VT R vt).meaning S env ↔ v = α 0 := by
  simp only [leastVertex,meaning_and,meaning_mem,hv,hV,elements_ofFinset,
    Finset.mem_image,Finset.mem_univ,true_and,hc.eq_iff,exists_eq,true_and,
    meaning_allIn,forall_exists_index,forall_apply_eq_imp_iff,meaning_neg]
  have hm (w : V) : (vertexLt ats.up R.up (var 0) vt.up).meaning S (Fin.cons (code w) env) ↔
      AnchoredTree.key G α w < AnchoredTree.key G α v := by
    apply meaning_vertexLt S _ _ _ _ _ code hc G hG α w v
    all_goals first | assumption | rfl
  simpa only [hm] using AnchoredTree.least_iff_root G hG α v

end QuotedFormula

namespace QuotedTerm

variable {A V : Type} [Fintype A] [Fintype V] {k : ℕ}

lemma meaning_root (S : Input A) (env : Fin k → HF A)
    (ats VT R : QuotedTerm k) (code : V → HF A) (hc : Function.Injective code)
    (G : SimpleGraph V) (hG : G.Connected) (α : Fin 4 → V)
    (hα : ats.meaning S env = tupleCode (List.ofFn (code ∘ α)))
    (hV : VT.meaning S env = ofFinset (Finset.univ.image code))
    (hR : R.meaning S env = ofFinset ((BFS.closure G (Fintype.card A)).image (distanceCode code)))
    (hcard : Fintype.card V ≤ Fintype.card A) :
    (root ats VT R).meaning S env = code (α 0) := by
  have hm (v : V) : (QuotedFormula.leastVertex ats.up VT.up R.up (var 0)).meaning S
      (Fin.cons (code v) env) ↔ v = α 0 := by
    apply QuotedFormula.meaning_leastVertex S _ _ _ _ _ code hc G hG α v
    all_goals first | assumption | rfl
  simp only [root,meaning_unique,meaning_filter,hV,elements_ofFinset]
  have hf : (Finset.univ.image code).filter (fun z =>
      (QuotedFormula.leastVertex ats.up VT.up R.up (var 0)).meaning S (Fin.cons z env)) =
      {code (α 0)} := by
    ext z
    simp only [Finset.mem_filter,Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_singleton]
    constructor
    · rintro ⟨⟨v,rfl⟩,hv⟩
      rw [hm] at hv
      rw [hv]
    · rintro rfl
      exact ⟨⟨α 0,rfl⟩,(hm _).mpr rfl⟩
  rw [hf]
  exact uniqueHF_singleton _

end QuotedTerm

end

end WitnessedChoice.BGS

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

lemma meaning_adjacent (env : Fin k → HF (Atom b)) (Et ut vt : QuotedTerm k)
    (D : Finset (Edge n)) (u v : Vertex n)
    (hE : Et.meaning (atomInput b) env = ofFinset (D.image (edgeCode b)))
    (hu : ut.meaning (atomInput b) env = vertexCode b u)
    (hv : vt.meaning (atomInput b) env = vertexCode b v) (hn : 1 ≤ n) :
    (adjacent Et ut vt).meaning (atomInput b) env ↔ (edgeGraph D).Adj u v := by
  rw [QuotedFormula.meaning_adjacent,hE,hu,hv]
  exact blockAdjacent_edges hn D u v

lemma meaning_parentEligible (env : Fin k → HF (Atom b)) (Et R rt vt wt : QuotedTerm k)
    (r v w : Vertex n)
    (hE : Et.meaning (atomInput b) env = ofFinset (Finset.univ.image (edgeCode b)))
    (hR : R.meaning (atomInput b) env = ofFinset
      ((BFS.closure (boxGraph n) (Fintype.card (Atom b))).image (distanceCode (vertexCode b))))
    (hr : rt.meaning (atomInput b) env = vertexCode b r)
    (hv : vt.meaning (atomInput b) env = vertexCode b v)
    (hw : wt.meaning (atomInput b) env = vertexCode b w) (hn : 1 ≤ n) :
    (parentEligible Et R rt vt wt).meaning (atomInput b) env ↔ AnchoredTree.Eligible (boxGraph n) r v w := by
  have hd (u : Vertex n) (ut : QuotedTerm k) (hu : ut.meaning (atomInput b) env = vertexCode b u) :=
    QuotedTerm.meaning_distanceAt (atomInput b) env R rt ut (vertexCode b) (vertexCode_injective hn)
      (boxGraph n) (boxGraph_connected n) r u hR hr hu (vertex_card_le_atoms hn)
  rw [parentEligible,meaning_and,meaning_adjacent env Et vt wt _ v w hE hv hw hn,edgeGraph_univ]
  simp only [meaning_eq,meaning_successor,hd w wt hw,hd v vt hv]
  change ((boxGraph n).Adj v w ∧ ordinal ((boxGraph n).dist r w + 1) = ordinal ((boxGraph n).dist r v)) ↔ _
  rw [ordinal_injective.eq_iff]
  rfl

lemma meaning_parent (env : Fin k → HF (Atom b)) (ats VT Et R rt vt wt : QuotedTerm k)
    (α : Fin 4 → Vertex n) (v w : Vertex n) (hres : AnchoredTree.Resolving (boxGraph n) α)
    (hα : ats.meaning (atomInput b) env = tupleCode (List.ofFn (vertexCode b ∘ α)))
    (hV : VT.meaning (atomInput b) env = ofFinset (Finset.univ.image (vertexCode b)))
    (hE : Et.meaning (atomInput b) env = ofFinset (Finset.univ.image (edgeCode b)))
    (hR : R.meaning (atomInput b) env = ofFinset
      ((BFS.closure (boxGraph n) (Fintype.card (Atom b))).image (distanceCode (vertexCode b))))
    (hr : rt.meaning (atomInput b) env = vertexCode b (α 0))
    (hv : vt.meaning (atomInput b) env = vertexCode b v)
    (hw : wt.meaning (atomInput b) env = vertexCode b w) (hn : 1 ≤ n) :
    (QuotedFormula.parent ats VT Et R rt vt wt).meaning (atomInput b) env ↔
      v ≠ α 0 ∧ (anchoredTree α).parent v = w := by
  have hel (z : Vertex n) : (parentEligible Et.up R.up rt.up vt.up (var 0)).meaning
      (atomInput b) (Fin.cons (vertexCode b z) env) ↔ AnchoredTree.Eligible (boxGraph n) (α 0) v z := by
    apply meaning_parentEligible _ _ _ _ _ _ _ _ _ _ _ _ _ _ hn
    all_goals first | assumption | exact vertex_card_le_atoms hn | rfl
  have hlt (z : Vertex n) : (vertexLt ats.up R.up (var 0) wt.up).meaning
      (atomInput b) (Fin.cons (vertexCode b z) env) ↔
      AnchoredTree.key (boxGraph n) α z < AnchoredTree.key (boxGraph n) α w := by
    apply QuotedFormula.meaning_vertexLt _ _ _ _ _ _ (vertexCode b) (vertexCode_injective hn)
      (boxGraph n) (boxGraph_connected n) α z w
    all_goals first | assumption | exact vertex_card_le_atoms hn | rfl
  simp only [QuotedFormula.parent,meaning_and,meaning_parentEligible env Et R rt vt wt _ _ _ hE hR hr hv hw hn,
    meaning_allIn,hV,elements_ofFinset,Finset.mem_image,Finset.mem_univ,true_and,
    forall_exists_index,forall_apply_eq_imp_iff,meaning_imp,meaning_neg,hel,hlt]
  exact AnchoredTree.parent_iff (boxGraph n) (boxGraph_connected n) α hres v w

end QuotedGrid

end

end WitnessedSeparation.Grid

end


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

namespace WitnessedChoice.BGS.QuotedTerm

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

variable {A B : Type} [Fintype A] [Fintype B] {k : ℕ}

lemma mem_tupleProduct_image (m : ℕ) (r : QuotedTerm k) (S : Input A) (env : Fin k → HF A)
    (code : B → HF A) (hr : r.meaning S env = ofFinset (Finset.univ.image code)) (z : HF A) :
    z ∈ elements ((tupleProduct m r).meaning S env) ↔
      ∃ f : Fin m → B, tupleCode (List.ofFn (code ∘ f)) = z := by
  rw [mem_tupleProduct]
  simp only [hr,elements_ofFinset,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨g,hg,hz⟩
    choose f hf using hg
    exact ⟨f,by simpa only [show code ∘ f = g from funext hf] using hz⟩
  · rintro ⟨f,hf⟩
    exact ⟨code ∘ f,fun i => ⟨f i,rfl⟩,hf⟩

end

end WitnessedChoice.BGS.QuotedTerm

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

lemma meaning_faceDescription (env : Fin k → HF (Atom b)) (ft : QuotedTerm k)
    (v : Fin 4 → Vertex n) (e : Fin 4 → Edge n)
    (hf : ft.meaning (atomInput b) env = Hereditary.pair (tupleCode (List.ofFn (vertexCode b ∘ v)))
      (tupleCode (List.ofFn (edgeCode b ∘ e)))) (hn : 1 ≤ n) :
    (faceDescription ft).meaning (atomInput b) env ↔
      Function.Injective v ∧ Function.Injective e ∧
      ∀ i, (v i = tail (e i) ∧ v (i+1) = head (e i)) ∨
        (v (i+1) = tail (e i) ∧ v i = head (e i)) := by
  have hv := meaning_fv_pair env ft v e hf
  have he := meaning_fe_pair env ft v e hf
  have ha (i : Fin 4) : (hasEndpoints (fe ft i) (fv ft i) (fv ft (next4 i))).meaning (atomInput b) env ↔
      ((v i = tail (e i) ∧ v (i+1) = head (e i)) ∨
        (v (i+1) = tail (e i) ∧ v i = head (e i))) := by
    simp only [next4_eq_add,hasEndpoints,meaning_and,meaning_neg,meaning_eq,hv,(vertexCode_injective hn).eq_iff,
      meaning_incident env _ _ _ _ (hv i) (he i) hn,
      meaning_incident env _ _ _ _ (hv (i+1)) (he i) hn]
    exact (endpoints_incident_iff (e i) (v i) (v (i+1))).symm
  have hne (i j : Fin 4) : (if i=j then truth else
      (eq (fv ft i) (fv ft j)).neg.and (eq (fe ft i) (fe ft j)).neg).meaning (atomInput b) env ↔
      (i ≠ j → v i ≠ v j ∧ e i ≠ e j) := by
    split_ifs with hij
    · simp [truth,hij]
    · simp only [meaning_and,meaning_neg,meaning_eq,hv,he,(vertexCode_injective hn).eq_iff,
        edgeCode_injective.eq_iff,Ne,hij,not_false_eq_true,true_implies]
  simp only [faceDescription,meaning_allFin,meaning_and,hne,ha]
  constructor
  · intro hh
    refine ⟨?_,?_,fun i => (hh i).2⟩
    · intro i j hij
      by_contra hn
      exact ((hh i).1 j hn).1 hij
    · intro i j hij
      by_contra hn
      exact ((hh i).1 j hn).2 hij
  · rintro ⟨hv,he,hh⟩ i
    exact ⟨fun j hij => ⟨fun h => hij (hv h),fun h => hij (he h)⟩,hh i⟩

lemma mem_faces (env : Fin k → HF (Atom b)) (VT Et : QuotedTerm k)
    (hV : VT.meaning (atomInput b) env = ofFinset (Finset.univ.image (vertexCode b)))
    (hE : Et.meaning (atomInput b) env = ofFinset (Finset.univ.image (edgeCode b)))
    (hn : 1 ≤ n) (z : HF (Atom b)) :
    z ∈ elements ((faces VT Et).meaning (atomInput b) env) ↔
      ∃ C : CycleFrame n, frameCode b C = z := by
  have hTV (t : HF (Atom b)) := mem_tupleProduct_image 4 VT (atomInput b) env (vertexCode b) hV t
  have hTE (t u : HF (Atom b)) := mem_tupleProduct_image 4 Et.up (atomInput b) (Fin.cons t env)
    (edgeCode b) (by exact hE) u
  simp only [faces,QuotedTerm.meaning_filter,meaning_bind,meaning_map,meaning_pair,meaning_var,
    Fin.cons_zero,Fin.cons_one,elements_ofFinset,Finset.mem_filter,Finset.mem_biUnion,
    Finset.mem_image,hTV,hTE,exists_exists_eq_and]
  constructor
  · rintro ⟨⟨v,e,rfl⟩,hd⟩
    have hh := (meaning_faceDescription (Fin.cons _ env) (var 0) v e rfl hn).mp hd
    exact ⟨⟨v,e,hh.1,hh.2.1,hh.2.2⟩,rfl⟩
  · rintro ⟨C,rfl⟩
    refine ⟨⟨C.vertex,C.edge,rfl⟩,?_⟩
    exact (meaning_faceDescription (Fin.cons _ env) (var 0) C.vertex C.edge rfl hn).mpr
      ⟨C.vertex_injective,C.edge_injective,C.endpoints⟩

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

lemma meaning_tree (env : Fin k → HF (Atom b)) (ats VT Et R : QuotedTerm k)
    (α : Fin 4 → Vertex n) (hres : AnchoredTree.Resolving (boxGraph n) α)
    (hα : ats.meaning (atomInput b) env = tupleCode (List.ofFn (vertexCode b ∘ α)))
    (hV : VT.meaning (atomInput b) env = ofFinset (Finset.univ.image (vertexCode b)))
    (hE : Et.meaning (atomInput b) env = ofFinset (Finset.univ.image (edgeCode b)))
    (hR : R.meaning (atomInput b) env = ofFinset
      ((BFS.closure (boxGraph n) (Fintype.card (Atom b))).image (distanceCode (vertexCode b))))
    (hn : 1 ≤ n) :
    (tree ats VT Et R).meaning (atomInput b) env =
      ofFinset ((anchoredParents α).treeEdges.image (edgeCode b)) := by
  have hr := QuotedTerm.meaning_root (atomInput b) env ats VT R (vertexCode b)
    (vertexCode_injective hn) (boxGraph n) (boxGraph_connected n) α hα hV hR (vertex_card_le_atoms hn)
  have hpred (e : Edge n) :
      (existsIn VT.up (existsIn VT.up.up
        ((QuotedFormula.parent ats.up.up.up VT.up.up.up Et.up.up.up R.up.up.up
          (root ats VT R).up.up.up (var 1) (var 0)).and
            (hasEndpoints (var 2) (var 1) (var 0))))).meaning (atomInput b)
              (Fin.cons (edgeCode b e) env) ↔ e ∈ (anchoredParents α).treeEdges := by
    have hp (v w : Vertex n) := meaning_parent
      (Fin.cons (vertexCode b w) (Fin.cons (vertexCode b v) (Fin.cons (edgeCode b e) env)))
      ats.up.up.up VT.up.up.up Et.up.up.up R.up.up.up (root ats VT R).up.up.up (var 1) (var 0)
      α v w hres hα hV hE hR hr rfl rfl hn
    have hep (v w : Vertex n) := meaning_hasEndpoints
      (Fin.cons (vertexCode b w) (Fin.cons (vertexCode b v) (Fin.cons (edgeCode b e) env)))
      (var 2) (var 1) (var 0) e v w rfl rfl rfl hn
    simp only [meaning_existsIn,QuotedTerm.meaning_up,hV,elements_ofFinset,Finset.mem_image,
      Finset.mem_univ,true_and,exists_exists_eq_and,meaning_and,hp,hep]
    constructor
    · rintro ⟨v,w,⟨hv,rfl⟩,he⟩
      have hpe := (anchoredParents α).endpoints v hv
      have heq : e = (anchoredParents α).edge v hv := by
        apply edge_eq_of_endpoints
        rcases he with ⟨ht,hh⟩ | ⟨ht,hh⟩ <;> rcases hpe with ⟨hp,hp'⟩ | ⟨hp',hp⟩
        · exact Or.inr ⟨ht.symm.trans hp.symm,hh.symm.trans hp'.symm⟩
        · exact Or.inl ⟨ht.symm.trans hp'.symm,hh.symm.trans hp.symm⟩
        · exact Or.inl ⟨ht.symm.trans hp'.symm,hh.symm.trans hp.symm⟩
        · exact Or.inr ⟨ht.symm.trans hp.symm,hh.symm.trans hp'.symm⟩
      rw [heq]
      exact (anchoredParents α).edge_mem v hv
    · intro he
      obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp he
      refine ⟨v.val,(anchoredTree α).parent v.val,⟨v.property,rfl⟩,?_⟩
      rcases (anchoredParents α).endpoints v.val v.property with ⟨hh,ht⟩ | ⟨ht,hh⟩
      · exact Or.inr ⟨ht.symm,hh.symm⟩
      · exact Or.inl ⟨ht.symm,hh.symm⟩
  simp only [tree,QuotedTerm.meaning_filter,hE,elements_ofFinset]
  congr 1
  ext z
  simp only [Finset.mem_filter,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨⟨e,rfl⟩,h⟩
    exact ⟨e,(hpred e).mp h,rfl⟩
  · rintro ⟨e,he,rfl⟩
    exact ⟨⟨e,rfl⟩,(hpred e).mpr he⟩

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

@[simp] lemma atom_mem_edgeCode (e d : Edge n) (s : LocalGroup e) :
    atom (.inl ⟨e,s⟩) ∈ elements (edgeCode b d) ↔ e=d := by
  rw [mem_edgeCode_iff]
  constructor
  · rintro ⟨t,ht⟩
    exact congrArg Sigma.fst (Sum.inl.inj (atom_injective ht))
  · rintro rfl
    exact ⟨s,rfl⟩

end





end WitnessedSeparation.Grid


namespace WitnessedSeparation.Grid

noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

namespace QuotedGrid

open QuotedTerm QuotedFormula SourceSyntax SourceProgram

variable {k : ℕ}

lemma value_distance_edges (env : Fin k → HF (Atom b)) (V E : QuotedTerm k)
    (D : Finset (Edge n)) (p : Polynomial ℝ) (hp : GridResources p b)
    (hV : V.meaning (atomInput b) env = ofFinset (Finset.univ.image (vertexCode b)))
    (hE : E.meaning (atomInput b) env = ofFinset (D.image (edgeCode b))) (hn : 1 ≤ n) :
    (CPTTerm.distance (.quoted V) (.quoted E)).value (atomInput b) p env = distancesCode b (edgeGraph D) := by
  apply CPTTerm.distance_value (.quoted V) (.quoted E) (atomInput b) p env
    (vertexCode b) (vertexCode_injective hn) (edgeGraph D) (by simpa only [CPTTerm.value_quoted] using hV) _ hp.time hp.space
  intro u v
  simpa only [CPTTerm.value_quoted,hE] using blockAdjacent_edges (b := b) hn D u v

lemma value_distances (env : Fin k → HF (Atom b)) (p : Polynomial ℝ)
    (hp : GridResources p b) (hn : 1 ≤ n) :
    (SourceProgram.distances : CPTTerm k).value (atomInput b) p env = distancesCode b (boxGraph n) := by
  unfold SourceProgram.distances
  rw [value_distance_edges env _ _ Finset.univ p hp (quoted_vertexBlocks hn env) (quoted_edgeBlocks env) hn,
    edgeGraph_univ]

lemma value_connTable (env : Fin k → HF (Atom b)) (V T : QuotedTerm k)
    (D : Finset (Edge n)) (p : Polynomial ℝ) (hp : GridResources p b)
    (hV : V.meaning (atomInput b) env = ofFinset (Finset.univ.image (vertexCode b)))
    (hT : T.meaning (atomInput b) env = ofFinset (D.image (edgeCode b))) (hn : 1 ≤ n) :
    (SourceProgram.connTable V T).value (atomInput b) p env = connTableCode b D := by
  have hd (e : Edge n) :
      (T.up.diff (var 0).singleton).meaning (atomInput b) (Fin.cons (edgeCode b e) env) =
        ofFinset ((D.erase e).image (edgeCode b)) := by
    simp only [meaning_diff,QuotedTerm.meaning_up,hT,meaning_singleton,meaning_var,
      Fin.cons_zero,elements_ofFinset,Hereditary.singleton]
    congr 1
    ext z
    simp only [Finset.mem_filter,Finset.mem_image,Finset.mem_erase,Finset.mem_singleton]
    constructor
    · rintro ⟨⟨f,hf,rfl⟩,hne⟩
      exact ⟨f,⟨fun h => hne (by rw [h]),hf⟩,rfl⟩
    · rintro ⟨f,⟨hne,hf⟩,rfl⟩
      exact ⟨⟨f,hf,rfl⟩,fun h => hne (edgeCode_injective h)⟩
  simp only [SourceProgram.connTable,CPTTerm.value_map,CPTTerm.value_quoted,hT,elements_ofFinset,
    connTableCode,Finset.image_image]
  apply congrArg ofFinset
  apply Finset.image_congr
  intro e he
  simp only [Function.comp_apply]
  rw [CPTTerm.value_letIn,value_distance_edges (Fin.cons (edgeCode b e) env) V.up (T.up.diff (var 0).singleton)
    (D.erase e) p hp hV (hd e) hn]
  simp only [CPTTerm.value_quoted,meaning_pair,meaning_var,Fin.cons_zero,Fin.cons_one]

end QuotedGrid

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

open Classical WitnessedChoice

variable {n : ℕ}

lemma low_high_endpoints (α : Fin 4 → Vertex n) (e : Edge n) :
    (lowEnd α e = tail e ∧ highEnd α e = head e) ∨
      (highEnd α e = tail e ∧ lowEnd α e = head e) := by
  unfold lowEnd highEnd
  split_ifs <;> simp

lemma low_lt_high (α : Fin 4 → Vertex n) (hα : AnchoredTree.Resolving (boxGraph n) α) (e : Edge n) :
    vertexKey α (lowEnd α e) < vertexKey α (highEnd α e) := by
  have hne : vertexKey α (tail e) ≠ vertexKey α (head e) :=
    fun h => (head_ne_tail e) (hα h).symm
  unfold lowEnd highEnd
  split_ifs with h
  · exact h
  · exact lt_of_le_of_ne (le_of_not_gt h) hne.symm

lemma ordered_endpoints_iff (α : Fin 4 → Vertex n) (hα : AnchoredTree.Resolving (boxGraph n) α)
    (e : Edge n) (u v : Vertex n) :
    (((u=tail e ∧ v=head e) ∨ (v=tail e ∧ u=head e)) ∧ vertexKey α u < vertexKey α v) ↔
      u=lowEnd α e ∧ v=highEnd α e := by
  constructor
  · rintro ⟨(⟨rfl,rfl⟩|⟨rfl,rfl⟩),h⟩
    · simp only [lowEnd,highEnd,ite_eq_left h,and_self]
    · unfold lowEnd highEnd
      split_ifs with hh
      · exact False.elim ((not_lt_of_ge (le_of_lt h)) hh)
      · exact ⟨rfl,rfl⟩
  · rintro ⟨rfl,rfl⟩
    exact ⟨low_high_endpoints α e,low_lt_high α hα e⟩

lemma edgeKey_injective (α : Fin 4 → Vertex n) (hα : AnchoredTree.Resolving (boxGraph n) α) :
    Function.Injective (edgeKey α) := by
  intro e f h
  have h₁ := hα (congrArg (fun k : Lex (VertexKey × VertexKey) => (ofLex k).1) h)
  have h₂ := hα (congrArg (fun k : Lex (VertexKey × VertexKey) => (ofLex k).2) h)
  change lowEnd α e = lowEnd α f at h₁
  change highEnd α e = highEnd α f at h₂
  apply edge_eq_of_endpoints
  rcases low_high_endpoints α e with ⟨he,he'⟩ | ⟨he',he⟩ <;>
    rcases low_high_endpoints α f with ⟨hf,hf'⟩ | ⟨hf',hf⟩
  · exact Or.inl ⟨he.symm.trans (h₁.trans hf),he'.symm.trans (h₂.trans hf')⟩
  · exact Or.inr ⟨he.symm.trans (h₁.trans hf),he'.symm.trans (h₂.trans hf')⟩
  · exact Or.inr ⟨he'.symm.trans (h₂.trans hf'),he.symm.trans (h₁.trans hf)⟩
  · exact Or.inl ⟨he'.symm.trans (h₂.trans hf'),he.symm.trans (h₁.trans hf)⟩

lemma leastEdges_subsingleton (α : Fin 4 → Vertex n) (hα : AnchoredTree.Resolving (boxGraph n) α)
    (D : Finset (Edge n)) : (↑(leastEdges α D) : Set (Edge n)).Subsingleton := by
  intro e he f hf
  obtain ⟨he,hm⟩ := Finset.mem_filter.mp he
  obtain ⟨hf,hn⟩ := Finset.mem_filter.mp hf
  exact edgeKey_injective α hα (le_antisymm (le_of_not_gt (hm f hf)) (le_of_not_gt (hn e he)))

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

namespace QuotedGrid

open QuotedTerm QuotedFormula

variable {k : ℕ}

lemma meaning_edgeLt (env : Fin k → HF (Atom b)) (ats VT R et ft : QuotedTerm k)
    (α : Fin 4 → Vertex n) (e f : Edge n) (hres : AnchoredTree.Resolving (boxGraph n) α)
    (hα : ats.meaning (atomInput b) env = tupleCode (List.ofFn (vertexCode b ∘ α)))
    (hV : VT.meaning (atomInput b) env = ofFinset (Finset.univ.image (vertexCode b)))
    (hR : R.meaning (atomInput b) env = ofFinset
      ((BFS.closure (boxGraph n) (Fintype.card (Atom b))).image (distanceCode (vertexCode b))))
    (he : et.meaning (atomInput b) env = edgeCode b e)
    (hf : ft.meaning (atomInput b) env = edgeCode b f) (hn : 1 ≤ n) :
    (edgeLt ats VT R et ft).meaning (atomInput b) env ↔ edgeKey α e < edgeKey α f := by
  have hlt {l : ℕ} (env' : Fin l → HF (Atom b)) (at' R' ut vt : QuotedTerm l) (u v : Vertex n)
      (hat : at'.meaning (atomInput b) env' = tupleCode (List.ofFn (vertexCode b ∘ α)))
      (hR' : R'.meaning (atomInput b) env' = R.meaning (atomInput b) env)
      (hu : ut.meaning (atomInput b) env' = vertexCode b u)
      (hv : vt.meaning (atomInput b) env' = vertexCode b v) :
      (vertexLt at' R' ut vt).meaning (atomInput b) env' ↔ vertexKey α u < vertexKey α v := by
    exact QuotedFormula.meaning_vertexLt (atomInput b) env' at' R' ut vt (vertexCode b)
      (vertexCode_injective hn) (boxGraph n) (boxGraph_connected n) α u v hat (hR'.trans hR) hu hv (vertex_card_le_atoms hn)
  have hm (u v w z : Vertex n) := hlt
    (Fin.cons (vertexCode b z) (Fin.cons (vertexCode b w) (Fin.cons (vertexCode b v) (Fin.cons (vertexCode b u) env))))
    ats.up.up.up.up R.up.up.up.up
  have hp (u v w z : Vertex n) := meaning_hasEndpoints
    (Fin.cons (vertexCode b z) (Fin.cons (vertexCode b w) (Fin.cons (vertexCode b v) (Fin.cons (vertexCode b u) env))))
  simp only [edgeLt,meaning_existsIn,QuotedTerm.meaning_up,hV,elements_ofFinset,Finset.mem_image,
    Finset.mem_univ,true_and,exists_exists_eq_and,meaning_allList,List.mem_cons,
    List.mem_nil_iff,forall_eq_or_imp,forall_false,implies_true,and_true,meaning_and,meaning_or,meaning_eq,
    meaning_var,Fin.cons_zero,Fin.cons_one,fin_cons_two,fin_cons_three,(vertexCode_injective hn).eq_iff]
  have hh (u v w z : Vertex n) :
      (hasEndpoints et.up.up.up.up (var 3) (var 2)).meaning (atomInput b)
        (Fin.cons (vertexCode b z) (Fin.cons (vertexCode b w) (Fin.cons (vertexCode b v) (Fin.cons (vertexCode b u) env)))) ↔
          (u=tail e ∧ v=head e) ∨ (v=tail e ∧ u=head e) := hp u v w z _ _ _ e u v he rfl rfl hn
  have hh' (u v w z : Vertex n) :
      (hasEndpoints ft.up.up.up.up (var 1) (var 0)).meaning (atomInput b)
        (Fin.cons (vertexCode b z) (Fin.cons (vertexCode b w) (Fin.cons (vertexCode b v) (Fin.cons (vertexCode b u) env)))) ↔
          (w=tail f ∧ z=head f) ∨ (z=tail f ∧ w=head f) := hp u v w z _ _ _ f w z hf rfl rfl hn
  have hm32 (u v w z : Vertex n) :
      (vertexLt ats.up.up.up.up R.up.up.up.up (var 3) (var 2)).meaning (atomInput b)
        (Fin.cons (vertexCode b z) (Fin.cons (vertexCode b w) (Fin.cons (vertexCode b v) (Fin.cons (vertexCode b u) env)))) ↔
          vertexKey α u < vertexKey α v := hm u v w z _ _ u v hα rfl rfl rfl
  have hm10 (u v w z : Vertex n) :
      (vertexLt ats.up.up.up.up R.up.up.up.up (var 1) (var 0)).meaning (atomInput b)
        (Fin.cons (vertexCode b z) (Fin.cons (vertexCode b w) (Fin.cons (vertexCode b v) (Fin.cons (vertexCode b u) env)))) ↔
          vertexKey α w < vertexKey α z := hm u v w z _ _ w z hα rfl rfl rfl
  have hm31 (u v w z : Vertex n) :
      (vertexLt ats.up.up.up.up R.up.up.up.up (var 3) (var 1)).meaning (atomInput b)
        (Fin.cons (vertexCode b z) (Fin.cons (vertexCode b w) (Fin.cons (vertexCode b v) (Fin.cons (vertexCode b u) env)))) ↔
          vertexKey α u < vertexKey α w := hm u v w z _ _ u w hα rfl rfl rfl
  have hm20 (u v w z : Vertex n) :
      (vertexLt ats.up.up.up.up R.up.up.up.up (var 2) (var 0)).meaning (atomInput b)
        (Fin.cons (vertexCode b z) (Fin.cons (vertexCode b w) (Fin.cons (vertexCode b v) (Fin.cons (vertexCode b u) env)))) ↔
          vertexKey α v < vertexKey α z := hm u v w z _ _ v z hα rfl rfl rfl
  simp only [hh,hh',hm32,hm10,hm31,hm20]
  constructor
  · rintro ⟨u,v,w,z,he,hf,huv,hwz,h⟩
    obtain ⟨rfl,rfl⟩ := (ordered_endpoints_iff α hres e u v).mp ⟨he,huv⟩
    obtain ⟨rfl,rfl⟩ := (ordered_endpoints_iff α hres f w z).mp ⟨hf,hwz⟩
    rw [edgeKey,edgeKey,Prod.Lex.toLex_lt_toLex]
    exact h.imp id (fun ⟨he,hl⟩ => ⟨congrArg (vertexKey α) he,hl⟩)
  · intro h
    rw [edgeKey,edgeKey,Prod.Lex.toLex_lt_toLex] at h
    exact ⟨lowEnd α e,highEnd α e,lowEnd α f,highEnd α f,
      low_high_endpoints α e,low_high_endpoints α f,low_lt_high α hres e,low_lt_high α hres f,
      h.imp id (fun ⟨he,hl⟩ => ⟨hres he,hl⟩)⟩

end QuotedGrid

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

lemma selected_inter_empty (x : Finset (Σ e : Edge n, LocalGroup e)) (e : Edge n) :
    ofFinset ((elements (stateCode (x.image Sum.inl : Finset (Atom b)))) ∩ elements (edgeCode b e)) = emptyHF ↔
      missingEdge x e := by
  rw [show emptyHF = (ofFinset ∅ : HF (Atom b)) from rfl, ofFinset_inj,Finset.eq_empty_iff_forall_notMem]
  simp only [Finset.mem_inter,stateCode,elements_ofFinset,Finset.image_image,Finset.mem_image,Function.comp_apply]
  constructor
  · intro h r hr he
    exact h (atom (.inl r)) ⟨⟨r,hr,rfl⟩,(atom_mem_edgeCode _ _ _).mpr he⟩
  · rintro h z ⟨⟨r,hr,rfl⟩,he⟩
    exact h r hr ((atom_mem_edgeCode _ _ _).mp he)

namespace QuotedGrid

open QuotedTerm QuotedFormula

variable {k : ℕ}

lemma meaning_nextEdges (env : Fin k → HF (Atom b)) (ats VT ET R TT xt : QuotedTerm k)
    (α : Fin 4 → Vertex n) (T : Finset (Edge n)) (x : Finset (Σ e : Edge n, LocalGroup e))
    (hres : AnchoredTree.Resolving (boxGraph n) α)
    (hα : ats.meaning (atomInput b) env = tupleCode (List.ofFn (vertexCode b ∘ α)))
    (hV : VT.meaning (atomInput b) env = ofFinset (Finset.univ.image (vertexCode b)))
    (hE : ET.meaning (atomInput b) env = ofFinset (Finset.univ.image (edgeCode b)))
    (hR : R.meaning (atomInput b) env = ofFinset
      ((BFS.closure (boxGraph n) (Fintype.card (Atom b))).image (distanceCode (vertexCode b))))
    (hT : TT.meaning (atomInput b) env = ofFinset (T.image (edgeCode b)))
    (hx : xt.meaning (atomInput b) env = stateCode (x.image Sum.inl)) (hn : 1 ≤ n) :
    (nextEdges ats VT ET R TT xt).meaning (atomInput b) env =
      ofFinset ((leastEdges α (remainingEdges T x)).image (edgeCode b)) := by
  have hd : (ET.diff TT).meaning (atomInput b) env = ofFinset ((Finset.univ \ T).image (edgeCode b)) := by
    simp only [meaning_diff,hE,hT,elements_ofFinset]
    apply ofFinset_inj.mpr
    ext z
    simp only [Finset.mem_filter,Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_sdiff,
      not_exists,not_and]
    constructor
    · rintro ⟨⟨e,rfl⟩,he⟩
      refine ⟨e,?_,rfl⟩
      exact fun ht => he e ht rfl
    · rintro ⟨e,he,rfl⟩
      exact ⟨⟨e,rfl⟩,fun f hf hfe => he ((edgeCode_injective hfe) ▸ hf)⟩
  have hmiss {l : ℕ} (env' : Fin l → HF (Atom b)) (x' e' : QuotedTerm l) (e : Edge n)
      (hx' : x'.meaning (atomInput b) env' = stateCode (x.image Sum.inl))
      (he' : e'.meaning (atomInput b) env' = edgeCode b e) :
      (eq (x'.inter e') empty).meaning (atomInput b) env' ↔ missingEdge x e := by
    simp only [meaning_eq,meaning_inter,hx',he',meaning_empty]
    exact selected_inter_empty x e
  have hm1 (e : Edge n) := hmiss (Fin.cons (edgeCode b e) env) xt.up (var 0) e hx rfl
  have hm2 (e f : Edge n) := hmiss (Fin.cons (edgeCode b f) (Fin.cons (edgeCode b e) env)) xt.up.up (var 0) f hx rfl
  have ho (e f : Edge n) := meaning_edgeLt (Fin.cons (edgeCode b f) (Fin.cons (edgeCode b e) env))
    ats.up.up VT.up.up R.up.up (var 0) (var 1) α f e hres hα hV hR rfl rfl hn
  simp only [nextEdges,QuotedTerm.meaning_filter,hd,elements_ofFinset]
  apply ofFinset_inj.mpr
  ext z
  simp only [Finset.mem_filter,Finset.mem_image]
  constructor
  · rintro ⟨⟨⟨e,he,rfl⟩,hm⟩,hmin⟩
    refine ⟨e,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨he,(hm1 e).mp hm⟩,?_⟩,rfl⟩
    simp only [meaning_allIn,QuotedTerm.meaning_up,hd,elements_ofFinset,Finset.forall_mem_image,meaning_neg,meaning_and,hm2,ho] at hmin
    intro f hf
    obtain ⟨hf,hfm⟩ := Finset.mem_filter.mp hf
    exact fun hlt => hmin hf ⟨hfm,hlt⟩
  · rintro ⟨e,he,rfl⟩
    obtain ⟨he,hmin⟩ := Finset.mem_filter.mp he
    obtain ⟨he,hm⟩ := Finset.mem_filter.mp he
    refine ⟨⟨⟨e,he,rfl⟩,(hm1 e).mpr hm⟩,?_⟩
    simp only [meaning_allIn,QuotedTerm.meaning_up,hd,elements_ofFinset,Finset.forall_mem_image,meaning_neg,meaning_and,hm2,ho]
    intro f hf ⟨hfm,hlt⟩
    exact hmin f (Finset.mem_filter.mpr ⟨hf,hfm⟩) hlt

end QuotedGrid

end





noncomputable section

open Classical WitnessedChoice

variable {n : ℕ}

lemma mem_gridCandidates (α : Fin 4 → Vertex n) (T : Finset (Edge n))
    (x : Finset (Σ e : Edge n, LocalGroup e)) (r : Σ e : Edge n, LocalGroup e) :
    r ∈ gridCandidates α T x ↔ r.1 ∈ leastEdges α (remainingEdges T x) ∧ AcceptsFaces x r.1 r.2 := by
  simp only [gridCandidates,Finset.mem_filter,Finset.mem_univ,true_and]

lemma candidate_new_edge {α : Fin 4 → Vertex n} {T : Finset (Edge n)}
    {x : Finset (Σ e : Edge n, LocalGroup e)} {r : Σ e : Edge n, LocalGroup e}
    (hr : r ∈ gridCandidates α T x) : r.1 ∉ T ∧ missingEdge x r.1 := by
  obtain ⟨hh,_⟩ := (mem_gridCandidates α T x r).mp hr
  have he := (Finset.mem_filter.mp hh).1
  simpa only [remainingEdges,Finset.mem_filter,Finset.mem_sdiff,Finset.mem_univ,true_and] using he

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.TreeTest RelationPools

variable {n : ℕ} {b : Vertex n → Scalar}

lemma actionPerm_edgeBlock (g : BoxGroup n) (e : Edge n) :
    (edgeBlockSet b e).image (actionPerm g) = edgeBlockSet b e := by
  apply Finset.eq_of_subset_of_card_le
  · intro a ha
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨s,rfl⟩ := (mem_edgeBlockSet e d).mp hd
    exact (mem_edgeBlockSet e _).mpr ⟨restrictGroup e g*s,rfl⟩
  · rw [Finset.card_image_of_injective _ (actionPerm g).injective]

lemma actionPerm_vertexBlock (g : BoxGroup n) (v : Vertex n) :
    (vertexBlockSet b v).image (actionPerm g) = vertexBlockSet b v := by
  apply Finset.eq_of_subset_of_card_le
  · intro a ha
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨s,rfl⟩ := (mem_vertexBlockSet v d).mp hd
    exact (mem_vertexBlockSet v _).mpr ⟨actConfiguration g s,rfl⟩
  · rw [Finset.card_image_of_injective _ (actionPerm g).injective]

lemma actionPerm_blocks (hn : 1 ≤ n) (g : BoxGroup n) :
    ∀ u ∈ blocks (atomInput b), u.image (actionPerm g) = u := by
  intro u hu
  rcases Finset.mem_union.mp hu with hu | hu
  · rw [edgeBlocks_grid] at hu
    obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp hu
    exact actionPerm_edgeBlock g e
  · rw [vertexBlocks_grid hn] at hu
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hu
    exact actionPerm_vertexBlock g v

namespace ParentEdges

variable {T : RootedTree (Vertex n)} (P : ParentEdges T)

lemma fundamental_mem {N : Finset (Edge n)} {e : Edge n} (he : e ∈ N) (a : Scalar) :
    graph (actionPerm (b := b) (⟨0,P.flow e a⟩ : BoxGroup n)) ∈ P.fundamentalPool N :=
  Finset.mem_image.mpr ⟨(e,a),Finset.mem_product.mpr ⟨he,Finset.mem_univ _⟩,rfl⟩

lemma grid_transitivity (hn : 1 ≤ n) (α : Fin 4 → Vertex n)
    (hα : AnchoredTree.Resolving (boxGraph n) α)
    (x : Finset (Σ e : Edge n, LocalGroup e)) (hoff : ∀ r ∈ x, r.1 ∉ P.treeEdges)
    (r t : Σ e : Edge n, LocalGroup e)
    (hr : r ∈ gridCandidates α P.treeEdges x) (ht : t ∈ gridCandidates α P.treeEdges x) :
    ∃ g ∈ witnessPool localBound (atomInput b) True
      (fun _ => P.fundamentalPool (leastEdges α (remainingEdges P.treeEdges x))) (x.image Sum.inl),
      g (.inl r) = .inl t := by
  obtain ⟨hrN,hrs⟩ := (mem_gridCandidates α P.treeEdges x r).mp hr
  obtain ⟨htN,hts⟩ := (mem_gridCandidates α P.treeEdges x t).mp ht
  have ret := leastEdges_subsingleton α hα _ hrN htN
  rcases r with ⟨e,s⟩
  rcases t with ⟨e',t⟩
  dsimp at ret
  subst e'
  have hen := (candidate_new_edge hr).1
  have hnew := (candidate_new_edge hr).2
  let l := actionPerm (b := b) (⟨faceDelta e s t,0⟩ : BoxGroup n)
  let a := t.flow - (restrictGroup e (⟨faceDelta e s t,0⟩ : BoxGroup n) * s).flow
  let c := actionPerm (b := b) (⟨0,P.flow e a⟩ : BoxGroup n)
  have fixl : ∀ r ∈ x, l (.inl r) = .inl r := fun r hr => faceDelta_fix_past hrs hts hr
  have fixc : ∀ r ∈ x, c (.inl r) = .inl r := by
    intro r hr
    apply central_fix_edge
    exact P.flow_other e r.1 (hoff r hr) (hnew r hr) a
  have hfilter : PoolFilter (atomInput b) (x.image Sum.inl) (c*l) := by
    refine ⟨(fullAut (atomInput b)).mul_mem (actionPerm_fullAut _) (actionPerm_fullAut _),?_,?_⟩
    · intro u hu
      change u.image (c ∘ l) = u
      rw [←Finset.image_image,actionPerm_blocks hn _ u hu,actionPerm_blocks hn _ u hu]
    · intro a ha
      obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp ha
      change c (l (.inl r)) = _
      rw [fixl r hr,fixc r hr]
  refine ⟨c*l,?_,?_⟩
  · rw [witnessPool,ite_eq_left True.intro]
    apply Finset.mem_insert_of_mem
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨hfilter,graph l,faceDelta_in_localPool hn e s t,
      graph c,P.fundamental_mem hrN a,compose_graph l c⟩
  · exact central_after_local e s t (P.flow e a) (P.flow_self e hen a)

end ParentEdges

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.TreeTest

variable {n : ℕ} {b : Vertex n → Scalar}

lemma mem_edgeState (x : Finset (Σ e : Edge n, LocalGroup e)) (a : Atom b) :
    a ∈ edgeState x ↔ ∃ r ∈ x, Sum.inl r = a := Finset.mem_image

end





end WitnessedSeparation.Grid

end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_ChoiceSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace WitnessedSeparation.Grid

noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary RelationPools

variable {n : ℕ} {b : Vertex n → Scalar}

namespace QuotedGrid

open QuotedTerm QuotedFormula SourceSyntax SourceProgram

attribute [local irreducible] QuotedTerm.nextEdges QuotedTerm.tree SourceSyntax.cycleRelations

lemma fundamentalPool_in_cycleSet (p : Polynomial ℝ) (hp : GridResources p b)
    (α : Fin 4 → Vertex n) (hα : AnchoredTree.Resolving (boxGraph n) α)
    (x : Finset (Σ e : Edge n, LocalGroup e)) (hn : 1 ≤ n) :
    (anchoredParents α).fundamentalPool (leastEdges α (remainingEdges (anchoredParents α).treeEdges x)) ⊆
      SourceProgram.program.body.cycleSet (atomInput b) p
        (tupleCode (List.ofFn (vertexCode b ∘ α))) (edgeState x) := by
  let R := distancesCode b (boxGraph n)
  let T := ofFinset ((anchoredParents α).treeEdges.image (edgeCode b))
  let H := connTableCode b (anchoredParents α).treeEdges
  let env₀ : Fin 3 → HF (Atom b) := Fin.cons R
    (Fin.cons (stateCode (edgeState x)) (Fin.cons (tupleCode (List.ofFn (vertexCode b ∘ α))) Fin.elim0))
  let env₁ : Fin 4 → HF (Atom b) := Fin.cons T env₀
  let env : Fin 5 → HF (Atom b) := Fin.cons H env₁
  have ht : (tree (var 2) QuotedTerm.vertexBlocks QuotedTerm.edgeBlocks (var 0)).meaning
      (atomInput b) env₀ = T :=
    meaning_tree env₀ (var 2) _ _ (var 0) α hα rfl
      (quoted_vertexBlocks hn env₀) (quoted_edgeBlocks env₀) rfl hn
  have hh : (SourceProgram.connTable QuotedTerm.vertexBlocks (var 0)).value
      (atomInput b) p env₁ = H :=
    value_connTable env₁ _ _ (anchoredParents α).treeEdges p hp
      (quoted_vertexBlocks hn env₁) rfl hn
  have hv : SourceProgram.cycles.value (atomInput b) p
      (Fin.cons (stateCode (edgeState x)) (Fin.cons (tupleCode (List.ofFn (vertexCode b ∘ α))) Fin.elim0)) =
      (cycleRelations QuotedTerm.vertexBlocks QuotedTerm.edgeBlocks
        (faces QuotedTerm.vertexBlocks QuotedTerm.edgeBlocks) (var 2) (var 1) (var 0)
        (nextEdges (var 4) QuotedTerm.vertexBlocks QuotedTerm.edgeBlocks (var 2) (var 1) (var 3))).meaning
        (atomInput b) env := by
    rw [SourceProgram.cycles,CPTTerm.value_letIn,value_distances _ p hp hn,
      CPTTerm.value_letIn,CPTTerm.value_quoted]
    change ((SourceProgram.connTable QuotedTerm.vertexBlocks (var 0)).letIn _).value (atomInput b) p
      (Fin.cons ((tree (var 2) QuotedTerm.vertexBlocks QuotedTerm.edgeBlocks (var 0)).meaning (atomInput b) env₀) env₀) = _
    rw [ht,CPTTerm.value_letIn]
    change (CPTTerm.quoted _).value (atomInput b) p
      (Fin.cons ((SourceProgram.connTable QuotedTerm.vertexBlocks (var 0)).value (atomInput b) p env₁) env₁) = _
    rw [hh,CPTTerm.value_quoted]
  have hV := quoted_vertexBlocks (b := b) hn env
  have hE := quoted_edgeBlocks (b := b) env
  have hN := meaning_nextEdges env (var 4) QuotedTerm.vertexBlocks QuotedTerm.edgeBlocks (var 2)
    (var 1) (var 3) α (anchoredParents α).treeEdges x hα rfl hV hE rfl rfl rfl hn
  intro r hr
  change r ∈ (elements (SourceProgram.cycles.value (atomInput b) p _)).image decodeRelation
  rw [hv]
  refine Finset.mem_image.mpr ⟨relationCode r,?_,decodeRelation_code r⟩
  apply fundamentalPool_in_cycles env QuotedTerm.vertexBlocks QuotedTerm.edgeBlocks
    (faces QuotedTerm.vertexBlocks QuotedTerm.edgeBlocks) (var 2) (var 1) (var 0) _
    (anchoredParents α) _ hV hE (mem_faces env _ _ hV hE hn) rfl rfl rfl hN _ hn r hr
  intro e he
  exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).1).2

end QuotedGrid

end

end WitnessedSeparation.Grid


section

namespace WitnessedChoice.RelationPools

noncomputable section

open Classical WitnessedSeparation

variable {A : Type} [Fintype A]

lemma witnessPool_mono (B : ℕ) (S : Input A) (valid : Prop)
    (C D : Finset A → Finset (Relation A)) (x : Finset A) (hCD : C x ⊆ D x) :
    witnessPool B S valid C x ⊆ witnessPool B S valid D x := by
  unfold witnessPool
  split_ifs
  · intro g hg
    rcases Finset.mem_insert.mp hg with hg | hg
    · exact Finset.mem_insert.mpr (Or.inl hg)
    · apply Finset.mem_insert_of_mem
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hg ⊢
      obtain ⟨hf,l,hl,c,hc,he⟩ := hg
      exact ⟨hf,l,hl,c,hCD hc,he⟩
  · exact Finset.Subset.refl _

end

end WitnessedChoice.RelationPools

namespace WitnessedSeparation.Grid

noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary RelationPools

variable {n : ℕ} {b : Vertex n → Scalar}

namespace QuotedGrid

open SourceProgram

lemma selection_transitive_oai (p : Polynomial ℝ) (hp : GridResources p b)
    (α : Fin 4 → Vertex n) (hα : AnchoredTree.Resolving (boxGraph n) α)
    (x : Finset (Σ e : Edge n, LocalGroup e))
    (hoff : ∀ r ∈ x, r.1 ∉ (anchoredParents α).treeEdges) (hn : 1 ≤ n) :
    (SourceProgram.program.body.selection (atomInput b) p
      (tupleCode (List.ofFn (vertexCode b ∘ α)))).TransitiveAt (edgeState x) := by
  intro a ha d hd
  rw [selection_candidates p hp α hα x hn] at ha hd
  obtain ⟨r,hr,rfl⟩ := (mem_edgeState _ _).mp ha
  obtain ⟨t,ht,rfl⟩ := (mem_edgeState _ _).mp hd
  obtain ⟨g,hg,hgr⟩ := (anchoredParents α).grid_transitivity hn α hα x hoff r t hr ht
  refine ⟨g,?_,hgr⟩
  change g ∈ witnessPool localBound (atomInput b) True
    (program.body.cycleSet (atomInput b) p (tupleCode (List.ofFn (vertexCode b ∘ α)))) (edgeState x)
  exact witnessPool_mono localBound (atomInput b) True _ _ (edgeState x)
    (fundamentalPool_in_cycleSet p hp α hα x hn) hg

end QuotedGrid

end

end WitnessedSeparation.Grid

end


end OAI
end

theorem solution : type_of% @OAI.WitnessedSeparation.Grid.QuotedGrid.selection_transitive_oai := @OAI.WitnessedSeparation.Grid.QuotedGrid.selection_transitive_oai
