-- Prove2me | solution 1 for OAI.WitnessedSeparation.Grid.QuotedGrid.formula_value
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T00:28:26.484354+00:00
-- url     : https://prove2.me/submissions/c2e2a334-45e7-45bf-96eb-9000e96d7673

import Mathlib
import Definitions.Def_WitnessedChoice
import Definitions.Def_OAIQ4Wc000
import Theorems.Thm_OAI_WitnessedSeparation_Grid_QuotedGrid_selection_candidates
import Theorems.Thm_OAI_WitnessedSeparation_Grid_QuotedGrid_selection_transitive

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_GridAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WitnessedSeparation.Grid

variable {n : ℕ}

theorem sum_boundary (z : Edge n → Scalar) : ∑ v, boundary z v = 0 := by
  classical
  simp only [boundary, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply,
    Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro e _
  simp [mul_sub,Finset.sum_sub_distrib,← Finset.mul_sum]

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

namespace WitnessedChoice

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

variable {A : Type}

theorem stateCode_fixed_of_pointwise {g : Equiv.Perm A} {x : Finset A}
    (h : ∀ a ∈ x, g a = a) : g • stateCode x = stateCode x := by
  rw [smul_stateCode, stateCode_inj]
  calc
    x.image g = x.image id := Finset.image_congr h
    _ = x := Finset.image_id

namespace Selection

variable {P : Selection A}

theorem advance_mono (x : Finset A) (c : Option A) : x ⊆ advance x c := by
  cases c
  · exact Finset.Subset.refl _
  · exact Finset.subset_insert _ _

theorem advance_card {x : Finset A} {c : Option A} (h : x ≠ advance x c) :
    (advance x c).card = x.card + 1 := by
  cases c with
  | none => exact (h rfl).elim
  | some a =>
    change (insert a x).card = _
    apply Finset.card_insert_of_notMem
    intro ha
    exact h (Finset.insert_eq_of_mem ha).symm

theorem Prefix.restrict {b c k l} (h : P.Prefix b c k) (hle : l ≤ k) :
    P.Prefix b c l :=
  ⟨h.1, fun i hi => h.2 i (Nat.lt_of_lt_of_le hi hle)⟩

theorem Prefix.monotone {b c k} (h : P.Prefix b c k) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ k) : b i ⊆ b j := by
  induction j, hij using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ j hij ih =>
    have hjk : j < k := by omega
    have hs := h.2 j hjk
    rw [hs.2]
    exact (ih (by omega)).trans (advance_mono _ _)

theorem Prefix.card_eq {b c k} (h : P.Prefix b c k)
    (hstrict : ∀ i < k, b i ≠ b (i+1)) : ∀ i ≤ k, (b i).card = i := by
  intro i hi
  induction i with
  | zero => simp [h.1]
  | succ i ih =>
    have hic : i < k := by omega
    have hs := h.2 i hic
    rw [hs.2, advance_card (by simpa [hs.2] using hstrict i hic), ih (by omega)]

theorem FirstStabilization.length_le [Fintype A] {b c t} (h : P.FirstStabilization b c t) :
    t ≤ Fintype.card A := by
  have hc := (h.1.restrict (Nat.le_succ t)).card_eq h.2.1 t le_rfl
  rw [← hc]
  exact Finset.card_le_univ _

theorem exists_first_stabilization [Fintype A] {b c}
    (h : ∀ k, P.Prefix b c k) : ∃ t ≤ Fintype.card A, P.FirstStabilization b c t := by
  have hex : ∃ t, b t = b (t+1) := by
    by_contra hn
    push Not at hn
    have hc := (h (Fintype.card A + 1)).card_eq (fun i _ => hn i) (Fintype.card A + 1) le_rfl
    have hb := Finset.card_le_univ (b (Fintype.card A + 1))
    omega
  refine ⟨Nat.find hex, ?_, h _, ?_, Nat.find_spec hex⟩
  · have hh : P.FirstStabilization b c (Nat.find hex) :=
      ⟨h _, fun i hi => Nat.find_min hex hi, Nat.find_spec hex⟩
    exact hh.length_le
  · exact fun i hi => Nat.find_min hex hi

theorem Filtered.history {S : Input A} {α : HF A} (hf : P.Filtered S α)
    {b c k} (hp : P.Prefix b c k) {i : ℕ} (hi : i ≤ k)
    {g : Equiv.Perm A} (hg : g ∈ P.witnesses (b i)) : HistoryAut S α b i g := by
  refine ⟨hf.2.1 _ _ hg, ?_⟩
  intro j hji
  apply stateCode_fixed_of_pointwise
  intro a ha
  exact hf.2.2 _ _ hg _ (hp.monotone hji hi ha)

theorem Filtered.witnessed {S : Input A} {α : HF A} (hf : P.Filtered S α)
    {b c k} (hp : P.Prefix b c k) {i : ℕ} (hi : i ≤ k) (terminal : Finset A) :
    P.WitnessedAt S α b terminal i := by
  refine ⟨choices_nonempty _, fun g hg => hf.history hp hi hg, ?_⟩
  intro u hu v hv
  by_cases ht : (P.candidates (b i)).Nonempty ∧ P.TransitiveAt (b i)
  · simp only [choices, ite_eq_left ht, Finset.mem_image] at hu hv
    obtain ⟨a, ha, rfl⟩ := hu
    obtain ⟨a', ha', rfl⟩ := hv
    obtain ⟨g, hg, hga⟩ := ht.2 a ha a' ha'
    refine ⟨g, hg, ?_⟩
    simpa [choiceCode] using congrArg atom hga
  · have hu' : u = none := by simpa [choices, ht] using hu
    have hv' : v = none := by simpa [choices, ht] using hv
    subst u; subst v
    exact ⟨1, hf.1 _, one_smul _ _⟩

end Selection

end

end WitnessedChoice

end

section

namespace WitnessedChoice

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

variable {A : Type}

namespace Selection

variable [Fintype A]

variable {P : Selection A} {S : Input A} {α : HF A}

omit [Fintype A] in
theorem selected_mem (x : Finset A) : P.selected x ∈ P.choices x :=
  (choices_nonempty (P := P) x).choose_spec

omit [Fintype A] in
theorem run_prefix (k : ℕ) : P.Prefix P.run (fun i => P.selected (P.run i)) k := by
  exact ⟨rfl, fun i _ => ⟨selected_mem _, rfl⟩⟩

theorem exists_path : ∃ b c t, P.FirstStabilization b c t := by
  obtain ⟨t, _, ht⟩ := exists_first_stabilization (P := P) P.run_prefix
  exact ⟨P.run, (fun i => P.selected (P.run i)), t, ht⟩

end Selection

end

end WitnessedChoice

end

section

namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

variable {A : Type} [Fintype A]

namespace Realizes

variable {P : Selection A} {step : HF A → HF A → Result (HF A)}
  {choice : HF A → Result (HF A)} {witness : HF A → HF A → Result (HF A)}
  (hr : Realizes P step choice witness)

include hr

theorem prefix_decode {b c : ℕ → HF A} {k : ℕ} (hp : ChoicePrefix step choice b c k) :
    P.Prefix (decodeState ∘ b) (decodeChoice ∘ c) k ∧
    (∀ i ≤ k, b i = stateCode (decodeState (b i))) ∧
    (∀ i < k, c i = choiceCode (decodeChoice (c i))) := by
  have h0 : decodeState (b 0) = ∅ := by simp [hp.1, emptyHF, decodeState]
  have hstates : ∀ i ≤ k, b i = stateCode (decodeState (b i)) := by
    intro i hi
    induction i with
    | zero => simp [hp.1, emptyHF, stateCode, decodeState]
    | succ i ih =>
      have hik : i < k := by omega
      obtain ⟨⟨D, hD, hc⟩, hs⟩ := hp.2 i hik
      have hb := ih (by omega)
      rw [hb, hr.choice_eq] at hD
      cases hD
      simp only [elements_ofFinset] at hc
      obtain ⟨a, ha, hac⟩ := Finset.mem_image.mp hc
      have he := hr.step_eq (decodeState (b i)) a ha
      rw [← hb, hac] at he
      rw [he] at hs
      have hs' := Option.some.inj hs
      rw [← hs', decodeState_code]
  have hchoices : ∀ i < k, ∃ a ∈ P.choices (decodeState (b i)), choiceCode a = c i := by
    intro i hi
    obtain ⟨⟨D, hD, hc⟩, _⟩ := hp.2 i hi
    rw [hstates i (by omega), hr.choice_eq] at hD
    cases hD
    simp only [elements_ofFinset] at hc
    exact Finset.mem_image.mp hc
  refine ⟨⟨h0, ?_⟩, hstates, ?_⟩
  · intro i hi
    obtain ⟨a, ha, hac⟩ := hchoices i hi
    have hd : decodeChoice (c i) = a := by rw [← hac, decodeChoice_code]
    refine ⟨by simpa only [Function.comp_apply, hd] using ha, ?_⟩
    obtain ⟨_, hs⟩ := hp.2 i hi
    rw [hstates i (by omega), ← hac, hr.step_eq _ _ ha] at hs
    have he := Option.some.inj hs
    simp only [Function.comp_apply, hd]
    rw [← he, decodeState_code]
  · intro i hi
    obtain ⟨a, _, hac⟩ := hchoices i hi
    rw [← hac, decodeChoice_code]

theorem first_decode {b c : ℕ → HF A} {t : ℕ} (hp : FirstPath step choice b c t) :
    P.FirstStabilization (decodeState ∘ b) (decodeChoice ∘ c) t := by
  obtain ⟨hpre, hb, _⟩ := hr.prefix_decode hp.1
  refine ⟨hpre, ?_, congrArg decodeState hp.2.2⟩
  intro i hi he
  apply hp.2.1 i hi
  rw [hb i (by omega), hb (i+1) (by omega)]
  exact congrArg stateCode he

theorem good {S : Input A} {α : HF A} (hf : P.Filtered S α)
    (p : ℕ) (hp : Fintype.card A + 2 ≤ p) (free : Finset (Fin 1))
    (output : HF A → Result Bool) (hout : ∀ x : Finset A, (output (stateCode x)).isSome) :
    GoodWSC S p free (Fin.cons α Fin.elim0) step choice witness output := by
  constructor
  · intro b c k hk hstrict
    obtain ⟨hpre, hb, hc⟩ := hr.prefix_decode hk
    have hs : ∀ i < k, (decodeState ∘ b) i ≠ (decodeState ∘ b) (i+1) := by
      intro i hi he
      apply hstrict i hi
      rw [hb i (by omega), hb (i+1) (by omega)]
      exact congrArg stateCode he
    have hn : k ≤ Fintype.card A := by
      rw [← hpre.card_eq hs k le_rfl]
      exact Finset.card_le_univ _
    refine ⟨by omega, ?_, ofFinset ((P.choices (decodeState (b k))).image choiceCode), ?_, ?_, ?_⟩
    · rw [hb k le_rfl, TC_stateCode, Finset.card_image_of_injective _ atom_injective]
      exact (Finset.card_le_univ _).trans (by omega)
    · rw [hb k le_rfl, hr.choice_eq, decodeState_code]
    · simpa only [elements_ofFinset, Finset.image_nonempty] using P.choices_nonempty (decodeState (b k))
    · intro u hu
      simp only [elements_ofFinset] at hu
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
      rw [hb k le_rfl, hr.step_eq _ _ ha]
      simp
  · intro b c t ht
    obtain ⟨hpre, hb, hc⟩ := hr.prefix_decode ht.1
    have hfirst := hr.first_decode ht
    have hn := hfirst.length_le
    refine ⟨by omega, ?_, ?_⟩
    · intro i hi
      let x := decodeState (b i)
      let z := decodeState (b t)
      refine ⟨ofFinset ((P.choices x).image choiceCode),
        ofFinset ((P.witnesses x).image permutationGraph), ?_, ?_, ?_⟩
      · rw [hb i (by omega), hr.choice_eq]
      · rw [hb t (by omega), hb i (by omega), hr.witness_eq]
      · obtain ⟨_, hwnd, htrans⟩ := hf.witnessed hpre (by omega : i ≤ t+1) z
        refine ⟨by simp, ?_, ?_⟩
        · intro w hw
          simp only [elements_ofFinset] at hw
          obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hw
          obtain ⟨hpar, hhist⟩ := hwnd g hg
          refine ⟨g, rfl, hpar.1, ?_, ?_⟩
          · intro j hj
            have hj0 : j = 0 := Fin.eq_zero j
            subst j
            exact hpar.2
          · intro j hj
            rw [hb j (by omega)]
            exact hhist j hj
        · intro u hu v hv
          simp only [elements_ofFinset] at hu
          obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
          simp only [elements_ofFinset] at hv
          obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp hv
          obtain ⟨g, hg, he⟩ := htrans a ha a' ha'
          refine ⟨g, ?_, he⟩
          simp only [elements_ofFinset]
          apply Finset.mem_image.mpr
          exact ⟨g, hg, rfl⟩
    · rw [hb t (by omega)]
      exact hout _

end Realizes

end

end WitnessedChoice.BGS

end

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

lemma Formula.eval_letIn (S : Input A) (p : Polynomial ℝ) {n : ℕ}
    (v : Term n) (b : Formula (n+1)) (env : Fin n → HF A) {x : HF A} {c : Bool}
    (hv : v.eval S p env = some x) (hz : b.wscCount = 0)
    (hb : b.eval S p (Fin.cons x env) = some c) :
    (Formula.letIn v b).eval S p env = some c := by
  let f := fun z => (b.total S p hz (Fin.cons z env)).choose
  have hf (z) : b.eval S p (Fin.cons z env) = some (f z) :=
    (b.total S p hz (Fin.cons z env)).choose_spec
  have hx : f x = c := Option.some.inj ((hf x).symm.trans hb)
  rw [Formula.letIn,eval_existsIn S p _ _ env (Term.eval_singleton S p v env hv) hf]
  simp [Hereditary.singleton,hx]

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



namespace WitnessedChoice

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

open RelationPools

variable {A : Type} [Fintype A]

omit [Fintype A] in
lemma smul_pair (g : Equiv.Perm A) (x y : HF A) :
    g • pair x y = pair (g • x) (g • y) := map_pair g x y

omit [Fintype A] in
lemma tupleCode_fixed (g : Equiv.Perm A) (xs : List (HF A))
    (h : ∀ x ∈ xs, g • x = x) : g • tupleCode xs = tupleCode xs := by
  induction xs with
  | nil => simp [tupleCode,ordinal,smul_ofFinset]
  | cons x xs ih =>
    simp only [tupleCode,smul_pair]
    rw [h x (by simp),ih (fun y hy => h y (by simp [hy]))]

omit [Fintype A] in
lemma parameterCode_fixed (g : Equiv.Perm A) (α : Fin 4 → Finset A)
    (h : ∀ i, (α i).image g = α i) : g • parameterCode α = parameterCode α := by
  apply tupleCode_fixed
  intro x hx
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
  dsimp [Function.comp_apply]
  rw [smul_stateCode,h i]

variable (B : ℕ)

lemma one_mem_witnessPool (S : Input A) (valid : Prop)
    (C : Finset A → Finset (Relation A)) (x : Finset A) :
    (1 : Equiv.Perm A) ∈ witnessPool B S valid C x := by
  unfold witnessPool
  split_ifs <;> simp

lemma witnessPool_filter (S : Input A) (valid : Prop)
    (C : Finset A → Finset (Relation A)) (x : Finset A) {g : Equiv.Perm A}
    (h : g ∈ witnessPool B S valid C x) : PoolFilter S x g := by
  unfold witnessPool at h
  split_ifs at h
  · rcases Finset.mem_insert.mp h with rfl | h
    · exact ⟨(fullAut S).one_mem,by simp,by simp⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
      exact h.1
  · have hg : g = 1 := Finset.mem_singleton.mp h
    subst g
    exact ⟨(fullAut S).one_mem,by simp,by simp⟩

theorem guardedSelection_filtered (S : Input A) (valid : Prop)
    (D : Finset A → Finset A) (C : Finset A → Finset (Relation A))
    (α : Fin 4 → Finset A) (hα : ∀ i, α i ∈ blocks S) :
    (guardedSelection B S valid D C).Filtered S (parameterCode α) := by
  refine ⟨one_mem_witnessPool B S valid C,?_,?_⟩
  · intro x g hg
    obtain ⟨ha,hb,_⟩ := witnessPool_filter B S valid C x hg
    exact ⟨ha,parameterCode_fixed g α (fun i => hb (α i) (hα i))⟩
  · intro x g hg
    exact (witnessPool_filter B S valid C x hg).2.2

end

end WitnessedChoice



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

lemma meaning_composition (l c : QuotedTerm n) (r t : Relation A)
    (hl : l.meaning S env = relationCode r) (hc : c.meaning S env = relationCode t) :
    (composition l c).meaning S env = relationCode (compose r t) := by
  simp only [composition,meaning_relation,QuotedFormula.meaning_existsIn,meaning_atoms,
    exists_stateCode,Finset.mem_univ,true_and,QuotedFormula.meaning_and,
    QuotedFormula.meaning_link,meaning_var,Fin.cons_zero,Fin.cons_one,
    fin_cons_two,meaning_up,hl,hc,pair_mem_relationCode]
  rfl

end QuotedTerm

end





noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary RelationPools

variable {A : Type} [Fintype A]

lemma functionalOnto_iff (r : Relation A) : FunctionalOnto r ↔ ∃ g : Equiv.Perm A, r = graph g := by
  constructor
  · intro h
    let f : A → A := fun a => (h.1 a).choose
    have hf (a : A) : (a,f a) ∈ r ∧ ∀ b, (a,b) ∈ r → b = f a := (h.1 a).choose_spec
    have hs : Function.Surjective f := by
      intro b
      obtain ⟨a,hab⟩ := h.2 b
      exact ⟨a,((hf a).2 b hab).symm⟩
    let g : Equiv.Perm A := Equiv.ofBijective f ⟨Finite.injective_iff_surjective.mpr hs,hs⟩
    refine ⟨g,?_⟩
    ext ⟨a,b⟩
    simp only [mem_graph]
    constructor
    · intro hab
      exact ((hf a).2 b hab).symm
    · intro he
      rw [←he]
      exact (hf a).1
  · rintro ⟨g,rfl⟩
    constructor
    · intro a
      exact ⟨g a,by simp,fun b hb => (mem_graph g a b).mp hb |>.symm⟩
    · intro b
      exact ⟨g.symm b,by simp⟩

lemma rawFilter_graph (S : Input A) (x : Finset A) (g : Equiv.Perm A) :
    RawFilter S x (graph g) ↔ PoolFilter S x g := by
  constructor
  · rintro ⟨_,hR,hB,hx⟩
    refine ⟨?_,?_,?_⟩
    · intro R a b
      exact (hR R a b (g a) (g b) (by simp) (by simp)).symm
    · intro u hu
      apply Finset.eq_of_subset_of_card_le
      · intro y hy
        obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hy
        exact hB u hu a ha (g a) (by simp)
      · rw [Finset.card_image_of_injective _ g.injective]
    · intro a ha
      exact (mem_graph g a a).mp (hx a ha)
  · rintro ⟨hR,hB,hx⟩
    refine ⟨(functionalOnto_iff _).mpr ⟨g,rfl⟩,?_,?_,?_⟩
    · intro R a a' b b' hab ha'b'
      rw [←(mem_graph g a b).mp hab,←(mem_graph g a' b').mp ha'b']
      exact (hR R a a').symm
    · intro u hu a ha b hab
      rw [←(mem_graph g a b).mp hab,←hB u hu]
      exact Finset.mem_image.mpr ⟨a,ha,rfl⟩
    · intro a ha
      exact (mem_graph g a a).mpr (hx a ha)

lemma rawFilter_iff (S : Input A) (x : Finset A) (r : Relation A) :
    RawFilter S x r ↔ ∃ g : Equiv.Perm A, r = graph g ∧ PoolFilter S x g := by
  constructor
  · intro h
    obtain ⟨g,rfl⟩ := (functionalOnto_iff r).mp h.1
    exact ⟨g,rfl,(rawFilter_graph S x g).mp h⟩
  · rintro ⟨g,rfl,hg⟩
    exact (rawFilter_graph S x g).mpr hg

namespace QuotedFormula

variable {n : ℕ}

variable (S : Input A) (env : Fin n → HF A)

lemma meaning_functional (r : QuotedTerm n) (R : Relation A) (hr : r.meaning S env = relationCode R) :
    (functional r).meaning S env ↔ ∀ a, ∃! b, (a,b) ∈ R := by
  simp [functional,hr,ExistsUnique,atom_injective.eq_iff,pairCode]
  constructor
  · intro h a
    obtain ⟨b,hb,hu⟩ := h a
    exact ⟨b,hb,fun c hc => hu c a c hc rfl rfl⟩
  · intro h a
    obtain ⟨b,hb,hu⟩ := h a
    refine ⟨b,hb,?_⟩
    rintro c d e hc rfl rfl
    exact hu e hc

lemma meaning_onto (r : QuotedTerm n) (R : Relation A) (hr : r.meaning S env = relationCode R) :
    (onto r).meaning S env ↔ ∀ b, ∃ a, (a,b) ∈ R := by
  simp [onto,hr,pairCode,atom_injective.eq_iff]

lemma meaning_preserves (r : QuotedTerm n) (R : Relation A) (hr : r.meaning S env = relationCode R) :
    (preserves r).meaning S env ↔ ∀ s a a' b b', (a,b) ∈ R → (a',b') ∈ R → S.rel s a a' = S.rel s b b' := by
  simp [preserves,hr,Bool.coe_iff_coe,and_imp,pairCode,atom_injective.eq_iff]
  aesop

lemma meaning_fixesBlocks (r : QuotedTerm n) (R : Relation A) (hr : r.meaning S env = relationCode R) :
    (fixesBlocks r).meaning S env ↔ ∀ u ∈ blocks S, ∀ a ∈ u, ∀ b, (a,b) ∈ R → b ∈ u := by
  simp [fixesBlocks,hr,stateCode,atom_injective.eq_iff,pairCode]
  aesop

lemma meaning_fixesState (x r : QuotedTerm n) (X : Finset A) (R : Relation A)
    (hx : x.meaning S env = stateCode X) (hr : r.meaning S env = relationCode R) :
    (fixesState x r).meaning S env ↔ ∀ a ∈ X, (a,a) ∈ R := by
  simp [fixesState,hx,hr,stateCode,atom_injective.eq_iff,pairCode]

lemma meaning_filter (x r : QuotedTerm n) (X : Finset A) (R : Relation A)
    (hx : x.meaning S env = stateCode X) (hr : r.meaning S env = relationCode R) :
    (filter x r).meaning S env ↔ RawFilter S X R := by
  rw [filter,meaning_and,meaning_and,meaning_and,meaning_and,
    meaning_functional S env r R hr,meaning_onto S env r R hr,
    meaning_preserves S env r R hr,meaning_fixesBlocks S env r R hr,
    meaning_fixesState S env x r X R hx hr]
  simp only [RawFilter,FunctionalOnto,and_assoc]

end QuotedFormula

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


namespace QuotedTerm
open RelationPools

section

variable {n : ℕ}

variable {A : Type} [Fintype A] (S : Input A) (env : Fin n → HF A)

lemma meaning_witnessRelations (B : ℕ) (valid : QuotedFormula n) (x C : QuotedTerm n)
    (X : Finset A) (cycles : Finset (Relation A))
    (hx : x.meaning S env = stateCode X)
    (hC : C.meaning S env = ofFinset (cycles.image relationCode)) :
    (witnessRelations B valid x C).meaning S env =
      ofFinset ((witnessPool B S (valid.meaning S env) (fun _ => cycles) X).image permutationGraph) := by
  have hcomp (l c : Relation A) :
      (composition (var (1 : Fin (n+2))) (var 0)).meaning S
        (Fin.cons (relationCode c) (Fin.cons (relationCode l) env)) = relationCode (compose l c) :=
    meaning_composition S _ _ _ _ _ rfl rfl
  have hf (l c : Relation A) :
      (QuotedFormula.filter x.up.up (composition (var (1 : Fin (n+2))) (var 0))).meaning S
        (Fin.cons (relationCode c) (Fin.cons (relationCode l) env)) ↔ RawFilter S X (compose l c) :=
    QuotedFormula.meaning_filter S _ _ _ _ _ (by simpa using hx) (hcomp l c)
  simp only [witnessRelations,meaning_cond,witnessPool]
  split_ifs with hv
  · simp only [meaning_cup,meaning_singleton,identity,localRelations,meaning_bind,
      meaning_up,hC,elements_ofFinset,comprehend,Hereditary.singleton]
    apply ofFinset_inj.mpr
    ext z
    simp only [Finset.mem_union,Finset.mem_singleton,Finset.mem_biUnion,Finset.mem_image,
      Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert]
    constructor
    · rintro (hz | ⟨l,⟨r,hr,rfl⟩,c,⟨⟨t,ht,rfl⟩,hf'⟩,hz⟩)
      · exact ⟨1,Or.inl rfl,(hz.trans (relationCode_graph 1)).symm⟩
      · have hh := (hf r t).mp hf'
        obtain ⟨g,hg,hfg⟩ := (rawFilter_iff S X _).mp hh
        refine ⟨g,Or.inr ⟨hfg,r,hr,t,ht,hg⟩,?_⟩
        rw [hcomp r t,hg,relationCode_graph] at hz
        exact hz
    · rintro ⟨g,(rfl | ⟨hfg,r,hr,t,ht,hg⟩),rfl⟩
      · exact Or.inl (relationCode_graph 1).symm
      · refine Or.inr ⟨relationCode r,⟨r,hr,rfl⟩,relationCode t,⟨⟨t,ht,rfl⟩,?_⟩,?_⟩
        · exact (hf r t).mpr ((rawFilter_iff S X _).mpr ⟨g,hg,hfg⟩)
        · rw [hcomp r t,hg,relationCode_graph]
  · simp only [meaning_singleton,identity,relationCode_graph,Finset.image_singleton,Hereditary.singleton]

lemma meaning_guardedChoice (D M : QuotedTerm n) (P : Selection A) (X : Finset A)
    (hD : D.meaning S env = stateCode (P.candidates X))
    (hM : M.meaning S env = ofFinset ((P.witnesses X).image permutationGraph)) :
    (guardedChoice D M).meaning S env = ofFinset ((P.choices X).image choiceCode) := by
  have hne : stateCode (P.candidates X) ≠ emptyHF ↔ (P.candidates X).Nonempty := by
    change stateCode (P.candidates X) ≠ stateCode ∅ ↔ _
    simp only [ne_eq,stateCode_inj,Finset.nonempty_iff_ne_empty]
  have hm (a b : A) :
      (∃ g ∈ (P.witnesses X), Hereditary.pair (atom a) (atom b) ∈ elements (permutationGraph g)) ↔
      ∃ g ∈ P.witnesses X, g a = b := by
    simp only [← relationCode_graph,pair_mem_relationCode,mem_graph]
  simp only [guardedChoice,meaning_cond,QuotedFormula.meaning_and,QuotedFormula.meaning_neg,
    QuotedFormula.meaning_eq,hD,meaning_empty,hne,QuotedFormula.meaning_allIn,
    all_stateCode,meaning_up,QuotedFormula.meaning_existsIn,hM,elements_ofFinset,
    QuotedFormula.meaning_link,meaning_var,Fin.cons_zero,Fin.cons_one,fin_cons_two,
    Finset.mem_image,exists_exists_and_eq_and,hm]
  unfold Selection.choices Selection.TransitiveAt
  split_ifs
  · simp only [stateCode,Finset.image_image,Function.comp_def,choiceCode]
  · simp only [meaning_singleton,meaning_empty,Finset.image_singleton,choiceCode,ordinal]
    rfl

end

variable {n : ℕ} {A : Type} [Fintype A] (S : Input A) (env : Fin n → HF A)

lemma meaning_selectionStep (x y : QuotedTerm n) (X : Finset A) (c : Option A)
    (hx : x.meaning S env = stateCode X) (hy : y.meaning S env = choiceCode c)
    (hc : ∀ a, c = some a → a ∈ WitnessedChoice.edgeAtoms S) :
    (selectionStep x y).meaning S env = stateCode (Selection.advance X c) := by
  have hne (a : A) : (emptyHF : HF A) ≠ atom a := by
    intro h
    have hh := congrArg isSet h
    simp [emptyHF] at hh
  simp only [selectionStep,meaning_cup,hx,meaning_inter,meaning_double,meaning_unique,hy,
    meaning_edgeAtoms,elements_ofFinset]
  cases c with
  | none =>
    simp only [choiceCode,show ordinal (A := A) 0 = emptyHF from rfl,uniqueHF_empty,Hereditary.double,elements_ofFinset,
      stateCode,Selection.advance]
    apply ofFinset_inj.mpr
    ext z
    simp only [Finset.mem_union,Finset.mem_inter,Finset.mem_insert,Finset.mem_singleton,
      Finset.mem_image]
    constructor
    · rintro (h | ⟨(rfl|rfl),a,ha,he⟩)
      · exact h
      all_goals exact (hne a he.symm).elim
    · exact Or.inl
  | some a =>
    have ha := hc a rfl
    simp only [choiceCode,uniqueHF_atom,Hereditary.double,elements_ofFinset,stateCode,
      Selection.advance,Finset.image_insert]
    apply ofFinset_inj.mpr
    ext z
    simp only [Finset.mem_union,Finset.mem_inter,Finset.mem_insert,Finset.mem_singleton,
      Finset.mem_image]
    constructor
    · rintro (h | ⟨(rfl|rfl),b,hb,he⟩)
      · exact Or.inr h
      · exact Or.inl rfl
      · exact (hne b he.symm).elim
    · rintro (rfl|h)
      · exact Or.inr ⟨Or.inl rfl,a,ha,rfl⟩
      · exact Or.inl h

end QuotedTerm


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

@[simp] lemma value_letIn (t : CPTTerm n) (b : CPTFormula (n+1)) (S : Input A)
    (p : Polynomial ℝ) (env : Fin n → HF A) :
    (letIn t b).value S p env = b.value S p (Fin.cons (t.value S p env) env) := by
  apply value_eq
  exact Formula.eval_letIn S p t.code b.code env (t.eval_value S p env) b.count (b.eval_value S p _)

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

lemma collect_on {A : Type} (r : HF A) (guard : HF A → Result Bool) (body : HF A → Result (HF A))
    (g : HF A → Bool) (b : HF A → HF A)
    (hg : ∀ x ∈ elements r, guard x = some (g x))
    (hb : ∀ x ∈ elements r, g x = true → body x = some (b x)) :
    collect r guard body = some (ofFinset (((elements r).filter (fun x => g x = true)).image b)) := by
  have hgood : (∀ x ∈ elements r, (guard x).isSome) ∧
      (∀ x ∈ elements r, guard x = some true → (body x).isSome) := by
    constructor
    · intro x hx; rw [hg x hx]; simp
    · intro x hx ht
      rw [hg x hx] at ht
      rw [hb x hx (Option.some.inj ht)]
      simp
  rw [collect,ite_eq_left hgood]
  apply congrArg some
  apply ofFinset_inj.mpr
  have hf : (elements r).filter (fun x => guard x = some true) =
      (elements r).filter (fun x => g x = true) := Finset.filter_congr (by
        intro x hx
        rw [hg x hx,Option.some.injEq])
  rw [hf]
  apply Finset.image_congr
  intro x hx
  obtain ⟨hx,ht⟩ := Finset.mem_filter.mp hx
  change (body x).getD emptyHF = b x
  rw [hb x hx ht,Option.getD_some]

lemma Formula.eval_existsIn_on {A : Type} [Fintype A] (S : Input A) (p : Polynomial ℝ) {n : ℕ}
    (r : Term n) (a : Formula (n+1)) (env : Fin n → HF A)
    {rv : HF A} {av : HF A → Bool} (hr : r.eval S p env = some rv)
    (ha : ∀ x ∈ elements rv, a.eval S p (Fin.cons x env) = some (av x)) :
    (Formula.existsIn r a).eval S p env = some (decide (∃ x ∈ elements rv, av x = true)) := by
  simp only [Formula.existsIn,Formula.eval,Term.eval,hr,Option.bind_some]
  rw [collect_on rv _ _ av (fun _ => emptyHF) ha (by intros; rfl)]
  simp only [lift₂,Option.bind_some,Option.map_some,Option.some.injEq]
  have he : ofFinset (((elements rv).filter (fun x => av x = true)).image (fun _ => (emptyHF : HF A))) = emptyHF ↔
      ¬ ∃ x ∈ elements rv, av x = true := by
    rw [emptyHF,ofFinset_inj,Finset.image_eq_empty]
    simp
  simp only [he,decide_not,Bool.not_not]


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

namespace GuardedProgram

variable (G : GuardedProgram)

variable (S : Input A) (p : Polynomial ℝ) (α : HF A)

lemma candidates_eq (x : Finset A) : (G.selection S p α).candidates x = G.candidateSet S p α x := by
  simp [selection,guardedSelection]

lemma candidate_edge (x : Finset A) {a : A} (h : a ∈ (G.selection S p α).candidates x) :
    a ∈ WitnessedChoice.edgeAtoms S := by
  rw [G.candidates_eq] at h
  exact (Finset.mem_inter.mp h).2

lemma witnesses_value (x : Finset A) :
    G.witnesses.value S p (Fin.cons (stateCode x) (Fin.cons α Fin.elim0)) =
      ofFinset (((G.selection S p α).witnesses x).image permutationGraph) := by
  simp only [witnesses,CPTTerm.value_letIn,CPTTerm.value_normalizeRelations,CPTTerm.value_quoted]
  convert QuotedTerm.meaning_witnessRelations S
    (Fin.cons (ofFinset ((G.cycleSet S p α x).image relationCode))
      (Fin.cons (stateCode x) (Fin.cons α Fin.elim0)))
    G.localBound .truth (.var 1) (.var 0) x (G.cycleSet S p α x) rfl rfl using 1 <;>
    simp [cycleSet,selection,guardedSelection,QuotedFormula.truth,witnessPool]

lemma choice_value (x : Finset A) :
    G.choice.value S p (Fin.cons (stateCode x) (Fin.cons α Fin.elim0)) =
      ofFinset (((G.selection S p α).choices x).image choiceCode) := by
  simp only [choice,CPTTerm.value_letIn,CPTTerm.value_normalizeCandidates,CPTTerm.value_up,
    CPTTerm.value_quoted,G.witnesses_value]
  apply QuotedTerm.meaning_guardedChoice S _ (.var 1) (.var 0) (G.selection S p α) x
  · simp only [QuotedTerm.meaning_var,Fin.cons_one]
    rw [G.candidates_eq]
    rfl
  · rfl

lemma realizes : Realizes (G.selection S p α)
    (fun x y => step.code.eval S p (Fin.cons y (Fin.cons x (Fin.cons α Fin.elim0))))
    (fun x => G.choice.code.eval S p (Fin.cons x (Fin.cons α Fin.elim0)))
    (fun z x => G.witness.code.eval S p (Fin.cons x (Fin.cons z (Fin.cons α Fin.elim0)))) := by
  constructor
  · intro x
    rw [G.choice.eval_value,G.choice_value]
  · intro x c hc
    rw [step.correct]
    apply congrArg some
    apply QuotedTerm.meaning_selectionStep S _ (.var 1) (.var 0) x c rfl rfl
    intro a ha
    subst c
    exact G.candidate_edge S p α x (Selection.some_mem_choices.mp hc).1
  · intro z x
    rw [G.witness.eval_value]
    change some ((G.witnesses.rename ![0,2]).value S p _) = _
    rw [CPTTerm.value_rename]
    have he : (Fin.cons (stateCode x) (Fin.cons (stateCode z) (Fin.cons α Fin.elim0))) ∘ ![0,2] =
        Fin.cons (stateCode x) (Fin.cons α Fin.elim0) := by
      funext i; fin_cases i <;> rfl
    rw [he,G.witnesses_value]

end GuardedProgram

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



namespace WitnessedChoice.TreeTest

noncomputable section

open Classical

namespace RootedTree

variable {V A : Type} (T : RootedTree V)

theorem adj_symm {v w : V} (h : T.Adj v w) : T.Adj w v := h.symm

theorem parent_adj (v : V) (h : v ≠ T.root) : T.Adj v (T.parent v) := Or.inl ⟨h,rfl⟩

variable (B : V → Finset A) (rel : V → V → A → A → Prop)
  (hroot : (B T.root).Nonempty)
  (hext : ∀ v, v ≠ T.root → ∀ a ∈ B (T.parent v), ∃ b ∈ B v, rel (T.parent v) v a b)

lemma label_parent (v : V) (hv : v ≠ T.root) :
    rel (T.parent v) v (T.label B rel hroot hext (T.parent v)).val
      (T.label B rel hroot hext v).val := by
  conv_rhs => rw [label]
  simp only [dite_eq_right hv]
  exact (hext v hv _ (T.label B rel hroot hext (T.parent v)).property).choose_spec.2

theorem exists_labels
    (nonempty : ∀ v, (B v).Nonempty)
    (support : ∀ v w, T.Adj v w → ∀ a ∈ B v, ∃ b ∈ B w, rel v w a b)
    (symm : ∀ v w a b, rel v w a b → rel w v b a) :
    ∃ t : V → A, (∀ v, t v ∈ B v) ∧ ∀ v w, T.Adj v w → rel v w (t v) (t w) := by
  let he := fun v hv a ha => support (T.parent v) v (T.adj_symm (T.parent_adj v hv)) a ha
  let t := fun v => (T.label B rel (nonempty T.root) he v).val
  refine ⟨t, fun v => (T.label B rel (nonempty T.root) he v).property, ?_⟩
  intro v w h
  rcases h with ⟨hv, rfl⟩ | ⟨hw, rfl⟩
  · exact symm _ _ _ _ (T.label_parent B rel (nonempty T.root) he v hv)
  · exact T.label_parent B rel (nonempty T.root) he w hw

end RootedTree

namespace Problem

variable {V A : Type} (P : Problem V A)

lemma le_update (S : Finset A) : S ⊆ P.update S := Finset.subset_union_left

lemma update_subset {S : Finset A} (h : S ⊆ P.configs) : P.update S ⊆ P.configs :=
  Finset.union_subset h (Finset.filter_subset _ _)

lemma run_subset (k : ℕ) : P.run k ⊆ P.configs := by
  induction k with
  | zero => exact Finset.empty_subset _
  | succ k ih => exact P.update_subset ih

lemma run_step (k : ℕ) : P.run k ⊆ P.run (k+1) := P.le_update _

lemma run_comparison {k : ℕ} (h : ∀ i < k, P.run i ≠ P.run (i+1)) : k ≤ (P.run k).card := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    have hk := h k (by omega)
    have hc : (P.run k).card < (P.run (k+1)).card :=
      Finset.card_lt_card ((Finset.ssubset_iff_subset_ne).mpr ⟨P.run_step k, hk⟩)
    have hi := ih (fun i hi => h i (by omega))
    omega

lemma exists_stationary : ∃ t ≤ P.configs.card, P.run t = P.run (t+1) := by
  by_contra hn
  push Not at hn
  have hstrict : ∀ i < P.configs.card + 1, P.run i ≠ P.run (i+1) := fun i hi => hn i (by omega)
  have hc := P.run_comparison hstrict
  have hb := Finset.card_le_card (P.run_subset (P.configs.card+1))
  omega

lemma run_stationary_after {t : ℕ} (ht : P.run t = P.run (t+1)) :
    ∀ k, t ≤ k → P.run k = P.run t := by
  intro k hk
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction l with
  | zero => simp
  | succ l ih =>
    change P.update (P.run (t+l)) = P.run t
    rw [ih (by omega)]
    exact ht.symm

lemma deleted_fixed : P.update P.deleted = P.deleted := by
  obtain ⟨t, ht, he⟩ := P.exists_stationary
  have h0 := P.run_stationary_after he P.configs.card ht
  have h1 := P.run_stationary_after he (P.configs.card+1) (by omega)
  exact h1.trans h0.symm

lemma mem_survivors {a : A} {v : V} : a ∈ P.survivors v ↔ a ∈ P.block v ∧ a ∉ P.deleted := by
  simp only [survivors, Finset.mem_filter]

lemma survival_allowed {v : V} {a : A} (ha : a ∈ P.survivors v) : P.allowed a := by
  obtain ⟨ha, hn⟩ := P.mem_survivors.mp ha
  by_contra he
  apply hn
  rw [← P.deleted_fixed]
  apply Finset.mem_union_right
  exact Finset.mem_filter.mpr ⟨P.block_subset v ha, Or.inl he⟩

lemma survival_support {v w : V} (hw : P.tree.Adj v w) {a : A} (ha : a ∈ P.survivors v) :
    ∃ b ∈ P.survivors w, P.compatible v w a b := by
  obtain ⟨ha, hn⟩ := P.mem_survivors.mp ha
  by_contra he
  have he' : ¬ ∃ b ∈ P.block w, b ∉ P.deleted ∧ P.compatible v w a b := by
    rintro ⟨b, hb, hnd, hc⟩
    exact he ⟨b, P.mem_survivors.mpr ⟨hb, hnd⟩, hc⟩
  apply hn
  rw [← P.deleted_fixed]
  apply Finset.mem_union_right
  exact Finset.mem_filter.mpr ⟨P.block_subset v ha, Or.inr ⟨v, ha, w, hw, he'⟩⟩

lemma solution_survives {t : V → A} (ht : P.Solution t) : ∀ k v, t v ∉ P.run k := by
  intro k
  induction k with
  | zero => simp [run]
  | succ k ih =>
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact ih v hv
    · obtain ⟨_, hdel⟩ := Finset.mem_filter.mp hv
      rcases hdel with hna | ⟨v', hv', w, hw, hns⟩
      · exact hna (ht.1 v).2
      · have hh : v' = v := P.block_unique v' v (t v) hv' (ht.1 v).1
        subst v'
        exact hns ⟨t w, (ht.1 w).1, ih w, ht.2 v w hw⟩

theorem all_survive_iff_solution :
    (∀ v, (P.survivors v).Nonempty) ↔ ∃ t, P.Solution t := by
  constructor
  · intro h
    obtain ⟨t, ht, hcomp⟩ := P.tree.exists_labels P.survivors P.compatible h
      (fun _ _ hw _ ha => P.survival_support hw ha) P.compatible_symm
    exact ⟨t, ⟨fun v => ⟨(P.mem_survivors.mp (ht v)).1, P.survival_allowed (ht v)⟩, hcomp⟩⟩
  · rintro ⟨t, ht⟩ v
    exact ⟨t v, P.mem_survivors.mpr ⟨(ht.1 v).1, P.solution_survives ht _ v⟩⟩

end Problem

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

lemma boundary_solve (r : Vertex n → Scalar) (hr : ∑ v, r v = 0) :
    boundary (P.solve r) = r := by
  simp only [solve,map_sum,map_smul,P.boundary_route,smul_sub,Finset.sum_sub_distrib]
  rw [← Finset.sum_smul,hr,zero_smul,sub_zero]
  funext v
  simp [Pi.single_apply]

lemma solve_zero_off_tree (r : Vertex n → Scalar) {e : Edge n} (he : e ∉ P.treeEdges) :
    P.solve r e = 0 := by
  simp only [solve,Finset.sum_apply,Pi.smul_apply,P.route_zero_off_tree he,smul_zero,Finset.sum_const_zero]

lemma extend_scalars (b : Vertex n → Scalar) (hb : ∑ v, b v = 0) (z : Edge n → Scalar) :
    ∃ w : Edge n → Scalar, boundary w = b ∧ ∀ e, e ∉ P.treeEdges → w e = z e := by
  let r := b - boundary z
  have hr : ∑ v, r v = 0 := by
    simp only [r,Pi.sub_apply,Finset.sum_sub_distrib,hb,sum_boundary,sub_self]
  refine ⟨z + P.solve r, ?_, ?_⟩
  · rw [map_add,P.boundary_solve r hr]
    dsimp [r]
    abel
  · intro e he
    simp only [Pi.add_apply,P.solve_zero_off_tree r he,add_zero]

end ParentEdges

end





noncomputable section

open Classical Support WitnessedChoice.TreeTest

variable {n : ℕ}

lemma selectedVectors_preserves {x : Finset (Σ e : Edge n, LocalGroup e)}
    (hx : ConsistentSelection x) {r : Σ e : Edge n, LocalGroup e} (hr : r ∈ x)
    (f : EdgeFaces r.1) : selectedVectors x f.val = r.2.face f := by
  have h : ∃ s ∈ x, cycle f.val s.1 ≠ 0 := ⟨r,hr,f.property⟩
  rw [selectedVectors,dite_eq_left h]
  exact hx.2 h.choose h.choose_spec.1 r hr f.val h.choose_spec.2 f.property

lemma selectedScalars_preserves {x : Finset (Σ e : Edge n, LocalGroup e)}
    (hx : ConsistentSelection x) {r : Σ e : Edge n, LocalGroup e} (hr : r ∈ x) :
    selectedScalars x r.1 = r.2.flow := by
  have h : ∃ s ∈ x, s.1 = r.1 := ⟨r,hr,rfl⟩
  rw [selectedScalars,dite_eq_left h,hx.1 h.choose h.choose_spec.1 r hr h.choose_spec.2]

theorem extend_consistent_selection {T : RootedTree (Vertex n)} (P : ParentEdges T)
    (b : Vertex n → Scalar) (hb : ∑ v, b v = 0)
    (x : Finset (Σ e : Edge n, LocalGroup e)) (hx : ConsistentSelection x)
    (hoff : ∀ r ∈ x, r.1 ∉ P.treeEdges) :
    ∃ (s : (e : Edge n) → LocalGroup e) (t : (v : Vertex n) → Configuration b v),
      (∀ r ∈ x, s r.1 = r.2) ∧ ∀ v (e : IncidentEdges v), (t v).state e = s e.val := by
  obtain ⟨z,hz,hkeep⟩ := P.extend_scalars b hb (selectedScalars x)
  refine ⟨globalStates (selectedVectors x) z,globalConfiguration b (selectedVectors x) z hz,?_,?_⟩
  · intro r hr
    apply H.ext
    · funext f
      exact selectedVectors_preserves hx hr f
    · exact (hkeep r.1 (hoff r hr)).trans (selectedScalars_preserves hx hr)
  · intro v e
    rfl

theorem total_charge_of_global_configurations (b : Vertex n → Scalar)
    (s : (e : Edge n) → LocalGroup e) (t : (v : Vertex n) → Configuration b v)
    (h : ∀ v (e : IncidentEdges v), (t v).state e = s e.val) : ∑ v, b v = 0 := by
  have hb : boundary (fun e => (s e).flow) = b := by
    funext v
    rw [← sum_incident]
    exact (show divergence (fun e : IncidentEdges v => s e.val) = b v by
      have hh : (t v).state = fun e : IncidentEdges v => s e.val := funext (h v)
      rw [← hh]
      exact (t v).charge)
  rw [← hb]
  exact sum_boundary _

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

lemma cornerAnchors_resolve (u v : Vertex n)
    (h : ∀ i : Fin 4, (boxGraph n).dist (cornerAnchors n i) u =
      (boxGraph n).dist (cornerAnchors n i) v) : u = v := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  simp only [boxGraph_dist] at h0 h1 h2 h3
  simp only [cornerAnchors, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_last,
    Nat.dist_zero_left] at h0 h1 h2 h3
  simp only [Nat.dist_eq_sub_of_le_right (Nat.le_of_lt_succ u.1.isLt),
    Nat.dist_eq_sub_of_le_right (Nat.le_of_lt_succ u.2.1.isLt),
    Nat.dist_eq_sub_of_le_right (Nat.le_of_lt_succ u.2.2.isLt),
    Nat.dist_eq_sub_of_le_right (Nat.le_of_lt_succ v.1.isLt),
    Nat.dist_eq_sub_of_le_right (Nat.le_of_lt_succ v.2.1.isLt),
    Nat.dist_eq_sub_of_le_right (Nat.le_of_lt_succ v.2.2.isLt)] at h1 h2 h3
  apply Prod.ext
  · apply Fin.ext; omega
  · apply Prod.ext
    · apply Fin.ext; omega
    · apply Fin.ext; omega

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

lemma meaning_resolving (S : Input A) (env : Fin k → HF A)
    (ats VT R : QuotedTerm k) (code : V → HF A) (hc : Function.Injective code)
    (G : SimpleGraph V) (hG : G.Connected) (α : Fin 4 → V)
    (hα : ats.meaning S env = tupleCode (List.ofFn (code ∘ α)))
    (hV : VT.meaning S env = ofFinset (Finset.univ.image code))
    (hR : R.meaning S env = ofFinset ((BFS.closure G (Fintype.card A)).image (distanceCode code)))
    (hcard : Fintype.card V ≤ Fintype.card A) :
    (resolving ats VT R).meaning S env ↔ AnchoredTree.Resolving G α := by
  simp only [resolving,meaning_allIn,meaning_imp,meaning_allFin,meaning_eq,meaning_var,
    QuotedTerm.meaning_up,hV,elements_ofFinset,Finset.mem_image,Finset.mem_univ,true_and,
    forall_exists_index,forall_apply_eq_imp_iff,Fin.cons_zero,Fin.cons_one]
  have hd (u v : V) (i : Fin 4) (w : V) (wt : QuotedTerm (k+2))
      (hw : wt.meaning S (Fin.cons (code v) (Fin.cons (code u) env)) = code w) :
      (distanceAt R.up.up (ats.up.up.component i.val) wt).meaning S
        (Fin.cons (code v) (Fin.cons (code u) env)) = ordinal (G.dist (α i) w) := by
    apply meaning_distanceAt S _ _ _ _ code hc G hG _ _ _ _ hw hcard
    · simpa only [QuotedTerm.meaning_up] using hR
    · apply meaning_component_ofFn S _ _ (code ∘ α) _ i
      simpa only [QuotedTerm.meaning_up] using hα
  have hd₁ (u v : V) (i : Fin 4) := hd u v i u (var 1) (by simp)
  have hd₀ (u v : V) (i : Fin 4) := hd u v i v (var 0) (by simp)
  simp only [hd₁,hd₀,ordinal_injective.eq_iff,hc.eq_iff]
  constructor
  · intro h u v huv
    exact h u v (fun i => congrFun huv i)
  · intro h u v huv
    apply h
    exact funext huv

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





noncomputable section

open Classical WitnessedChoice WitnessedChoice.TreeTest

variable {n : ℕ}

namespace ParentEdges

variable {T : RootedTree (Vertex n)} (P : ParentEdges T)

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

end ParentEdges

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

lemma leastEdges_empty_iff (α : Fin 4 → Vertex n) (D : Finset (Edge n)) :
    leastEdges α D = ∅ ↔ D=∅ := by
  constructor
  · intro h
    by_contra hn
    have hD := Finset.nonempty_iff_ne_empty.mpr hn
    let K := D.image (edgeKey α)
    have hK : K.Nonempty := hD.image _
    obtain ⟨e,he,hek⟩ := Finset.mem_image.mp (Finset.min'_mem K hK)
    have hemin : e ∈ leastEdges α D := by
      refine Finset.mem_filter.mpr ⟨he,?_⟩
      intro f hf hlt
      have hm := Finset.min'_le K (edgeKey α f) (Finset.mem_image.mpr ⟨f,hf,rfl⟩)
      rw [←hek] at hm
      exact (not_lt_of_ge hm) hlt
    rw [h] at hemin
    exact Finset.notMem_empty _ hemin
  · rintro rfl
    simp [leastEdges]

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

lemma gridCandidates_fresh {α : Fin 4 → Vertex n} {T : Finset (Edge n)}
    {x : Finset (Σ e : Edge n, LocalGroup e)} {r : Σ e : Edge n, LocalGroup e}
    (hr : r ∈ gridCandidates α T x) : r ∉ x := fun hx => (candidate_new_edge hr).2 r hx rfl

lemma consistent_empty : ConsistentSelection (∅ : Finset (Σ e : Edge n, LocalGroup e)) := by
  simp [ConsistentSelection]

lemma consistent_insert {x : Finset (Σ e : Edge n, LocalGroup e)}
    (hx : ConsistentSelection x) {e : Edge n} {s : LocalGroup e}
    (hnew : missingEdge x e) (hs : AcceptsFaces x e s) : ConsistentSelection (insert ⟨e,s⟩ x) := by
  constructor
  · intro r hr t ht heq
    rcases Finset.mem_insert.mp hr with rfl | hr <;>
      rcases Finset.mem_insert.mp ht with rfl | ht
    · rfl
    · exact False.elim (hnew t ht heq.symm)
    · exact False.elim (hnew r hr heq)
    · exact hx.1 r hr t ht heq
  · intro r hr t ht f hf ht'
    rcases Finset.mem_insert.mp hr with rfl | hr <;>
      rcases Finset.mem_insert.mp ht with rfl | ht
    · rfl
    · exact hs t ht f hf ht'
    · exact (hs r hr f ht' hf).symm
    · exact hx.2 r hr t ht f hf ht'

lemma selectedVectors_accepts {x : Finset (Σ e : Edge n, LocalGroup e)}
    (hx : ConsistentSelection x) (e : Edge n) :
    AcceptsFaces x e (globalStates (selectedVectors x) 0 e) := by
  intro r hr f he hf
  exact selectedVectors_preserves hx hr ⟨f,hf⟩

lemma gridCandidates_empty_iff (α : Fin 4 → Vertex n) (T : Finset (Edge n))
    (x : Finset (Σ e : Edge n, LocalGroup e)) (hx : ConsistentSelection x) :
    gridCandidates α T x = ∅ ↔ remainingEdges T x = ∅ := by
  rw [←leastEdges_empty_iff α (remainingEdges T x)]
  constructor
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    have hm := (mem_gridCandidates α T x ⟨e,globalStates (selectedVectors x) 0 e⟩).mpr
      ⟨he,selectedVectors_accepts hx e⟩
    rw [h] at hm
    exact Finset.notMem_empty _ hm
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro r hr
    have hm := (mem_gridCandidates α T x r).mp hr |>.1
    rw [h] at hm
    exact Finset.notMem_empty _ hm

lemma remaining_empty_iff (T : Finset (Edge n)) (x : Finset (Σ e : Edge n, LocalGroup e)) :
    remainingEdges T x = ∅ ↔ ∀ e, e ∉ T → ∃ r ∈ x, r.1 = e := by
  simp only [Finset.eq_empty_iff_forall_notMem,remainingEdges,Finset.mem_filter,
    Finset.mem_sdiff,Finset.mem_univ,true_and,not_and,missingEdge,not_forall,not_not]
  constructor <;> intro H e he
  · obtain ⟨r,hr,hre⟩ := H e he
    exact ⟨r,hr,hre⟩
  · obtain ⟨r,hr,hre⟩ := H e he
    exact ⟨r,hr,hre⟩

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.TreeTest

variable {n : ℕ} {b : Vertex n → Scalar}

lemma edgeState_injective : Function.Injective (edgeState (b := b)) :=
  fun _ _ h => (Finset.image_inj Sum.inl_injective).mp h

lemma mem_edgeState (x : Finset (Σ e : Edge n, LocalGroup e)) (a : Atom b) :
    a ∈ edgeState x ↔ ∃ r ∈ x, Sum.inl r = a := Finset.mem_image

namespace ParentEdges

variable {T : RootedTree (Vertex n)} (P : ParentEdges T)

lemma prefix_invariant (α : Fin 4 → Vertex n) (S : Selection (Atom b))
    (hD : ∀ x, S.candidates (edgeState x) = edgeState (gridCandidates α P.treeEdges x))
    {B : ℕ → Finset (Atom b)} {c : ℕ → Option (Atom b)} {k : ℕ} (hpath : S.Prefix B c k) :
    ∀ i ≤ k, ∃ x : Finset (Σ e : Edge n, LocalGroup e),
      B i = edgeState x ∧ ConsistentSelection x ∧ ∀ r ∈ x, r.1 ∉ P.treeEdges := by
  intro i
  induction i with
  | zero =>
    intro _
    exact ⟨∅,hpath.1.trans edgeState_empty.symm,consistent_empty,by simp⟩
  | succ i ih =>
    intro hi
    obtain ⟨x,hx,hcons,hoff⟩ := ih (by omega)
    obtain ⟨hc,hstep⟩ := hpath.2 i (by omega)
    cases hci : c i with
    | none =>
      rw [hci] at hstep
      exact ⟨x,hstep.trans hx,hcons,hoff⟩
    | some a =>
      rw [hci] at hc hstep
      have ha := (Selection.some_mem_choices.mp hc).1
      rw [hx,hD] at ha
      obtain ⟨r,hr,rfl⟩ := (mem_edgeState _ a).mp ha
      obtain ⟨hne,hnew⟩ := candidate_new_edge hr
      have hh : B (i+1) = edgeState (insert r x) := by
        rw [hstep,hx,Selection.advance,edgeState_insert]
      refine ⟨insert r x,hh,consistent_insert hcons hnew ((mem_gridCandidates _ _ _ _).mp hr).2,?_⟩
      intro s hs
      rcases Finset.mem_insert.mp hs with rfl | hs
      · exact hne
      · exact hoff s hs

lemma terminal_complete (α : Fin 4 → Vertex n) (S : Selection (Atom b))
    (hD : ∀ x, S.candidates (edgeState x) = edgeState (gridCandidates α P.treeEdges x))
    (hTrans : ∀ x, ConsistentSelection x → (∀ r ∈ x, r.1 ∉ P.treeEdges) →
      S.TransitiveAt (edgeState x))
    {B : ℕ → Finset (Atom b)} {c : ℕ → Option (Atom b)} {t : ℕ} (hpath : S.FirstStabilization B c t) :
    ∃ x : Finset (Σ e : Edge n, LocalGroup e), B t = edgeState x ∧ ConsistentSelection x ∧
      (∀ r ∈ x, r.1 ∉ P.treeEdges) ∧ ∀ e, e ∉ P.treeEdges → ∃ r ∈ x, r.1 = e := by
  obtain ⟨x,hx,hcons,hoff⟩ := P.prefix_invariant α S hD hpath.1 t (by omega)
  refine ⟨x,hx,hcons,hoff,(remaining_empty_iff P.treeEdges x).mp ?_⟩
  apply (gridCandidates_empty_iff α P.treeEdges x hcons).mp
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro r hr
  have hne : (S.candidates (B t)).Nonempty := by
    rw [hx,hD]
    exact ⟨.inl r,(mem_edgeState _ _).mpr ⟨r,hr,rfl⟩⟩
  have ht : S.TransitiveAt (B t) := hx.symm ▸ hTrans x hcons hoff
  have hc := (hpath.1.2 t (by omega)).1
  have hs := (hpath.1.2 t (by omega)).2
  cases hci : c t with
  | none =>
    rw [hci] at hc
    exact (Selection.none_mem_choices.mp hc) ⟨hne,ht⟩
  | some a =>
    rw [hci] at hc hs
    have ha := (Selection.some_mem_choices.mp hc).1
    rw [hx,hD] at ha
    obtain ⟨s,hsc,rfl⟩ := (mem_edgeState _ a).mp ha
    simp only [Selection.advance] at hs
    have heq : insert s x = x := by
      apply edgeState_injective
      rw [edgeState_insert,←hx,←hs,←hpath.2.2]
    have hmem : s ∈ x := by rw [←heq]; exact Finset.mem_insert_self _ _
    exact gridCandidates_fresh hsc hmem

end ParentEdges

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

lemma edgeAtoms_grid : WitnessedChoice.edgeAtoms (atomInput b) =
    (Finset.univ : Finset (Σ e : Edge n, LocalGroup e)).image Sum.inl := by
  ext a
  simp only [WitnessedChoice.edgeAtoms,Finset.mem_filter,Finset.mem_univ,true_and,
    atomInput,decide_eq_true_eq,Finset.mem_image]
  constructor
  · intro h
    cases h with | ed e c => exact ⟨⟨e,c⟩,rfl⟩
  · rintro ⟨⟨e,c⟩,rfl⟩
    exact .ed e c

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

open Classical WitnessedChoice.TreeTest

variable {n : ℕ} {b : Vertex n → Scalar}

namespace ParentEdges

variable {T : RootedTree (Vertex n)} (P : ParentEdges T)

lemma solution_configs (x : Finset (Σ e : Edge n, LocalGroup e))
    (ht : ∃ t, (P.testProblem (b := b) x).Solution t) :
    ∃ t : (v : Vertex n) → Configuration b v,
      (∀ v, P.allowedConfig x ⟨v,t v⟩) ∧
      ∀ v w, T.Adj v w → P.configCompatibility ⟨v,t v⟩ ⟨w,t w⟩ := by
  obtain ⟨t,ht⟩ := ht
  have hv (v : Vertex n) : (t v).1 = v := (mem_configBlock v _).mp (ht.1 v).1
  let tt (v : Vertex n) : Configuration b v := (hv v) ▸ (t v).2
  have he (v : Vertex n) : (⟨v,tt v⟩ : ConfigAtom b) = t v := by
    have transport_pair {w : Vertex n} (a : Configuration b w) (h : w = v) :
        (⟨v,h ▸ a⟩ : ConfigAtom b) = ⟨w,a⟩ := by cases h; rfl
    exact transport_pair _ (hv v)
  refine ⟨tt,?_,?_⟩
  · intro v
    rw [he]
    exact (ht.1 v).2
  · intro v w hadj
    rw [he,he]
    exact ht.2 v w hadj

lemma exists_globals_of_solution (x : Finset (Σ e : Edge n, LocalGroup e))
    (hx : ∀ r ∈ x, ∀ s ∈ x, r.1 = s.1 → r = s)
    (ht : ∃ t, (P.testProblem (b := b) x).Solution t) :
    ∃ (s : (e : Edge n) → LocalGroup e) (t : (v : Vertex n) → Configuration b v),
      ∀ v (e : IncidentEdges v), (t v).state e = s e.val := by
  obtain ⟨t,hta,htc⟩ := P.solution_configs x ht
  let s (e : Edge n) := (t (head e)).state ⟨e,Or.inl rfl⟩
  refine ⟨s,t,?_⟩
  rintro v ⟨e,hi⟩
  rcases hi with hv | hv
  · subst v
    rfl
  · subst v
    by_cases he : e ∈ P.treeEdges
    · have ha : (edgeGraph P.treeEdges).Adj (tail e) (head e) :=
        ⟨e,he,Or.inl ⟨rfl,rfl⟩⟩
      exact htc _ _ ((P.graph_adj _ _).mp ha) e he (Or.inr rfl) (Or.inl rfl)
    · have h₁ := hta (tail e) e he (Or.inr rfl)
      have h₂ := hta (head e) e he (Or.inl rfl)
      have hh := hx _ h₁ _ h₂ rfl
      exact eq_of_heq (Sigma.mk.inj hh).2

lemma test_solution_of_zero (b : Vertex n → Scalar) (hb : ∑ v, b v = 0)
    (x : Finset (Σ e : Edge n, LocalGroup e)) (hx : ConsistentSelection x)
    (hoff : ∀ r ∈ x, r.1 ∉ P.treeEdges)
    (hcomplete : ∀ e, e ∉ P.treeEdges → ∃ r ∈ x, r.1 = e) :
    ∃ t, (P.testProblem (b := b) x).Solution t := by
  obtain ⟨s,t,hs,ht⟩ := extend_consistent_selection P b hb x hx hoff
  refine ⟨fun v => ⟨v,t v⟩,?_,?_⟩
  · intro v
    refine ⟨(mem_configBlock _ _).mpr rfl,?_⟩
    intro e he hi
    obtain ⟨⟨f,r⟩,hr,hfe⟩ := hcomplete e he
    dsimp at hfe
    subst f
    have hse := hs _ hr
    simpa only [atEdge,ht,hse] using hr
  · intro v w _ e he hv hw
    exact (ht v ⟨e,hv⟩).trans (ht w ⟨e,hw⟩).symm

lemma zero_of_test_solution (x : Finset (Σ e : Edge n, LocalGroup e))
    (hx : ∀ r ∈ x, ∀ s ∈ x, r.1 = s.1 → r = s)
    (ht : ∃ t, (P.testProblem (b := b) x).Solution t) : ∑ v, b v = 0 := by
  obtain ⟨s,t,ht⟩ := P.exists_globals_of_solution x hx ht
  exact total_charge_of_global_configurations b s t ht

theorem test_iff_zero (b : Vertex n → Scalar)
    (x : Finset (Σ e : Edge n, LocalGroup e)) (hx : ConsistentSelection x)
    (hoff : ∀ r ∈ x, r.1 ∉ P.treeEdges)
    (hcomplete : ∀ e, e ∉ P.treeEdges → ∃ r ∈ x, r.1 = e) :
    (∀ v, ((P.testProblem (b := b) x).survivors v).Nonempty) ↔ ∑ v, b v = 0 := by
  rw [(P.testProblem x).all_survive_iff_solution]
  exact ⟨P.zero_of_test_solution x hx.1,fun hb => P.test_solution_of_zero b hb x hx hoff hcomplete⟩

end ParentEdges

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS WitnessedChoice.TreeTest Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

lemma atom_mem_state (a : Atom b) (s : Finset (Atom b)) : atom a ∈ elements (stateCode s) ↔ a ∈ s := by
  simp only [stateCode,elements_ofFinset,Finset.mem_image,atom_injective.eq_iff,exists_eq_right]

lemma chosen_incident_iff (x : Finset (Σ e : Edge n, LocalGroup e)) (v : Vertex n)
    (a : Configuration b v) (e : Edge n) (hi : incident v e) :
    (∃ z ∈ elements (stateCode (x.image Sum.inl : Finset (Atom b))) ∩ elements (edgeCode b e),
      inputHF (atomInput b) .I (atom (.inr ⟨v,a⟩)) z = true) ↔
      Sigma.mk e (a.state ⟨e,hi⟩) ∈ x := by
  simp only [Finset.mem_inter,stateCode,elements_ofFinset,Finset.image_image,
    Finset.mem_image,Function.comp_apply]
  constructor
  · rintro ⟨z,⟨⟨r,hr,rfl⟩,he⟩,hinc⟩
    have hre := (atom_mem_edgeCode _ _ _).mp he
    rcases r with ⟨f,s⟩
    dsimp at hre
    subst f
    obtain ⟨hi',hs⟩ := (input_inc_iff _ _ _ _).mp hinc
    rwa [hs]
  · intro h
    exact ⟨atom (.inl ⟨e,a.state ⟨e,hi⟩⟩),⟨⟨⟨e,a.state ⟨e,hi⟩⟩,h,rfl⟩,
      (atom_mem_edgeCode _ _ _).mpr rfl⟩,(input_inc_iff _ _ _ _).mpr ⟨hi,rfl⟩⟩

namespace QuotedGrid

open QuotedTerm QuotedFormula SourceSyntax

variable {k : ℕ}

lemma meaning_edgeDiff (env : Fin k → HF (Atom b)) (E T : QuotedTerm k) (D : Finset (Edge n))
    (hE : E.meaning (atomInput b) env = ofFinset (Finset.univ.image (edgeCode b)))
    (hT : T.meaning (atomInput b) env = ofFinset (D.image (edgeCode b))) :
    (E.diff T).meaning (atomInput b) env = ofFinset ((Finset.univ \ D).image (edgeCode b)) := by
  simp only [meaning_diff,hE,hT,elements_ofFinset]
  apply ofFinset_inj.mpr
  ext z
  simp only [Finset.mem_filter,Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_sdiff,
    not_exists,not_and]
  constructor
  · rintro ⟨⟨e,rfl⟩,he⟩
    exact ⟨e,fun ht => he e ht rfl,rfl⟩
  · rintro ⟨e,he,rfl⟩
    exact ⟨⟨e,rfl⟩,fun f hf hfe => he ((edgeCode_injective hfe) ▸ hf)⟩

lemma meaning_allowed {T₀ : RootedTree (Vertex n)} (env : Fin k → HF (Atom b))
    (E T xt vt at₀ : QuotedTerm k) (P : ParentEdges T₀)
    (x : Finset (Σ e : Edge n, LocalGroup e)) (v : Vertex n) (a : Configuration b v)
    (hE : E.meaning (atomInput b) env = ofFinset (Finset.univ.image (edgeCode b)))
    (hT : T.meaning (atomInput b) env = ofFinset (P.treeEdges.image (edgeCode b)))
    (hx : xt.meaning (atomInput b) env = stateCode (x.image Sum.inl))
    (hv : vt.meaning (atomInput b) env = vertexCode b v)
    (ha : at₀.meaning (atomInput b) env = atom (.inr ⟨v,a⟩)) (hn : 1 ≤ n) :
    (allowed E T xt vt at₀).meaning (atomInput b) env ↔ P.allowedConfig x ⟨v,a⟩ := by
  have hd := meaning_edgeDiff env E T P.treeEdges hE hT
  have hi (e : Edge n) := meaning_incident (Fin.cons (edgeCode b e) env) vt.up (var 0) v e hv rfl hn
  simp only [allowed,meaning_allIn,hd,elements_ofFinset,Finset.forall_mem_image,
    Finset.mem_sdiff,Finset.mem_univ,true_and,meaning_imp,hi,meaning_existsIn,meaning_inter,
    QuotedTerm.meaning_up,hx,meaning_var,Fin.cons_zero,meaning_input,ha]
  constructor
  · intro h e he hi
    exact (chosen_incident_iff x v a e hi).mp (h he hi)
  · intro h e he hi
    exact (chosen_incident_iff x v a e hi).mpr (h e he hi)

end QuotedGrid

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS WitnessedChoice.TreeTest Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

lemma common_edge_unique (e f : Edge n) (v w : Vertex n) (hvw : v ≠ w)
    (he : incident v e) (he' : incident w e) (hf : incident v f) (hf' : incident w f) : e=f := by
  have heq := (endpoints_incident_iff e v w).mpr ⟨hvw,he,he'⟩
  have hfq := (endpoints_incident_iff f v w).mpr ⟨hvw,hf,hf'⟩
  apply edge_eq_of_endpoints
  rcases heq with ⟨h₁,h₂⟩ | ⟨h₂,h₁⟩ <;> rcases hfq with ⟨h₃,h₄⟩ | ⟨h₄,h₃⟩
  · exact Or.inl ⟨h₁.symm.trans h₃,h₂.symm.trans h₄⟩
  · exact Or.inr ⟨h₁.symm.trans h₃,h₂.symm.trans h₄⟩
  · exact Or.inr ⟨h₂.symm.trans h₄,h₁.symm.trans h₃⟩
  · exact Or.inl ⟨h₂.symm.trans h₄,h₁.symm.trans h₃⟩

lemma atom_config_mem (a : ConfigAtom b) (s : Finset (ConfigAtom b)) :
    atom (.inr a) ∈ elements (stateCode (s.image Sum.inr : Finset (Atom b))) ↔ a ∈ s := by
  rw [atom_mem_state]
  simp only [Finset.mem_image,Sum.inr.injEq,exists_eq_right]

namespace ParentEdges

variable {T₀ : RootedTree (Vertex n)} (P : ParentEdges T₀)

lemma compatible_edge_iff (v w : Vertex n) (a : Configuration b v) (c : Configuration b w)
    (e : Edge n) (he : e ∈ P.treeEdges) (hne : v ≠ w) (hv : incident v e) (hw : incident w e) :
    P.configCompatibility ⟨v,a⟩ ⟨w,c⟩ ↔ a.state ⟨e,hv⟩ = c.state ⟨e,hw⟩ := by
  constructor
  · exact fun h => h e he hv hw
  · intro h f _ hf hg
    have heq := common_edge_unique e f v w hne hv hw hf hg
    subst f
    exact h

end ParentEdges

namespace QuotedGrid

open QuotedTerm QuotedFormula SourceSyntax

variable {k : ℕ}

lemma meaning_support (env : Fin k → HF (Atom b)) (wt St et at₀ : QuotedTerm k)
    (s : Finset (ConfigAtom b)) (v w : Vertex n) (a : Configuration b v) (e : Edge n)
    (hv : incident v e) (hw : incident w e)
    (hW : wt.meaning (atomInput b) env = vertexCode b w)
    (hS : St.meaning (atomInput b) env = stateCode (s.image Sum.inr))
    (hE : et.meaning (atomInput b) env = edgeCode b e)
    (hA : at₀.meaning (atomInput b) env = atom (.inr ⟨v,a⟩)) :
    (existsIn (wt.diff St) (existsIn et.up
      ((input .I at₀.up.up (var 0)).and (input .I (var 1) (var 0))))).meaning (atomInput b) env ↔
      ∃ c : Configuration b w, Sigma.mk w c ∉ s ∧ a.state ⟨e,hv⟩ = c.state ⟨e,hw⟩ := by
  simp only [meaning_existsIn,meaning_diff,hW,elements_ofFinset,Finset.mem_filter,and_assoc,
    exists_vertexCode,QuotedTerm.meaning_up,hS,atom_config_mem,hE,WitnessedSeparation.Grid.exists_edgeCode,
    meaning_and,meaning_input,hA,meaning_var,Fin.cons_zero,Fin.cons_one,input_inc_iff]
  constructor
  · rintro ⟨c,hc,r,⟨hv',h₁⟩,⟨hw',h₂⟩⟩
    exact ⟨c,hc,h₁.trans h₂.symm⟩
  · rintro ⟨c,hc,h⟩
    exact ⟨c,hc,a.state ⟨e,hv⟩,⟨hv,rfl⟩,⟨hw,h.symm⟩⟩

lemma meaning_unsupported {T₀ : RootedTree (Vertex n)} (env : Fin k → HF (Atom b))
    (V T St vt at₀ : QuotedTerm k) (P : ParentEdges T₀) (s : Finset (ConfigAtom b))
    (v : Vertex n) (a : Configuration b v)
    (hV : V.meaning (atomInput b) env = ofFinset (Finset.univ.image (vertexCode b)))
    (hT : T.meaning (atomInput b) env = ofFinset (P.treeEdges.image (edgeCode b)))
    (hS : St.meaning (atomInput b) env = stateCode (s.image Sum.inr))
    (hv : vt.meaning (atomInput b) env = vertexCode b v)
    (ha : at₀.meaning (atomInput b) env = atom (.inr ⟨v,a⟩)) (hn : 1 ≤ n) :
    (unsupported V T St vt at₀).meaning (atomInput b) env ↔
      ∃ w, T₀.Adj v w ∧ ¬ ∃ c ∈ configBlock b w, c ∉ s ∧ P.configCompatibility ⟨v,a⟩ c := by
  have hi (e : Edge n) (w : Vertex n) := meaning_incident
    (Fin.cons (vertexCode b w) (Fin.cons (edgeCode b e) env)) vt.up.up (var 1) v e hv rfl hn
  have hi' (e : Edge n) (w : Vertex n) := meaning_incident
    (Fin.cons (vertexCode b w) (Fin.cons (edgeCode b e) env)) (var 0) (var 1) w e rfl rfl hn
  simp only [unsupported,meaning_existsIn,hT,elements_ofFinset,Finset.mem_image,
    exists_exists_and_eq_and,QuotedTerm.meaning_up,hV,Finset.mem_univ,true_and,
    exists_exists_eq_and,meaning_allList,List.mem_cons,List.not_mem_nil,forall_eq_or_imp,forall_false,implies_true,and_true,
    meaning_neg,meaning_eq,meaning_var,Fin.cons_zero,hv,(vertexCode_injective hn).eq_iff,hi,hi']
  constructor
  · rintro ⟨e,he,w,hvw,hve,hwe,hsup⟩
    have hne : v ≠ w := Ne.symm hvw
    have hAdj : T₀.Adj v w := (P.graph_adj _ _).mp
      ⟨e,he,(endpoints_incident_iff e v w).mpr ⟨hne,hve,hwe⟩⟩
    refine ⟨w,hAdj,?_⟩
    rintro ⟨⟨u,c⟩,hc,hcs,hcomp⟩
    have hu := (mem_configBlock w ⟨u,c⟩).mp hc
    dsimp at hu
    subst u
    apply hsup
    apply (meaning_support (Fin.cons (vertexCode b w) (Fin.cons (edgeCode b e) env))
      (var 0) St.up.up (var 1) at₀.up.up s v w a e hve hwe rfl hS rfl ha).mpr
    exact ⟨c,hcs,(P.compatible_edge_iff v w a c e he hne hve hwe).mp hcomp⟩
  · rintro ⟨w,hadj,hsup⟩
    obtain ⟨e,he,hep⟩ := (P.graph_adj _ _).mpr hadj
    obtain ⟨hne,hve,hwe⟩ := (endpoints_incident_iff e v w).mp hep
    refine ⟨e,he,w,Ne.symm hne,hve,hwe,?_⟩
    intro hh
    obtain ⟨c,hcs,hce⟩ := (meaning_support
      (Fin.cons (vertexCode b w) (Fin.cons (edgeCode b e) env))
      (var 0) St.up.up (var 1) at₀.up.up s v w a e hve hwe rfl hS rfl ha).mp hh
    exact hsup ⟨⟨w,c⟩,(mem_configBlock _ _).mpr rfl,hcs,
      (P.compatible_edge_iff v w a c e he hne hve hwe).mpr hce⟩

end QuotedGrid

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS WitnessedChoice.TreeTest Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

lemma configAtoms_grid : WitnessedChoice.configAtoms (atomInput b) =
    (Finset.univ : Finset (ConfigAtom b)).image Sum.inr := by
  ext a
  simp only [WitnessedChoice.configAtoms,Finset.mem_filter,Finset.mem_univ,true_and,
    atomInput,decide_eq_true_eq,Finset.mem_image]
  constructor
  · intro h
    cases h with | cf v c => exact ⟨⟨v,c⟩,rfl⟩
  · rintro ⟨⟨v,c⟩,rfl⟩
    exact .cf v c

lemma config_mem_vertexCode (a : ConfigAtom b) (v : Vertex n) :
    atom (.inr a) ∈ elements (vertexCode b v) ↔ a.1 = v := by
  rw [mem_vertexCode_iff]
  constructor
  · rintro ⟨c,hc⟩
    exact congrArg Sigma.fst (Sum.inr.inj (atom_injective hc))
  · intro h
    rcases a with ⟨w,c⟩
    dsimp at h
    subst w
    exact ⟨c,rfl⟩

namespace QuotedGrid

open QuotedTerm QuotedFormula SourceSyntax

variable {k : ℕ}

lemma meaning_deletedStep {T₀ : RootedTree (Vertex n)} (env : Fin k → HF (Atom b))
    (V E T xt St : QuotedTerm k) (P : ParentEdges T₀) (s : Finset (ConfigAtom b))
    (x : Finset (Σ e : Edge n, LocalGroup e))
    (hV : V.meaning (atomInput b) env = ofFinset (Finset.univ.image (vertexCode b)))
    (hE : E.meaning (atomInput b) env = ofFinset (Finset.univ.image (edgeCode b)))
    (hT : T.meaning (atomInput b) env = ofFinset (P.treeEdges.image (edgeCode b)))
    (hx : xt.meaning (atomInput b) env = stateCode (x.image Sum.inl))
    (hS : St.meaning (atomInput b) env = stateCode (s.image Sum.inr)) (hn : 1 ≤ n) :
    (deletedStep V E T xt St).meaning (atomInput b) env =
      stateCode (((P.testProblem x).update s).image Sum.inr) := by
  have hp (v : Vertex n) (a : Configuration b v) :
      (existsIn V.up ((mem (var 1) (var 0)).and
        ((allowed E.up.up T.up.up xt.up.up (var 0) (var 1)).neg.or
          (unsupported V.up.up T.up.up St.up.up (var 0) (var 1))))).meaning (atomInput b)
        (Fin.cons (atom (.inr ⟨v,a⟩)) env) ↔
      ¬ P.allowedConfig x ⟨v,a⟩ ∨ ∃ w, T₀.Adj v w ∧
        ¬ ∃ c ∈ configBlock b w, c ∉ s ∧ P.configCompatibility ⟨v,a⟩ c := by
    have hex (Q : Vertex n → Prop) : (∃ w, v=w ∧ Q w) ↔ Q v := by
      constructor
      · rintro ⟨w,rfl,h⟩
        exact h
      · exact fun h => ⟨v,rfl,h⟩
    simp only [meaning_existsIn,QuotedTerm.meaning_up,hV,elements_ofFinset,Finset.mem_image,
      Finset.mem_univ,true_and,exists_exists_eq_and,meaning_and,meaning_mem,meaning_var,
      Fin.cons_zero,Fin.cons_one,config_mem_vertexCode,hex,
      meaning_or,meaning_neg]
    rw [meaning_allowed (Fin.cons (vertexCode b v) (Fin.cons (atom (.inr ⟨v,a⟩)) env))
      E.up.up T.up.up xt.up.up (var 0) (var 1) P x v a hE hT hx rfl rfl hn,
      meaning_unsupported (Fin.cons (vertexCode b v) (Fin.cons (atom (.inr ⟨v,a⟩)) env))
      V.up.up T.up.up St.up.up (var 0) (var 1) P s v a hV hT hS rfl rfl hn]
  simp only [deletedStep,meaning_cup,hS,QuotedTerm.meaning_filter,meaning_configAtoms,configAtoms_grid,
    stateCode,elements_ofFinset,Finset.image_image]
  apply ofFinset_inj.mpr
  ext z
  simp only [Finset.mem_union,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,
    Problem.update,ParentEdges.testProblem,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,
    true_and,mem_configBlock]
  constructor
  · rintro (⟨a,ha,rfl⟩ | ⟨⟨⟨v,a⟩,rfl⟩,h⟩)
    · exact ⟨a,Or.inl ha,rfl⟩
    · refine ⟨⟨v,a⟩,Or.inr ?_,rfl⟩
      rcases (hp v a).mp h with h | ⟨w,hw,hno⟩
      · exact Or.inl h
      · exact Or.inr ⟨v,rfl,w,hw,by simpa only [mem_configBlock] using hno⟩
  · rintro ⟨⟨v,a⟩,(ha | ha),rfl⟩
    · exact Or.inl ⟨⟨v,a⟩,ha,rfl⟩
    · refine Or.inr ⟨⟨⟨v,a⟩,rfl⟩,(hp v a).mpr ?_⟩
      rcases ha with h | ⟨w,hw,u,hu,hno⟩
      · exact Or.inl h
      · dsimp at hw
        subst w
        exact Or.inr ⟨u,hu,by simpa only [mem_configBlock] using hno⟩

end QuotedGrid

end

end WitnessedSeparation.Grid


section

namespace WitnessedChoice.TreeTest.Problem

open WitnessedChoice.BGS

variable {V A : Type} (P : Problem V A)

lemma run_eq_finite (k : ℕ) : P.run k = FiniteIteration.run P.update k := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg P.update ih

end WitnessedChoice.TreeTest.Problem

namespace WitnessedSeparation.Grid

noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS WitnessedChoice.TreeTest Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

namespace QuotedGrid

open QuotedTerm QuotedFormula SourceSyntax

variable {k : ℕ}

lemma value_deletion {T₀ : RootedTree (Vertex n)} (env : Fin k → HF (Atom b))
    (V E T xt : QuotedTerm k) (P : ParentEdges T₀)
    (x : Finset (Σ e : Edge n, LocalGroup e)) (p : Polynomial ℝ) (hp : GridResources p b)
    (hV : V.meaning (atomInput b) env = ofFinset (Finset.univ.image (vertexCode b)))
    (hE : E.meaning (atomInput b) env = ofFinset (Finset.univ.image (edgeCode b)))
    (hT : T.meaning (atomInput b) env = ofFinset (P.treeEdges.image (edgeCode b)))
    (hx : xt.meaning (atomInput b) env = stateCode (x.image Sum.inl)) (hn : 1 ≤ n) :
    (CPTTerm.quoted (deletedStep V.up E.up T.up xt.up (var 0))).iterate.value (atomInput b) p env =
      stateCode ((P.testProblem x).deleted.image Sum.inr) := by
  have hc : Fintype.card (ConfigAtom b) ≤ Fintype.card (Atom b) := by
    exact Fintype.card_le_of_injective (fun c : ConfigAtom b => (Sum.inr c : Atom b)) Sum.inr_injective
  have htime : Fintype.card (ConfigAtom b) ≤ resource p (Fintype.card (Atom b)) := by
    have := hp.basic
    omega
  have hspace : (TC (ofFinset ((Finset.univ : Finset (ConfigAtom b)).image
      (fun a => atom (Sum.inr a : Atom b))))).card ≤ resource p (Fintype.card (Atom b)) := by
    have he : ofFinset ((Finset.univ : Finset (ConfigAtom b)).image (fun a => atom (Sum.inr a : Atom b))) =
        stateCode ((Finset.univ : Finset (ConfigAtom b)).image Sum.inr) := by
      simp only [stateCode,Finset.image_image,Function.comp_def]
    rw [he,TC_stateCode,Finset.card_image_of_injective _ atom_injective,
      Finset.card_image_of_injective _ Sum.inr_injective,Finset.card_univ]
    exact htime
  apply CPTTerm.value_eq
  rw [CPTTerm.eval_iterate]
  have h := ordinaryIteration_encoded (resource p (Fintype.card (Atom b)))
    (fun a : ConfigAtom b => atom (Sum.inr a : Atom b)) (P.testProblem x).update
    (fun s => (deletedStep V.up E.up T.up xt.up (var 0)).meaning (atomInput b) (Fin.cons s env))
    (fun s => some ((CPTTerm.quoted (deletedStep V.up E.up T.up xt.up (var 0))).value
      (atomInput b) p (Fin.cons s env)))
    (by intro s; rw [CPTTerm.value_quoted])
    (by
      intro s
      have hcode (s : Finset (ConfigAtom b)) : ofFinset (s.image (fun a => atom (Sum.inr a : Atom b))) =
          stateCode (s.image Sum.inr) := by simp only [stateCode,Finset.image_image,Function.comp_def]
      rw [hcode,hcode]
      exact meaning_deletedStep (Fin.cons (stateCode (s.image Sum.inr)) env)
        V.up E.up T.up xt.up (var 0) P s x hV hE hT hx rfl hn)
    (P.testProblem x).le_update htime hspace
  convert h using 2
  simp only [stateCode,Finset.image_image,Function.comp_def,Problem.deleted,
    ParentEdges.testProblem,Finset.card_univ,Problem.run_eq_finite]

end QuotedGrid

end

end WitnessedSeparation.Grid

end


namespace WitnessedSeparation.Grid

noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS WitnessedChoice.TreeTest Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

lemma selected_inter_singleton (x : Finset (Σ e : Edge n, LocalGroup e))
    (hx : ∀ r ∈ x, ∀ t ∈ x, r.1=t.1 → r=t) (r : Σ e : Edge n, LocalGroup e) (hr : r ∈ x) :
    elements (stateCode (x.image Sum.inl : Finset (Atom b))) ∩ elements (edgeCode b r.1) =
      {atom (.inl r)} := by
  ext z
  simp only [Finset.mem_inter,stateCode,elements_ofFinset,Finset.image_image,
    Finset.mem_image,Function.comp_apply,Finset.mem_singleton]
  constructor
  · rintro ⟨⟨t,ht,rfl⟩,he⟩
    have heq := (atom_mem_edgeCode _ _ _).mp he
    rw [hx t ht r hr heq]
  · rintro rfl
    exact ⟨⟨r,hr,rfl⟩,(atom_mem_edgeCode _ _ _).mpr rfl⟩

lemma edgeState_subset_edgeAtoms (x : Finset (Σ e : Edge n, LocalGroup e)) :
    edgeState (b := b) x ⊆ WitnessedChoice.edgeAtoms (atomInput b) := by
  rw [edgeAtoms_grid]
  exact Finset.image_subset_image (Finset.subset_univ _)

namespace QuotedGrid

open QuotedTerm QuotedFormula SourceSyntax

variable {k : ℕ}

lemma meaning_complete {T₀ : RootedTree (Vertex n)} (env : Fin k → HF (Atom b))
    (E T xt : QuotedTerm k) (P : ParentEdges T₀)
    (x : Finset (Σ e : Edge n, LocalGroup e)) (hx : ConsistentSelection x)
    (hoff : ∀ r ∈ x, r.1 ∉ P.treeEdges)
    (hc : ∀ e, e ∉ P.treeEdges → ∃ r ∈ x, r.1=e)
    (hE : E.meaning (atomInput b) env = ofFinset (Finset.univ.image (edgeCode b)))
    (hT : T.meaning (atomInput b) env = ofFinset (P.treeEdges.image (edgeCode b)))
    (hX : xt.meaning (atomInput b) env = stateCode (x.image Sum.inl)) :
    (complete E T xt).meaning (atomInput b) env := by
  have hfirst : (eq xt (xt.inter QuotedTerm.edgeAtoms)).meaning (atomInput b) env := by
    simp only [meaning_eq,meaning_inter,hX,meaning_edgeAtoms,stateCode,elements_ofFinset]
    congr 1
    exact (Finset.inter_eq_left.mpr (Finset.image_subset_image (edgeState_subset_edgeAtoms x))).symm
  have hone : (allIn (E.diff T) (eq (xt.up.inter (var 0)).card (nat 1))).meaning (atomInput b) env := by
    simp only [meaning_allIn,meaning_edgeDiff env E T P.treeEdges hE hT,elements_ofFinset,
      Finset.forall_mem_image,Finset.mem_sdiff,Finset.mem_univ,true_and]
    intro e he
    obtain ⟨r,hr,hre⟩ := hc e he
    simp only [meaning_eq,meaning_card,meaning_inter,QuotedTerm.meaning_up,hX,meaning_var,
      Fin.cons_zero,meaning_nat,cardHF,elements_ofFinset]
    rw [←hre,selected_inter_singleton x hx.1 r hr,Finset.card_singleton]
  have hzero : (allIn T (eq (xt.up.inter (var 0)) empty)).meaning (atomInput b) env := by
    simp only [meaning_allIn,hT,elements_ofFinset,Finset.forall_mem_image,meaning_eq,
      meaning_inter,QuotedTerm.meaning_up,hX,meaning_var,Fin.cons_zero,meaning_empty]
    intro e he
    apply (selected_inter_empty x e).mpr
    intro r hr hh
    exact hoff r hr (hh.symm ▸ he)
  simpa only [complete,meaning_allList,List.mem_cons,List.not_mem_nil,forall_eq_or_imp,
    forall_false,implies_true,and_true] using ⟨hfirst,hone,hzero⟩

lemma meaning_survives (env : Fin k → HF (Atom b)) (V D : QuotedTerm k)
    (s : Finset (ConfigAtom b))
    (hV : V.meaning (atomInput b) env = ofFinset (Finset.univ.image (vertexCode b)))
    (hD : D.meaning (atomInput b) env = stateCode (s.image Sum.inr)) :
    (allIn V (nonempty ((var 0).diff D.up))).meaning (atomInput b) env ↔
      ∀ v, ((configBlock b v).filter (· ∉ s)).Nonempty := by
  simp only [meaning_allIn,hV,elements_ofFinset,Finset.forall_mem_image,Finset.mem_univ,
    forall_const,nonempty,meaning_neg,meaning_eq,meaning_diff,meaning_var,Fin.cons_zero,
    QuotedTerm.meaning_up,hD,meaning_empty]
  apply forall_congr'
  intro v
  rw [show (emptyHF : HF (Atom b)) = ofFinset ∅ from rfl,ofFinset_inj]
  change ({z ∈ elements (vertexCode b v) | z ∉ elements (stateCode (s.image Sum.inr))} : Finset _) ≠ ∅ ↔ _
  rw [←Finset.nonempty_iff_ne_empty]
  constructor
  · rintro ⟨z,hz⟩
    obtain ⟨hz,hnot⟩ := Finset.mem_filter.mp hz
    obtain ⟨c,rfl⟩ := (mem_vertexCode_iff v z).mp hz
    exact ⟨⟨v,c⟩,Finset.mem_filter.mpr ⟨(mem_configBlock _ _).mpr rfl,
      fun h => hnot ((atom_config_mem _ _).mpr h)⟩⟩
  · rintro ⟨⟨w,c⟩,hc⟩
    obtain ⟨hc,hn⟩ := Finset.mem_filter.mp hc
    have hw := (mem_configBlock v ⟨w,c⟩).mp hc
    dsimp at hw
    subst w
    exact ⟨atom (.inr ⟨v,c⟩),Finset.mem_filter.mpr ⟨(mem_vertexCode_iff _ _).mpr ⟨c,rfl⟩,
      fun h => hn ((atom_config_mem _ _).mp h)⟩⟩

end QuotedGrid

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS WitnessedChoice.TreeTest Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

lemma testProblem_block {T₀ : RootedTree (Vertex n)} (P : ParentEdges T₀)
    (x : Finset (Σ e : Edge n, LocalGroup e)) (v : Vertex n) :
    (P.testProblem (b := b) x).block v = configBlock b v := rfl

lemma survivors_test_iff_zero {T₀ : RootedTree (Vertex n)} (P : ParentEdges T₀)
    (x : Finset (Σ e : Edge n, LocalGroup e)) (hx : ConsistentSelection x)
    (hoff : ∀ r ∈ x, r.1 ∉ P.treeEdges)
    (hc : ∀ e, e ∉ P.treeEdges → ∃ r ∈ x, r.1=e) :
    (∀ v, ((configBlock b v).filter (· ∉ (P.testProblem (b := b) x).deleted)).Nonempty) ↔
      ∑ v, b v = 0 := by
  have h := P.test_iff_zero b x hx hoff hc
  have hs (v : Vertex n) : (P.testProblem (b := b) x).survivors v =
      (configBlock b v).filter (· ∉ (P.testProblem (b := b) x).deleted) := by
    ext a
    simp only [Problem.survivors,Finset.mem_filter,testProblem_block]
  simpa only [hs] using h

namespace QuotedGrid

open QuotedTerm QuotedFormula SourceSyntax SourceProgram

attribute [local irreducible] QuotedTerm.tree SourceSyntax.complete SourceSyntax.deletedStep

lemma value_output (p : Polynomial ℝ) (hp : GridResources p b)
    (α : Fin 4 → Vertex n) (hα : AnchoredTree.Resolving (boxGraph n) α)
    (x : Finset (Σ e : Edge n, LocalGroup e)) (hx : ConsistentSelection x)
    (hoff : ∀ r ∈ x, r.1 ∉ (anchoredParents α).treeEdges)
    (hc : ∀ e, e ∉ (anchoredParents α).treeEdges → ∃ r ∈ x, r.1=e) (hn : 1 ≤ n) :
    SourceProgram.output.value (atomInput b) p
      (Fin.cons (stateCode (edgeState x)) (Fin.cons (tupleCode (List.ofFn (vertexCode b ∘ α))) Fin.elim0)) =
      decide (∑ v, b v = 0) := by
  let R := distancesCode b (boxGraph n)
  let T := ofFinset ((anchoredParents α).treeEdges.image (edgeCode b))
  let D : HF (Atom b) := stateCode (((anchoredParents α).testProblem (b := b) x).deleted.image Sum.inr)
  let env₀ : Fin 3 → HF (Atom b) := Fin.cons R
    (Fin.cons (stateCode (edgeState x)) (Fin.cons (tupleCode (List.ofFn (vertexCode b ∘ α))) Fin.elim0))
  let env₁ : Fin 4 → HF (Atom b) := Fin.cons T env₀
  let env₂ : Fin 5 → HF (Atom b) := Fin.cons D env₁
  have ht : (tree (var 2) QuotedTerm.vertexBlocks QuotedTerm.edgeBlocks (var 0)).meaning
      (atomInput b) env₀ = T :=
    meaning_tree env₀ (var 2) _ _ (var 0) α hα rfl
      (quoted_vertexBlocks hn env₀) (quoted_edgeBlocks env₀) rfl hn
  have hd : (CPTTerm.quoted
      (deletedStep QuotedTerm.vertexBlocks QuotedTerm.edgeBlocks (var 1) (var 3) (var 0))).iterate.value
        (atomInput b) p env₁ = D := by
    exact value_deletion env₁ QuotedTerm.vertexBlocks QuotedTerm.edgeBlocks (var 0) (var 2)
      (anchoredParents α) x p hp (quoted_vertexBlocks hn env₁) (quoted_edgeBlocks env₁) rfl rfl hn
  have hcomplete := meaning_complete env₂ QuotedTerm.edgeBlocks (var 1) (var 3)
    (anchoredParents α) x hx hoff hc (quoted_edgeBlocks env₂) rfl rfl
  have hsurvive := meaning_survives env₂ QuotedTerm.vertexBlocks (var 0)
    ((anchoredParents α).testProblem (b := b) x).deleted (quoted_vertexBlocks hn env₂) rfl
  have hm : ((complete QuotedTerm.edgeBlocks (var 1) (var 3)).and
      (allIn QuotedTerm.vertexBlocks (nonempty ((var 0).diff (var 1))))).meaning (atomInput b) env₂ ↔
        ∑ v, b v = 0 := by
    rw [meaning_and,and_iff_right hcomplete]
    change (allIn QuotedTerm.vertexBlocks (nonempty ((var 0).diff (var 1)))).meaning
      (atomInput b) env₂ ↔ _ at hsurvive
    exact hsurvive.trans (survivors_test_iff_zero (b := b) (anchoredParents α) x hx hoff hc)
  rw [SourceProgram.output,CPTFormula.value_letIn,value_distances _ p hp hn,
    CPTFormula.value_letIn,CPTTerm.value_quoted]
  change (CPTFormula.letIn _ _).value (atomInput b) p
    (Fin.cons ((tree (var 2) QuotedTerm.vertexBlocks QuotedTerm.edgeBlocks (var 0)).meaning
      (atomInput b) env₀) env₀) = _
  rw [ht,CPTFormula.value_letIn]
  change (CPTFormula.quoted _).value (atomInput b) p
    (Fin.cons ((CPTTerm.quoted
      (deletedStep QuotedTerm.vertexBlocks QuotedTerm.edgeBlocks (var 1) (var 3) (var 0))).iterate.value
        (atomInput b) p env₁) env₁) = _
  rw [hd,CPTFormula.value_quoted]
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using hm

end QuotedGrid

end

end WitnessedSeparation.Grid



namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

namespace Realizes

variable {A : Type} [Fintype A] {P : Selection A}
    {step : HF A → HF A → Result (HF A)} {choice : HF A → Result (HF A)}
    {witness : HF A → HF A → Result (HF A)}
    (hr : Realizes P step choice witness)

include hr

lemma first_encode {b : ℕ → Finset A} {c : ℕ → Option A} {t : ℕ}
    (hb : P.FirstStabilization b c t) :
    FirstPath step choice (stateCode ∘ b) (choiceCode ∘ c) t := by
  refine ⟨⟨?_,?_⟩,?_,?_⟩
  · simp only [Function.comp_apply,hb.1.1,stateCode,Finset.image_empty]
    rfl
  · intro i hi
    obtain ⟨hc,hs⟩ := hb.1.2 i hi
    refine ⟨⟨ofFinset ((P.choices (b i)).image choiceCode),hr.choice_eq _,?_⟩,?_⟩
    · exact (elements_ofFinset _ ▸ Finset.mem_image.mpr ⟨c i,hc,rfl⟩)
    · simpa only [Function.comp_apply,hs] using hr.step_eq (b i) (c i) hc
  · intro i hi he
    exact hb.2.1 i hi (stateCode_inj.mp he)
  · exact congrArg stateCode hb.2.2

lemma value_constant {S : Input A} {α : HF A} (hf : P.Filtered S α)
    (p : ℕ) (hp : Fintype.card A+2 ≤ p) (free : Finset (Fin 1))
    (output : HF A → Result Bool) (hout : ∀ x : Finset A, (output (stateCode x)).isSome)
    (v : Bool)
    (ht : ∀ b c t, P.FirstStabilization b c t → output (stateCode (b t)) = some v) :
    witnessedIteration S p free (Fin.cons α Fin.elim0) step choice witness output = some v := by
  have ht' : ∀ b c t, FirstPath step choice b c t → output (b t) = some v := by
    intro b c t hh
    obtain ⟨_,hb,_⟩ := hr.prefix_decode hh.1
    rw [hb t (by omega)]
    exact ht _ _ t (hr.first_decode hh)
  have hiff : (∀ b c t, FirstPath step choice b c t → output (b t) = some true) ↔ v = true := by
    constructor
    · intro h
      obtain ⟨b,c,t,hb⟩ := P.exists_path
      have h₁ := h _ _ t (hr.first_encode hb)
      have h₂ := ht' _ _ t (hr.first_encode hb)
      exact Option.some.inj (h₂.symm.trans h₁)
    · intro hv b c t hh
      exact (ht' b c t hh).trans (congrArg some hv)
  unfold witnessedIteration
  rw [ite_eq_left (hr.good hf p hp free output hout)]
  rw [propext hiff]
  cases v <;> simp

end Realizes

namespace GuardedProgram

open WitnessedChoice.RelationPools

lemma value_constant {A : Type} [Fintype A] (G : GuardedProgram) (S : Input A) (p : Polynomial ℝ)
    (α₀ : Fin 4 → Finset A) (hα : ∀ i, α₀ i ∈ blocks S)
    (hp : Fintype.card A+2 ≤ resource p (Fintype.card A)) (v : Bool)
    (ht : ∀ B c t, (G.selection S p (parameterCode α₀)).FirstStabilization B c t →
      G.output.value S p (Fin.cons (stateCode (B t)) (Fin.cons (parameterCode α₀) Fin.elim0)) = v) :
    G.formula.eval S p (Fin.cons (parameterCode α₀) Fin.elim0) = some v := by
  apply (G.realizes S p (parameterCode α₀)).value_constant
    (guardedSelection_filtered G.localBound S True _ _ α₀ hα)
    (resource p (Fintype.card A)) hp
  · intro x
    rw [G.output.eval_value]
    simp
  · intro B c t h
    rw [G.output.eval_value,ht B c t h]

end GuardedProgram

end

end WitnessedChoice.BGS



namespace WitnessedSeparation.Grid

noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary RelationPools

variable {n : ℕ} {b : Vertex n → Scalar}

namespace QuotedGrid

open SourceProgram

attribute [local irreducible] SourceProgram.candidates SourceProgram.cycles SourceProgram.output

lemma terminal_output (p : Polynomial ℝ) (hp : GridResources p b)
    (α : Fin 4 → Vertex n) (hα : AnchoredTree.Resolving (boxGraph n) α) (hn : 1 ≤ n)
    (B : ℕ → Finset (Atom b)) (c : ℕ → Option (Atom b)) (t : ℕ)
    (hh : (program.body.selection (atomInput b) p
      (tupleCode (List.ofFn (vertexCode b ∘ α)))).FirstStabilization B c t) :
    program.body.output.value (atomInput b) p
      (Fin.cons (stateCode (B t)) (Fin.cons (tupleCode (List.ofFn (vertexCode b ∘ α))) Fin.elim0)) =
        decide (∑ v, b v = 0) := by
  obtain ⟨x,hx,hcons,hoff,hc⟩ := (anchoredParents α).terminal_complete α
    (program.body.selection (atomInput b) p (tupleCode (List.ofFn (vertexCode b ∘ α))))
    (fun x => selection_candidates p hp α hα x hn)
    (fun x _ hoff => selection_transitive p hp α hα x hoff hn) hh
  rw [hx]
  exact value_output p hp α hα x hcons hoff hc hn

lemma body_value (p : Polynomial ℝ) (hp : GridResources p b)
    (α : Fin 4 → Vertex n) (hα : AnchoredTree.Resolving (boxGraph n) α) (hn : 1 ≤ n) :
    program.body.formula.eval (atomInput b) p
      (Fin.cons (tupleCode (List.ofFn (vertexCode b ∘ α))) Fin.elim0) =
        some (decide (∑ v, b v = 0)) := by
  apply program.body.value_constant (atomInput b) p (fun i => vertexBlockSet b (α i))
    (fun i => ?_) hp.basic
  · exact terminal_output p hp α hα hn
  · apply Finset.mem_union_right
    rw [vertexBlocks_grid hn]
    exact Finset.mem_image.mpr ⟨α _,Finset.mem_univ _,rfl⟩

end QuotedGrid

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

namespace QuotedGrid

open QuotedTerm QuotedFormula SourceSyntax SourceProgram

attribute [local irreducible] QuotedFormula.resolving

lemma mem_grid_blockParameters {k : ℕ} (env : Fin k → HF (Atom b)) (hn : 1 ≤ n) (z : HF (Atom b)) :
    z ∈ elements ((QuotedTerm.blockParameters : QuotedTerm k).meaning (atomInput b) env) ↔
      ∃ α : Fin 4 → Vertex n, tupleCode (List.ofFn (vertexCode b ∘ α)) = z := by
  rw [blockParameters,mem_tupleProduct,quoted_vertexBlocks hn env,elements_ofFinset]
  constructor
  · rintro ⟨f,hf,hz⟩
    have hh (i : Fin 4) : ∃ v : Vertex n, vertexCode b v = f i := by
      obtain ⟨v,_,hv⟩ := Finset.mem_image.mp (hf i)
      exact ⟨v,hv⟩
    choose α hα using hh
    exact ⟨α,(congrArg (fun f => tupleCode (List.ofFn f)) (funext hα)).trans hz⟩
  · rintro ⟨α,hz⟩
    exact ⟨vertexCode b ∘ α,fun i => Finset.mem_image.mpr ⟨α i,Finset.mem_univ _,rfl⟩,hz⟩

lemma mem_parameters (p : Polynomial ℝ) (hp : GridResources p b) (hn : 1 ≤ n) (z : HF (Atom b)) :
    z ∈ elements (SourceProgram.parameters.value (atomInput b) p Fin.elim0) ↔
      ∃ α : Fin 4 → Vertex n, AnchoredTree.Resolving (boxGraph n) α ∧
        tupleCode (List.ofFn (vertexCode b ∘ α)) = z := by
  let env : Fin 1 → HF (Atom b) := Fin.cons (distancesCode b (boxGraph n)) Fin.elim0
  have hm (α : Fin 4 → Vertex n) :
      (resolving (var 0) QuotedTerm.vertexBlocks (var 1)).meaning (atomInput b)
        (Fin.cons (tupleCode (List.ofFn (vertexCode b ∘ α))) env) ↔
          AnchoredTree.Resolving (boxGraph n) α := by
    exact meaning_resolving (atomInput b) _ (var 0) QuotedTerm.vertexBlocks (var 1)
      (vertexCode b) (vertexCode_injective hn) (boxGraph n) (boxGraph_connected n) α rfl
      (quoted_vertexBlocks hn _) rfl (vertex_card_le_atoms hn)
  rw [SourceProgram.parameters,CPTTerm.value_letIn,value_distances _ p hp hn,CPTTerm.value_quoted]
  simp only [QuotedTerm.meaning_filter,elements_ofFinset,Finset.mem_filter]
  rw [mem_grid_blockParameters env hn z]
  constructor
  · rintro ⟨⟨α,rfl⟩,hr⟩
    exact ⟨α,(hm α).mp hr,rfl⟩
  · rintro ⟨α,hα,rfl⟩
    exact ⟨⟨α,rfl⟩,(hm α).mpr hα⟩

lemma mem_parameterTerm (p : Polynomial ℝ) (hp : GridResources p b) (hn : 1 ≤ n) (z : HF (Atom b)) :
    z ∈ elements (program.parameterTerm.value (atomInput b) p Fin.elim0) ↔
      ∃ α : Fin 4 → Vertex n, AnchoredTree.Resolving (boxGraph n) α ∧
        tupleCode (List.ofFn (vertexCode b ∘ α)) = z := by
  rw [ClosedGuardedProgram.parameterTerm,CPTTerm.value_letIn,CPTTerm.value_quoted]
  simp only [QuotedTerm.meaning_filter,elements_ofFinset,Finset.mem_filter,meaning_mem,meaning_var,
    Fin.cons_zero,Fin.cons_one]
  change (z ∈ elements (QuotedTerm.blockParameters.meaning (atomInput b) _) ∧
    z ∈ elements (SourceProgram.parameters.value (atomInput b) p Fin.elim0)) ↔ _
  rw [mem_parameters p hp hn z]
  constructor
  · exact fun h => h.2
  · rintro ⟨α,hα,hz⟩
    exact ⟨(mem_grid_blockParameters _ hn z).mpr ⟨α,hz⟩,α,hα,hz⟩

lemma parameterTerm_nonempty (p : Polynomial ℝ) (hp : GridResources p b) (hn : 1 ≤ n) :
    (elements (program.parameterTerm.value (atomInput b) p Fin.elim0)).Nonempty := by
  refine ⟨tupleCode (List.ofFn (vertexCode b ∘ cornerAnchors n)),(mem_parameterTerm p hp hn _).mpr
    ⟨cornerAnchors n,?_,rfl⟩⟩
  intro u v h
  exact cornerAnchors_resolve u v (fun i => congrFun h i)

end QuotedGrid

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

namespace QuotedGrid

open SourceProgram

attribute [local irreducible] SourceProgram.parameters SourceProgram.candidates
  SourceProgram.cycles SourceProgram.output

lemma formula_value_oai (p : Polynomial ℝ) (hp : GridResources p b) (hn : 1 ≤ n) :
    program.formula.eval (atomInput b) p Fin.elim0 = some (decide (∑ v, b v = 0)) := by
  have he (z : HF (Atom b)) (hz : z ∈ elements (program.parameterTerm.value (atomInput b) p Fin.elim0)) :
      program.body.formula.eval (atomInput b) p (Fin.cons z Fin.elim0) =
        some (decide (∑ v, b v = 0)) := by
    obtain ⟨α,hα,rfl⟩ := (mem_parameterTerm p hp hn z).mp hz
    exact body_value p hp α hα hn
  rw [ClosedGuardedProgram.formula,
    Formula.eval_existsIn_on _ p _ _ _ (program.parameterTerm.eval_value _ p _) he]
  apply congrArg some
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · exact fun ⟨_,_,h⟩ => h
  · intro h
    obtain ⟨z,hz⟩ := parameterTerm_nonempty p hp hn
    exact ⟨z,hz,h⟩

end QuotedGrid

end

end WitnessedSeparation.Grid

end OAI
end

theorem solution : type_of% @OAI.WitnessedSeparation.Grid.QuotedGrid.formula_value_oai := @OAI.WitnessedSeparation.Grid.QuotedGrid.formula_value_oai
