-- Prove2me | solution 1 for OAI.VariableWL.main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T02:01:33.060911+00:00
-- url     : https://prove2.me/submissions/e27f0cfd-8d06-40a8-a926-135f1a7146e3

import Mathlib
import Definitions.Def_VariableWL
import Definitions.Def_OAIQ6Wl002
import Theorems.Thm_OAI_VariableWL_general_hard
import Theorems.Thm_OAI_VariableWL_subcubic_hard

section
-- module Solutions.OAIQ6_WL.VariableWL_Refinement
attribute [-instance] _root_.OAI.VariableWL.Circuit.ProductCellular.powTwoNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6

namespace VariableWL

private theorem map_univ_comp_equiv {A : Type uVariable1} {B : Type uVariable2} {C : Type uVariable3} [Fintype A] [Fintype B]
    (e : A ≃ B) (f : B → C) :
    Finset.univ.val.map f = Finset.univ.val.map (fun a => f (e a)) := by
  rw [← Multiset.map_univ_val_equiv e, Multiset.map_map]
  rfl

theorem color_iso {G H : Graph} (e : G.graph ≃g H.graph) (k : ℕ) :
    ∀ s (v : Tuple G k), color H k s (e ∘ v) = color G k s v := by
  classical
  intro s
  induction s with
  | zero =>
    intro v
    funext i j
    simp [color, e.injective.eq_iff, e.map_rel_iff]
  | succ s ih =>
    intro v
    apply Prod.ext (ih v)
    change Finset.univ.val.map (fun z => fun i =>
      color H k s (Function.update (e ∘ v) i z)) =
      Finset.univ.val.map (fun z => fun i => color G k s (Function.update v i z))
    rw [map_univ_comp_equiv e.toEquiv]
    apply Multiset.map_congr rfl
    intro z _
    funext i
    simpa only [Function.comp_update, RelIso.coe_fn_toEquiv] using ih (Function.update v i z)

theorem histogram_iso {G H : Graph} (e : G.graph ≃g H.graph) (k s : ℕ) :
    histogram H k s = histogram G k s := by
  unfold histogram
  rw [map_univ_comp_equiv (tupleEquiv e k)]
  apply Multiset.map_congr rfl
  intro v _
  exact color_iso e k s v

theorem equivalent_of_iso {G H : Graph} (e : G.graph ≃g H.graph) (k : ℕ) :
    Equivalent G H k := fun s => (histogram_iso e k s).symm

theorem equivalent_order {G H : Graph} {k : ℕ} (hk : k ≠ 0)
    (h : Equivalent G H k) : G.order = H.order := by
  have hc := congrArg Multiset.card (h 0)
  simp only [histogram_card] at hc
  exact Nat.pow_left_injective hk hc

theorem color_zero_eq_iff {G H : Graph} {k : ℕ} (v : Tuple G k) (w : Tuple H k) :
    color G k 0 v = color H k 0 w ↔
      (∀ i j, v i = v j ↔ w i = w j) ∧
      (∀ i j, G.graph.Adj (v i) (v j) ↔ H.graph.Adj (w i) (w j)) := by
  classical
  constructor
  · intro h
    have hi : ∀ i j, (v i = v j ↔ w i = w j) ∧
        (G.graph.Adj (v i) (v j) ↔ H.graph.Adj (w i) (w j)) := by
      intro i j
      have hc := congrFun (congrFun h i) j
      change (decide (v i = v j), decide (G.graph.Adj (v i) (v j))) =
        (decide (w i = w j), decide (H.graph.Adj (w i) (w j))) at hc
      simpa only [Prod.mk.injEq, decide_eq_decide] using hc
    exact ⟨fun i j => (hi i j).1, fun i j => (hi i j).2⟩
  · rintro ⟨he, ha⟩
    funext i j
    apply Prod.ext
    · exact decide_eq_decide.mpr (he i j)
    · exact decide_eq_decide.mpr (ha i j)

theorem exists_color_match {G H : Graph} {k s : ℕ}
    (h : histogram G k s = histogram H k s) (v : Tuple G k) :
    ∃ w : Tuple H k, color H k s w = color G k s v := by
  have hm : color G k s v ∈ histogram G k s :=
    Multiset.mem_map.mpr ⟨v, Finset.mem_univ_val v, rfl⟩
  rw [h] at hm
  rcases Multiset.mem_map.mp hm with ⟨w, _, hw⟩
  exact ⟨w, hw⟩

theorem iso_of_equivalent_large {G H : Graph} {k : ℕ} (hk : k ≠ 0)
    (hlarge : G.order ≤ k) (h : Equivalent G H k) : Nonempty (G.graph ≃g H.graph) := by
  classical
  have horder := equivalent_order hk h
  by_cases hz : G.order = 0
  · have : IsEmpty (Fin G.order) := ⟨fun v => by have := v.isLt; omega⟩
    have : IsEmpty (Fin H.order) := ⟨fun v => by have := v.isLt; omega⟩
    exact ⟨⟨Equiv.equivOfIsEmpty _ _, fun {i _} => isEmptyElim i⟩⟩
  have hn : 0 < G.order := Nat.pos_of_ne_zero hz
  let pick : Fin G.order → Fin k := fun x => ⟨x.val, lt_of_lt_of_le x.isLt hlarge⟩
  let v : Tuple G k := fun i => ⟨i.val % G.order, Nat.mod_lt _ hn⟩
  have hv : ∀ x, v (pick x) = x := by
    intro x
    apply Fin.ext
    exact Nat.mod_eq_of_lt x.isLt
  obtain ⟨w, hw⟩ := exists_color_match (h 0) v
  obtain ⟨heq, hadj⟩ := (color_zero_eq_iff v w).mp hw.symm
  let f : Fin G.order → Fin H.order := fun x => w (pick x)
  have hinj : Function.Injective f := by
    intro x y hxy
    have hxy' := (heq (pick x) (pick y)).mpr hxy
    simpa only [hv] using hxy'
  have hsurj : Function.Surjective f := by
    apply (Fintype.bijective_iff_injective_and_card f).mpr
      ⟨hinj, by simpa using horder⟩ |>.2
  refine ⟨⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, ?_⟩⟩
  intro x y
  change H.graph.Adj (w (pick x)) (w (pick y)) ↔ G.graph.Adj x y
  simpa only [hv] using (hadj (pick x) (pick y)).symm

theorem equivalent_large_iff_iso {G H : Graph} {k : ℕ} (hk : k ≠ 0)
    (hlarge : G.order ≤ k) :
    Equivalent G H k ↔ Nonempty (G.graph ≃g H.graph) := by
  constructor
  · exact iso_of_equivalent_large hk hlarge
  · rintro ⟨e⟩
    exact equivalent_of_iso e k

end VariableWL

namespace VariableWL

theorem color_factor_succ {G : Graph} {k s t : ℕ} (f : Color k s → Color k t)
    (hf : ∀ v : Tuple G k, color G k t v = f (color G k s v)) (v : Tuple G k) :
    color G k (t+1) v = liftColor f (color G k (s+1) v) := by
  apply Prod.ext (hf v)
  change Finset.univ.val.map (fun z => fun i => color G k t (Function.update v i z)) =
    (Finset.univ.val.map (fun z => fun i => color G k s (Function.update v i z))).map
      (fun a => f ∘ a)
  rw [Multiset.map_map]
  apply Multiset.map_congr rfl
  intro z _
  funext i
  exact hf (Function.update v i z)

theorem tagColor_factor_succ {G H : Graph} {k s t : ℕ} (f : Color k s → Color k t)
    (hf : ∀ v, tagColor G H k t v = f (tagColor G H k s v)) (v : TaggedTuple G H k) :
    tagColor G H k (t+1) v = liftColor f (tagColor G H k (s+1) v) := by
  cases v with
  | inl v => exact color_factor_succ f (fun a => hf (.inl a)) v
  | inr v => exact color_factor_succ f (fun a => hf (.inr a)) v

theorem tagColor_eq_previous {G H : Graph} {k s : ℕ} {v w : TaggedTuple G H k}
    (h : tagColor G H k (s+1) v = tagColor G H k (s+1) w) :
    tagColor G H k s v = tagColor G H k s w := by
  have hp := congrArg Prod.fst h
  cases v <;> cases w <;> exact hp

private theorem samePairs_next_subset (G H : Graph) (k s : ℕ) :
    samePairs G H k (s+1) ⊆ samePairs G H k s := by
  classical
  intro p hp
  simp only [samePairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  exact tagColor_eq_previous hp

private theorem exists_nat_plateau (a : ℕ → ℕ) (hmono : ∀ n, a (n+1) ≤ a n) :
    ∃ n ≤ a 0, a (n+1) = a n := by
  by_contra! h
  have hstrict : ∀ n ≤ a 0, a (n+1) < a n := by
    intro n hn
    exact lt_of_le_of_ne (hmono n) (h n hn)
  have hbound : ∀ n ≤ a 0 + 1, a n + n ≤ a 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro hn
      have hprev := ih (by omega)
      have hstep := hstrict n (by omega)
      omega
  have := hbound (a 0 + 1) le_rfl
  omega

theorem exists_stable_round (G H : Graph) (k : ℕ) :
    ∃ s ≤ (G.order ^ k + H.order ^ k) ^ 2, StableAt G H k s := by
  classical
  obtain ⟨s, hs, heq⟩ := exists_nat_plateau
    (fun n => (samePairs G H k n).card)
    (fun n => Finset.card_le_card (samePairs_next_subset G H k n))
  have hsets : samePairs G H k (s+1) = samePairs G H k s :=
    Finset.eq_of_subset_of_card_le (samePairs_next_subset G H k s) heq.ge
  refine ⟨s, ?_, ?_⟩
  · refine hs.trans ?_
    calc
      (samePairs G H k 0).card ≤ Fintype.card (TaggedTuple G H k × TaggedTuple G H k) :=
        Finset.card_le_univ _
      _ = (G.order ^ k + H.order ^ k) ^ 2 := by
        simp [TaggedTuple, Tuple, pow_two]
  · intro v w hvw
    have hm : (v, w) ∈ samePairs G H k s := by
      simp [samePairs, hvw]
    rw [← hsets] at hm
    simpa only [samePairs, Finset.mem_filter, Finset.mem_univ, true_and] using hm

theorem stable_later_factor {G H : Graph} {k s : ℕ} (hs : StableAt G H k s) :
    ∀ t, ∃ f : Color k s → Color k (s+t),
      ∀ v, tagColor G H k (s+t) v = f (tagColor G H k s v) := by
  obtain ⟨f₀, hf₀⟩ := (Function.factorsThrough_iff (tagColor G H k (s+1))).mp hs
  have hbase : ∀ v, tagColor G H k (s+1) v = f₀ (tagColor G H k s v) :=
    fun v => congrFun hf₀ v
  intro t
  induction t with
  | zero => exact ⟨id, fun _ => rfl⟩
  | succ t ih =>
    obtain ⟨f, hf⟩ := ih
    refine ⟨liftColor f ∘ f₀, ?_⟩
    intro v
    calc
      tagColor G H k (s+(t+1)) v = liftColor f (tagColor G H k (s+1) v) :=
        tagColor_factor_succ f hf v
      _ = (liftColor f ∘ f₀) (tagColor G H k s v) := by rw [hbase]; rfl

theorem histogram_eq_previous {G H : Graph} {k s : ℕ}
    (h : histogram G k (s+1) = histogram H k (s+1)) :
    histogram G k s = histogram H k s := by
  simpa only [histogram_fst] using congrArg (Multiset.map Prod.fst) h

theorem histogram_eq_of_le {G H : Graph} {k s t : ℕ} (hle : s ≤ t)
    (h : histogram G k t = histogram H k t) : histogram G k s = histogram H k s := by
  induction t generalizing s with
  | zero => have : s = 0 := Nat.eq_zero_of_le_zero hle; subst s; exact h
  | succ t ih =>
    by_cases he : s = t + 1
    · subst s; exact h
    · exact ih (by omega) (histogram_eq_previous h)

theorem histogram_eq_later {G H : Graph} {k s : ℕ} (hs : StableAt G H k s)
    (h : histogram G k s = histogram H k s) (t : ℕ) :
    histogram G k (s+t) = histogram H k (s+t) := by
  obtain ⟨f, hf⟩ := stable_later_factor hs t
  have hG : histogram G k (s+t) = (histogram G k s).map f := by
    simp only [histogram, Multiset.map_map]
    apply Multiset.map_congr rfl
    intro v _
    exact hf (.inl v)
  have hH : histogram H k (s+t) = (histogram H k s).map f := by
    simp only [histogram, Multiset.map_map]
    apply Multiset.map_congr rfl
    intro v _
    exact hf (.inr v)
  rw [hG, hH, h]

theorem equivalent_iff_bounded_round (G H : Graph) (k : ℕ) :
    Equivalent G H k ↔
      histogram G k ((G.order ^ k + H.order ^ k) ^ 2) =
      histogram H k ((G.order ^ k + H.order ^ k) ^ 2) := by
  constructor
  · intro h; exact h _
  · intro hn
    obtain ⟨s, hs, hstable⟩ := exists_stable_round G H k
    have heq := histogram_eq_of_le hs hn
    intro t
    by_cases ht : t ≤ s
    · exact histogram_eq_of_le ht heq
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt (Nat.lt_of_not_ge ht))
      exact histogram_eq_later hstable heq d

end VariableWL

universe uGame1 uGame2 uGame3 uGame4 uGame5 uGame6 uGame7

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_Program
attribute [-instance] _root_.OAI.VariableWL.MachineOneHead.instFintypeControl _root_.OAI.VariableWL.MachineReduction.comparisonFintype _root_.OAI.VariableWL.MachineReduction.letterFintype _root_.OAI.VariableWL.MachineReduction.realFintype _root_.OAI.VariableWL.MachineReduction.realNonempty _root_.OAI.VariableWL.MultiStack.instFintypeLabel _root_.OAI.VariableWL.MultiStack.instFintypeMotion _root_.OAI.VariableWL.MultiStack.instFintypeVars _root_.OAI.VariableWL.MultiStack.instInhabitedLabel _root_.OAI.VariableWL.MultiStack.instInhabitedVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace VariableWL.Computation

variable {Γ : Type}

theorem configuration_ext {M : Machine} {a b : Configuration M}
    (hc : a.control=b.control) (hh : a.heads=b.heads) (hs : a.cells=b.cells) : a=b := by
  cases a
  cases b
  congr

namespace Program
variable {Q Γ : Type} {k : ℕ}

noncomputable section
variable [Fintype Q] [Fintype Γ]

 theorem controlCode_injective : Function.Injective (controlCode (Q:=Q)) := by
  intro a b h
  cases a with
  | none => cases b with
    | none => rfl
    | some q => have := congrArg Fin.val h; dsimp [controlCode] at this; omega
  | some a => cases b with
    | none => have := congrArg Fin.val h; dsimp [controlCode] at this; omega
    | some b =>
      congr 1
      apply (Fintype.equivFin Q).injective
      apply Fin.ext
      have := congrArg Fin.val h
      simpa only [controlCode, Nat.add_right_cancel_iff] using this

 theorem symbolCode_injective : Function.Injective (symbolCode (Γ:=Γ)) := by
  intro a b h
  have hv := congrArg Fin.val h
  cases a with
  | none => cases b with
    | none => rfl
    | some b => cases b with
      | inl b => cases b
                 · change 0=1 at hv; omega
                 · change 0=2 at hv; omega
      | inr b => change 0=(Fintype.equivFin Γ b).val+3 at hv; omega
  | some a => cases b with
    | none => cases a with
      | inl a => cases a
                 · change 1=0 at hv; omega
                 · change 2=0 at hv; omega
      | inr a => change (Fintype.equivFin Γ a).val+3=0 at hv; omega
    | some b => cases a with
      | inl a => cases b with
        | inl b => cases a <;> cases b
                   · rfl
                   · change 1=2 at hv; omega
                   · change 2=1 at hv; omega
                   · rfl
        | inr b => cases a
                   · change 1=(Fintype.equivFin Γ b).val+3 at hv; omega
                   · change 2=(Fintype.equivFin Γ b).val+3 at hv; omega
      | inr a => cases b with
        | inl b => cases b
                   · change (Fintype.equivFin Γ a).val+3=1 at hv; omega
                   · change (Fintype.equivFin Γ a).val+3=2 at hv; omega
        | inr b =>
          congr 2
          apply (Fintype.equivFin Γ).injective
          apply Fin.ext
          change (Fintype.equivFin Γ a).val+3=(Fintype.equivFin Γ b).val+3 at hv
          omega

 @[simp] theorem control_roundtrip (q : Option Q) : controlDecode (controlCode q)=q :=
  Function.leftInverse_invFun controlCode_injective q
 @[simp] theorem symbol_roundtrip (a : Symbol Γ) : symbolDecode (symbolCode a)=a :=
  Function.leftInverse_invFun symbolCode_injective a

 theorem encodeWord (w : Word) (i : ℤ) :
    symbolCode (typedWordCells (Γ:=Γ) w i)=wordCells (Fintype.card Γ) w i := by
  unfold typedWordCells wordCells
  split_ifs
  · cases w[i.toNat]? with
    | none => rfl
    | some b => cases b <;> rfl
  · rfl

 theorem encode_initial (P : Program Q Γ k) (w : Word) :
    P.encodeState (initial w)=VariableWL.initial P.compile w := by
  apply configuration_ext <;> try rfl
  funext j i
  change symbolCode ((if j=0 then typedWordCells w else fun _ => none) i) =
    (if j=0 then wordCells _ w else fun _ => 0) i
  split_ifs with h
  · exact encodeWord w i
  · rfl

 theorem encode_step (P : Program Q Γ k) (s : State Q Γ k) :
    VariableWL.step P.compile (P.encodeState s)=(P.step s).map P.encodeState := by
  unfold VariableWL.step step
  change ((P.transition (controlDecode (controlCode s.control))
    (fun j => symbolDecode (symbolCode (s.cells j (s.heads j))))).map _).map _ = _
  simp only [control_roundtrip,symbol_roundtrip,Option.map_map]
  cases P.transition s.control (fun j => s.cells j (s.heads j)) with
  | none => rfl
  | some data =>
    apply congrArg some
    apply configuration_ext <;> try rfl
    funext j i
    change (if i=s.heads j then symbolCode (data.2 j).1 else symbolCode (s.cells j i)) =
      symbolCode (if i=s.heads j then (data.2 j).1 else s.cells j i)
    split_ifs <;> rfl

 theorem encode_run (P : Program Q Γ k) (w : Word) (t : ℕ) :
    VariableWL.run P.compile w t=P.encodeState (P.run w t) := by
  induction t with
  | zero => exact (P.encode_initial w).symm
  | succ t ih =>
    simp only [VariableWL.run,run,ih,P.encode_step]
    cases P.step (P.run w t) <;> rfl

 theorem compile_outputs (P : Program Q Γ k) {w out : Word} {T : ℕ}
    (h : P.OutputsWithin w out T) : VariableWL.OutputsWithin P.compile w out T := by
  obtain ⟨t,ht,halt,hout⟩ := h
  refine ⟨t,ht,?_,?_⟩
  · rw [P.encode_run,P.encode_step,halt]
    rfl
  · rw [P.encode_run]
    funext i
    change symbolCode ((P.run w t).cells 0 i)=wordCells _ out i
    rw [congrFun hout i]
    exact encodeWord out i

end
end Program
end VariableWL.Computation

namespace VariableWL.Computation

variable {Γ : Type}

 theorem typedWordCells_nil (i : ℤ) : typedWordCells (Γ:=Γ) [] i=none := by
  unfold typedWordCells
  split_ifs <;> rfl

 theorem typedWordCells_cons (b : Bool) (w : Word) (i : ℤ) :
    typedWordCells (Γ:=Γ) (b::w) i =
      if i=0 then bitSymbol b else typedWordCells w (i-1) := by
  by_cases hi : i=0
  · subst i
    rfl
  · rw [ite_eq_right hi]
    by_cases hn : i < 0
    · unfold typedWordCells
      rw [ite_eq_right (by omega),ite_eq_right (by omega)]
    · obtain ⟨n,hnat⟩ : ∃ n : ℕ, i=(n+1:ℕ) := by
        refine ⟨i.toNat-1,?_⟩
        have := Int.toNat_of_nonneg (by omega : 0 ≤ i)
        omega
      subst i
      unfold typedWordCells
      rw [ite_eq_left (by omega),ite_eq_left (by omega)]
      have hsub : ((n+1:ℕ):ℤ)-1=(n:ℤ) := by omega
      simp only [hsub,Int.toNat_natCast,List.getElem?_cons_succ]

 @[simp] theorem stackCells_nil (i : ℤ) : stackCells (Γ:=Γ) [] i=none :=
  typedWordCells_nil _

 theorem stackCells_cons (b : Bool) (w : Word) (i : ℤ) :
    stackCells (Γ:=Γ) (b::w) i =
      if i=stackHead w-1 then bitSymbol b else stackCells w i := by
  unfold stackCells
  rw [typedWordCells_cons]
  apply if_congr
  · simp only [List.length_cons,stackHead]
    omega
  · rfl
  · congr 1
    simp only [List.length_cons]
    omega

 theorem stackCells_head (w : Word) : stackCells (Γ:=Γ) w (stackHead w)=
    w.head?.bind bitSymbol := by
  cases w with
  | nil => simp
  | cons b w =>
    rw [stackCells_cons,ite_eq_left]
    · rfl
    · simp only [stackHead,List.length_cons]
      omega

 theorem stackCells_below (w : Word) (i : ℤ) (h : i < stackHead w) :
    stackCells (Γ:=Γ) w i=none := by
  unfold stackCells typedWordCells
  rw [ite_eq_right]
  unfold stackHead at h
  omega

namespace Stack

 theorem firstUpdate (a : Action) (w : Word) :
    stackHead w + (a.firstMove w.head?).displacement = stackHead (a.apply w) := by
  cases a <;> cases w <;>
    simp [stackHead,Action.firstMove,Action.apply,Motion.displacement]
  all_goals omega

 theorem secondUpdate (a : Action) (w : Word) (i : ℤ) :
    (if i=stackHead (a.apply w) then
      a.secondWrite (if stackHead (a.apply w)=stackHead w then
        a.firstWrite w.head? else stackCells w (stackHead (a.apply w)))
    else if i=stackHead w then a.firstWrite w.head? else stackCells (Γ:=Γ) w i) =
    stackCells (a.apply w) i := by
  cases a with
  | keep =>
    simp only [Action.apply,Action.secondWrite,Action.firstWrite,reduceCtorEq,ite_false,ite_true]
    split_ifs with h
    · subst i
      exact (stackCells_head w).symm
    · rfl
  | pop =>
    cases w with
    | nil => simp [Action.apply,Action.secondWrite,Action.firstWrite]
    | cons b w =>
      simp only [Action.apply,List.tail_cons,Action.secondWrite,Action.firstWrite,ite_true]
      have hh : stackHead (b::w)=stackHead w-1 := by
        simp only [stackHead,List.length_cons]; omega
      have hn : stackHead w ≠ stackHead w-1 := by omega
      simp only [hh,stackCells_cons,ite_eq_right hn]
      by_cases hi : i=stackHead w
      · subst i
        simp only [ite_true]
      · rw [ite_eq_right hi]
        by_cases hj : i=stackHead w-1
        · subst i
          simp only [ite_true]
          exact (stackCells_below w _ (by omega)).symm
        · simp only [ite_eq_right hj]
  | push b =>
    simp only [Action.apply,Action.secondWrite,Action.firstWrite,reduceCtorEq,ite_false]
    rw [stackCells_cons]
    have hh : stackHead (b::w)=stackHead w-1 := by
      simp only [stackHead,List.length_cons]; omega
    rw [hh]
    split_ifs with h₁ h₂
    · rfl
    · subst i
      exact (stackCells_head w).symm
    · rfl

variable {Q : Type} {k : ℕ}

 theorem Action.length_apply_le (a : Action) (w : Word) : (a.apply w).length ≤ w.length+1 := by
  cases a <;> cases w <;> simp [Action.apply]
  all_goals omega

 theorem Machine.length_run (M : Machine Q k) (w : Word) (t : ℕ) (j : Fin (k+1)) :
    ((M.run w t).tapes j).length ≤ w.length+t := by
  induction t with
  | zero =>
    dsimp [Machine.run,Machine.initial]
    split_ifs <;> simp
  | succ t ih =>
    simp only [Machine.run]
    unfold Machine.step
    cases h : M.transition (M.run w t).control (fun i => ((M.run w t).tapes i).head?) with
    | none => dsimp; omega
    | some d =>
      dsimp
      exact (Action.length_apply_le _ _).trans (by omega)

end Stack
end VariableWL.Computation

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_Stack
attribute [-instance] _root_.OAI.VariableWL.MachineReduction.comparisonFintype _root_.OAI.VariableWL.MachineReduction.realFintype _root_.OAI.VariableWL.MachineReduction.realNonempty _root_.OAI.VariableWL.MultiStack.instFintypeMotion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace VariableWL.Computation

variable {Q Γ : Type} {k : ℕ}

namespace Program
variable {Q Γ : Type} {k : ℕ}

 theorem evolve_add (P : Program Q Γ k) (s : State Q Γ k) (n m : ℕ) :
    P.evolve s (n+m)=P.evolve (P.evolve s n) m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change (P.step (P.evolve s (n+m))).getD (P.evolve s (n+m)) = _
    rw [ih]
    rfl

 theorem evolve_run (P : Program Q Γ k) (w : Word) (n : ℕ) :
    P.evolve (initial w) n=P.run w n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [evolve,run,ih]

 theorem evolve_one (P : Program Q Γ k) {s s' : State Q Γ k} (h : P.step s=some s') :
    P.evolve s 1=s' := by simp only [evolve,h,Option.getD_some]

end Program

 theorem state_ext {Q Γ : Type} {k : ℕ} {s t : State Q Γ k}
    (hc : s.control=t.control) (hh : s.heads=t.heads) (hs : s.cells=t.cells) : s=t := by
  cases s
  cases t
  congr

namespace Stack

 theorem step_eq_intermediate (P : Program Q Γ k) (s : Computation.State Q Γ k)
    (q : Option Q) (data : Fin (k+1) → Symbol Γ × Motion)
    (h : P.transition s.control (fun j => s.cells j (s.heads j))=some (q,data)) :
    P.step s=some (intermediate s q data) := by
  unfold Program.step
  rw [h]
  rfl

 theorem Machine.execute_two (M : Machine Q k) (s : State Q k)
    (q : Q) (acts : Fin (k+1) → Action)
    (h : M.transition s.control (fun j => (s.tapes j).head?)=some (q,acts)) :
    M.program.evolve (M.execState s) 2=
      M.execState ⟨q,fun j => (acts j).apply (s.tapes j)⟩ := by
  let data : Fin (k+2) → Symbol PUnit × Motion := Fin.cases (none,.stay)
    (fun j => ((acts j).firstWrite (s.tapes j).head?,
      (acts j).firstMove (s.tapes j).head?))
  let mid := intermediate (M.execState s) (some (.pending q acts)) data
  have hs : M.program.step (M.execState s)=some mid := by
    apply step_eq_intermediate
    dsimp only [Machine.program,Machine.execState]
    simp only [Fin.cases_succ,stackCells_head,readBit_bind,h]
    rfl
  have ht : M.program.step mid=some (M.execState ⟨q,fun j => (acts j).apply (s.tapes j)⟩) := by
    let data' : Fin (k+2) → Symbol PUnit × Motion :=
      Fin.cases (mid.cells 0 (mid.heads 0),.stay)
        (fun j => ((acts j).secondWrite (mid.cells j.succ (mid.heads j.succ)),.stay))
    have he : M.program.step mid=some (intermediate mid (some (.execute q)) data') := by
      apply step_eq_intermediate
      rfl
    rw [he]
    apply congrArg some
    apply state_ext
    · rfl
    · funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · change (stackHead (s.tapes j)+((acts j).firstMove _).displacement)+0 = _
        rw [add_zero,firstUpdate]
        rfl
    · funext i x
      refine Fin.cases ?_ (fun j => ?_) i
      · change (if x=0+0 then (if 0+0=0 then none else none)
          else if x=0 then none else none)=none
        simp only [ite_self]
      · change (if x=stackHead (s.tapes j)+((acts j).firstMove _).displacement then
          (acts j).secondWrite (if stackHead (s.tapes j)+((acts j).firstMove _).displacement=
            stackHead (s.tapes j) then (acts j).firstWrite _ else
            stackCells (s.tapes j) (stackHead (s.tapes j)+((acts j).firstMove _).displacement))
          else if x=stackHead (s.tapes j) then (acts j).firstWrite _ else stackCells (s.tapes j) x) = _
        rw [firstUpdate]
        exact secondUpdate _ _ _
  simp only [Program.evolve,hs,Option.getD_some,ht]

end Stack
end VariableWL.Computation

namespace VariableWL.Computation

variable {Q Γ : Type} {k : ℕ}

 theorem typedWordCells_snoc (w : Word) (b : Bool) (i : ℤ) :
    typedWordCells (Γ:=Γ) (w++[b]) i =
      if i=(w.length:ℤ) then bitSymbol b else typedWordCells w i := by
  induction w generalizing i with
  | nil =>
    rw [List.nil_append,typedWordCells_cons]
    simp only [typedWordCells_nil,List.length_nil,Nat.cast_zero]
  | cons a w ih =>
    rw [List.cons_append,typedWordCells_cons,typedWordCells_cons,ih]
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    split_ifs <;> first | rfl | (exfalso; omega)

namespace Stack

 theorem twoTapeUpdates (q qmid qfinal : Option Q) (h : ℤ) (c : ℤ → Symbol Γ)
    (ws : Fin (k+1) → Word) (io : Symbol Γ × Motion) (acts : Fin (k+1) → Action) :
    let mid := intermediate (tapeState q h c ws) qmid (firstData ws io acts)
    intermediate mid qfinal (secondData mid acts) =
      tapeState qfinal (h+io.2.displacement) (fun i => if i=h then io.1 else c i)
        (fun j => (acts j).apply (ws j)) := by
  dsimp only
  apply state_ext
  · rfl
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change h+io.2.displacement+0=h+io.2.displacement
      omega
    · change stackHead (ws j)+((acts j).firstMove _).displacement+0=stackHead _
      rw [add_zero,firstUpdate]
  · funext i x
    refine Fin.cases ?_ (fun j => ?_) i
    · change (if x=h+io.2.displacement then
        (if h+io.2.displacement=h then io.1 else c (h+io.2.displacement))
        else if x=h then io.1 else c x) = if x=h then io.1 else c x
      split_ifs <;> simp_all
    · change (if x=stackHead (ws j)+((acts j).firstMove _).displacement then
        (acts j).secondWrite (if stackHead (ws j)+((acts j).firstMove _).displacement=
          stackHead (ws j) then (acts j).firstWrite _ else
          stackCells (ws j) (stackHead (ws j)+((acts j).firstMove _).displacement))
        else if x=stackHead (ws j) then (acts j).firstWrite _ else stackCells (ws j) x) = _
      rw [firstUpdate]
      exact secondUpdate _ _ _

 theorem pushInput_apply (p : Word) (b : Bool) :
    (fun j : Fin (k+1) => (pushInput b j).apply (inputTapes p j))=inputTapes (p++[b]) := by
  funext j
  simp only [pushInput,inputTapes]
  split_ifs <;> simp [Action.apply,List.reverse_append]

 theorem inputCells_scan (p w : Word) (hp : 0 < p.length) :
    inputCells p w p.length=w.head?.bind bitSymbol := by
  unfold inputCells
  rw [ite_eq_right (by omega),sub_self]
  cases w <;> rfl

 theorem inputCells_blank (p : Word) (i : ℤ) : inputCells p [] i=
    if i=0 then marker else none := by
  simp only [inputCells,typedWordCells_nil]

 theorem inputCells_next (p w : Word) (b : Bool) (hp : 0 < p.length) (i : ℤ) :
    (if i=p.length then none else inputCells p (b::w) i)=inputCells (p++[b]) w i := by
  unfold inputCells
  rw [typedWordCells_cons]
  simp only [List.length_append,List.length_singleton,Nat.cast_add,Nat.cast_one]
  by_cases hz : i=0
  · subst i
    rw [ite_eq_right (by omega),ite_eq_left rfl,ite_eq_left rfl]
  · rw [ite_eq_right hz,ite_eq_right hz]
    by_cases hi : i=p.length
    · subst i
      rw [ite_eq_left rfl]
      have : (p.length:ℤ)-((p.length:ℤ)+1) = -1 := by omega
      rw [this]
      unfold typedWordCells
      rfl
    · rw [ite_eq_right hi,ite_eq_right (by omega)]
      congr 1
      omega

 theorem Machine.loading_two (M : Machine Q k) (p w : Word) (b : Bool) (hp : 0 < p.length) :
    M.program.evolve (M.loading p (b::w)) 2=M.loading (p++[b]) w := by
  let io : Symbol PUnit × Motion := (none,.right)
  let mid := intermediate (M.loading p (b::w)) (some (.put b))
    (firstData (inputTapes p) io (pushInput b))
  have hs : M.program.step (M.loading p (b::w))=some mid := by
    apply step_eq_intermediate
    dsimp only [Machine.program,Machine.loading,tapeState]
    simp only [Fin.cases_zero,inputCells_scan p _ hp,List.head?_cons,Option.bind_some,readBit_bit]
    congr 1
    funext j
    change (stackCells (inputTapes p j) (stackHead (inputTapes p j)),
      if j=0 then Motion.left else .stay) = _
    rw [stackCells_head]
    dsimp only [pushInput]
    split_ifs <;> rfl
  have ht : M.program.step mid=some (intermediate mid (some .read) (secondData mid (pushInput b))) := by
    apply step_eq_intermediate
    dsimp only [Machine.program,mid,intermediate]
    congr 1
    funext j
    dsimp only [pushInput]
    split_ifs <;> rfl
  simp only [Program.evolve,hs,Option.getD_some,ht]
  rw [show mid=intermediate (tapeState (some .read) p.length (inputCells p (b::w))
      (inputTapes p)) (some (.put b)) (firstData (inputTapes p) io (pushInput b)) from rfl]
  rw [twoTapeUpdates,pushInput_apply]
  apply state_ext
  · rfl
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change (p.length:ℤ)+1=((p++[b]).length:ℤ)
      simp only [List.length_append,List.length_singleton,Nat.cast_add,Nat.cast_one]
    · rfl
  · funext i x
    refine Fin.cases ?_ (fun j => ?_) i
    · exact inputCells_next p w b hp x
    · rfl

end Stack
end VariableWL.Computation

namespace VariableWL.Computation.Stack

variable {Q : Type} {k : ℕ}

 theorem initial_tapeState (w : Word) :
    Program.initial (Q:=Control Q k) (Γ:=PUnit) (k:=k+1) w =
    tapeState none 0 (typedWordCells w) (inputTapes []) := by
  apply state_ext
  · rfl
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change (0:ℤ)=stackHead (inputTapes [] j)
      simp [inputTapes,stackHead]
  · funext i x
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change (if j.succ=0 then typedWordCells w else fun _ => none) x=stackCells (inputTapes [] j) x
      rw [ite_eq_right (Fin.succ_ne_zero j)]
      simp [inputTapes]

 theorem Machine.initial_two (M : Machine Q k) (b : Bool) (w : Word) :
    M.program.evolve (Program.initial (b::w)) 2=M.loading [b] w := by
  rw [initial_tapeState]
  let start : Computation.State (Control Q k) PUnit (k+1) := tapeState (none : Option (Control Q k)) 0 (typedWordCells (b::w)) (inputTapes [])
  let io : Symbol PUnit × Motion := (marker,.right)
  let mid := intermediate start (some (.put b)) (firstData (inputTapes []) io (pushInput b))
  have hs : M.program.step start=some mid := by
    apply step_eq_intermediate
    change instruction (Control.put (Q:=Q) (k:=k) b) (marker,.right)
      (fun j => (stackCells (inputTapes [] j) (stackHead (inputTapes [] j)),
        if j=0 then Motion.left else .stay)) = _
    congr 1
    funext j
    rw [stackCells_head]
    dsimp only [pushInput]
    split_ifs <;> rfl
  have ht : M.program.step mid=some (intermediate mid (some .read) (secondData mid (pushInput b))) := by
    apply step_eq_intermediate
    dsimp only [Machine.program,mid,intermediate]
    congr 1
    funext j
    dsimp only [pushInput]
    split_ifs <;> rfl
  change M.program.evolve start 2=_
  simp only [Program.evolve,hs,Option.getD_some,ht]
  rw [show mid=intermediate start (some (.put b)) (firstData (inputTapes []) io (pushInput b)) from rfl]
  rw [show start=tapeState (none : Option (Control Q k)) 0 (typedWordCells (b::w)) (inputTapes []) from rfl]
  rw [twoTapeUpdates,pushInput_apply]
  apply state_ext
  · rfl
  · rfl
  · funext i x
    refine Fin.cases ?_ (fun j => ?_) i
    · change (if x=0 then marker else typedWordCells (b::w) x)=inputCells [b] w x
      rw [typedWordCells_cons]
      unfold inputCells
      simp only [List.length_singleton,Nat.cast_one]
      split_ifs <;> rfl
    · rfl

 theorem Machine.loading_all (M : Machine Q k) (p w : Word) (hp : 0 < p.length) :
    M.program.evolve (M.loading p w) (2*w.length)=M.loading (p++w) [] := by
  induction w generalizing p with
  | nil => simp only [List.length_nil,mul_zero,Program.evolve,List.append_nil]
  | cons b w ih =>
    have he : 2*(b::w).length=2+2*w.length := by simp only [List.length_cons]; omega
    rw [he,Program.evolve_add,M.loading_two p w b hp]
    rw [ih (p++[b]) (by simp only [List.length_append,List.length_singleton]; omega)]
    simp only [List.append_assoc,List.singleton_append]

 theorem Machine.back_zero (M : Machine Q k) (ws : Fin (k+1) → Word) :
    M.program.step (M.backState 0 ws)=some (M.execState ⟨M.start,ws⟩) := by
  unfold Program.step
  change (instruction (Control.execute (k:=k) M.start) (none,.stay)
    (fun j => (stackCells (ws j) (stackHead (ws j)),.stay))).map _ = _
  apply congrArg some
  apply state_ext
  · rfl
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact add_zero _
  · funext i x
    refine Fin.cases ?_ (fun j => ?_) i
    · change (if x=0 then none else if x=0 then marker else none)=none
      split_ifs <;> rfl
    · change (if x=stackHead (ws j) then stackCells (ws j) (stackHead (ws j))
        else stackCells (ws j) x)=stackCells (ws j) x
      split_ifs with h
      · rw [h]
      · rfl

 theorem Machine.back_succ (M : Machine Q k) (n : ℕ) (ws : Fin (k+1) → Word) :
    M.program.step (M.backState (n+1) ws)=some (M.backState n ws) := by
  have hz : ((n+1:ℕ):ℤ)≠0 := by omega
  unfold Program.step
  dsimp only [Machine.program,Machine.backState,tapeState,Fin.cases_zero]
  rw [ite_eq_right hz]
  apply congrArg some
  apply state_ext
  · rfl
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change ((n+1:ℕ):ℤ)+(-1)=(n:ℤ)
      omega
    · exact add_zero _
  · funext i x
    refine Fin.cases ?_ (fun j => ?_) i
    · change (if x=((n+1:ℕ):ℤ) then none else if x=0 then marker else none)=
        if x=0 then marker else none
      split_ifs <;> first | rfl | (exfalso; omega)
    · change (if x=stackHead (ws j) then stackCells (ws j) (stackHead (ws j))
        else stackCells (ws j) x)=stackCells (ws j) x
      split_ifs with h
      · rw [h]
      · rfl

 theorem Machine.back_all (M : Machine Q k) (n : ℕ) (ws : Fin (k+1) → Word) :
    M.program.evolve (M.backState n ws) (n+1)=M.execState ⟨M.start,ws⟩ := by
  induction n with
  | zero => exact M.program.evolve_one (M.back_zero ws)
  | succ n ih =>
    rw [show n+1+1=1+(n+1) by omega,Program.evolve_add]
    rw [M.program.evolve_one (M.back_succ n ws),ih]

 theorem Machine.loading_end (M : Machine Q k) (p : Word) (hp : 0 < p.length) :
    M.program.step (M.loading p [])=some (M.backState (p.length-1) (inputTapes p)) := by
  unfold Program.step
  dsimp only [Machine.program,Machine.loading,tapeState,Fin.cases_zero]
  rw [inputCells_scan p [] hp]
  change (instruction (Control.back : Control Q k) (none,.left)
    (fun j => (stackCells (inputTapes p j) (stackHead (inputTapes p j)),.stay))).map _ = _
  apply congrArg some
  apply state_ext
  · rfl
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change (p.length:ℤ)+(-1)=((p.length-1:ℕ):ℤ)
      omega
    · exact add_zero _
  · funext i x
    refine Fin.cases ?_ (fun j => ?_) i
    · change (if x=p.length then none else inputCells p [] x)=if x=0 then marker else none
      rw [inputCells_blank]
      split_ifs <;> first | rfl | (exfalso; omega)
    · change (if x=stackHead (inputTapes p j) then stackCells (inputTapes p j) (stackHead (inputTapes p j))
        else stackCells (inputTapes p j) x)=stackCells (inputTapes p j) x
      split_ifs with h
      · rw [h]
      · rfl

 theorem Machine.initial_empty (M : Machine Q k) :
    M.program.evolve (Program.initial []) 1=M.execState (M.initial []) := by
  apply Program.evolve_one
  rw [initial_tapeState]
  unfold Program.step
  change (instruction (Control.execute (k:=k) M.start) (none,.stay)
    (fun j => (stackCells (inputTapes [] j) (stackHead (inputTapes [] j)),.stay))).map _ = _
  apply congrArg some
  apply state_ext
  · rfl
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact add_zero _
  · funext i x
    refine Fin.cases ?_ (fun j => ?_) i
    · change (if x=0 then none else typedWordCells [] x)=none
      simp only [typedWordCells_nil,ite_self]
    · change (if x=stackHead (inputTapes [] j) then stackCells (inputTapes [] j) (stackHead (inputTapes [] j))
        else stackCells (inputTapes [] j) x)=stackCells (inputTapes [] j) x
      split_ifs with h
      · rw [h]
      · rfl

 theorem Machine.initialize_ (M : Machine Q k) (w : Word) :
    M.program.run w (3*w.length+1)=M.execState (M.initial w) := by
  rw [← Program.evolve_run]
  cases w with
  | nil => exact M.initial_empty
  | cons b w =>
    have hn : 3*(b::w).length+1=2+(2*w.length+(1+(w.length+1))) := by
      simp only [List.length_cons]; omega
    rw [hn,Program.evolve_add,M.initial_two,Program.evolve_add,
      M.loading_all [b] w (by simp),Program.evolve_add]
    rw [M.program.evolve_one (M.loading_end ([b]++w) (by simp)),
      show ([b]++w).length-1=w.length by simp,M.back_all]
    rfl

end VariableWL.Computation.Stack

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_OneHead
attribute [-instance] _root_.OAI.VariableWL.MachineReduction.comparisonFintype _root_.OAI.VariableWL.MachineReduction.realFintype _root_.OAI.VariableWL.MachineReduction.realNonempty _root_.OAI.VariableWL.MultiStack.instFintypeMotion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9 uVariable10

namespace VariableWL.Computation

variable {Q Γ : Type} {k : ℕ}

 theorem stackCells_pop (b : Bool) (w : Word) (i : ℤ) :
    (if i=stackHead (b::w) then none else stackCells (Γ:=Γ) (b::w) i)=stackCells w i := by
  rw [stackCells_cons]
  have hh : stackHead (b::w)=stackHead w-1 := by
    simp only [stackHead,List.length_cons]; omega
  rw [hh]
  split_ifs with h
  · subst i
    exact (stackCells_below w _ (by omega)).symm
  · rfl

namespace Stack

 theorem Machine.output_step (M : Machine Q k) (p remaining : Word) (b : Bool) (ws : Fin (k+1) → Word) :
    M.program.step (M.outputState p (b::remaining) ws)=some (M.outputState (p++[b]) remaining ws) := by
  unfold Program.step
  dsimp only [Machine.program,Machine.outputState,tapeState,Fin.cases_succ]
  rw [stackCells_head,Function.update_self,List.head?_cons,Option.bind_some,readBit_bit]
  apply congrArg some
  apply state_ext
  · rfl
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change (p.length:ℤ)+1=((p++[b]).length:ℤ)
      simp only [List.length_append,List.length_singleton,Nat.cast_add,Nat.cast_one]
    · change stackHead (Function.update ws M.output (b::remaining) j)+
        (if j=M.output then Motion.right else .stay).displacement=
        stackHead (Function.update ws M.output remaining j)
      by_cases h : j=M.output
      · subst j
        simp only [Function.update_self,ite_true,Motion.displacement,stackHead,List.length_cons]
        omega
      · simp only [Function.update_of_ne h,ite_eq_right h,Motion.displacement,add_zero]
  · funext i x
    refine Fin.cases ?_ (fun j => ?_) i
    · change (if x=p.length then bitSymbol b else typedWordCells p x)=typedWordCells (p++[b]) x
      exact (typedWordCells_snoc p b x).symm
    · change (if x=stackHead (Function.update ws M.output (b::remaining) j) then
        (if j=M.output then none else stackCells (Function.update ws M.output (b::remaining) j)
          (stackHead (Function.update ws M.output (b::remaining) j)))
        else stackCells (Function.update ws M.output (b::remaining) j) x)=
        stackCells (Function.update ws M.output remaining j) x
      by_cases h : j=M.output
      · subst j
        simp only [Function.update_self,ite_true]
        exact stackCells_pop b remaining x
      · simp only [Function.update_of_ne h,ite_eq_right h]
        split_ifs with hx
        · rw [hx]
        · rfl

 theorem Machine.output_all (M : Machine Q k) (p remaining : Word) (ws : Fin (k+1) → Word) :
    M.program.evolve (M.outputState p remaining ws) remaining.length=
      M.outputState (p++remaining) [] ws := by
  induction remaining generalizing p with
  | nil => simp only [List.length_nil,Program.evolve,List.append_nil]
  | cons b remaining ih =>
    rw [show (b::remaining).length=1+remaining.length by simp only [List.length_cons]; omega,
      Program.evolve_add,M.program.evolve_one (M.output_step p remaining b ws),ih]
    simp only [List.append_assoc,List.singleton_append]

 theorem Machine.output_halt (M : Machine Q k) (p : Word) (ws : Fin (k+1) → Word) :
    M.program.step (M.outputState p [] ws)=none := by
  unfold Program.step
  dsimp only [Machine.program,Machine.outputState,tapeState,Fin.cases_succ]
  rw [Function.update_self,stackCells_nil]
  rfl

 theorem Machine.execute_halt (M : Machine Q k) (s : State Q k) (h : M.step s=none) :
    M.program.step (M.execState s)=some (M.outputState [] (s.tapes M.output) s.tapes) := by
  have ht : M.transition s.control (fun j => (s.tapes j).head?)=none := by
    unfold Machine.step at h
    exact Option.map_eq_none_iff.mp h
  unfold Program.step
  dsimp only [Machine.program,Machine.execState,Fin.cases_succ]
  rw [show (fun j => readBit (stackCells (s.tapes j) (stackHead (s.tapes j))))=
      (fun j => (s.tapes j).head?) by funext j; rw [stackCells_head,readBit_bind],ht]
  apply congrArg some
  apply state_ext
  · rfl
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change stackHead (s.tapes j)+0=stackHead ((Function.update s.tapes M.output (s.tapes M.output)) j)
      rw [Function.update_eq_self,add_zero]
  · funext i x
    refine Fin.cases ?_ (fun j => ?_) i
    · change (if x=0 then none else none)=typedWordCells [] x
      simp only [ite_self,typedWordCells_nil]
    · change (if x=stackHead (s.tapes j) then stackCells (s.tapes j) (stackHead (s.tapes j))
        else stackCells (s.tapes j) x)=stackCells ((Function.update s.tapes M.output (s.tapes M.output)) j) x
      rw [Function.update_eq_self]
      split_ifs with hx
      · rw [hx]
      · rfl

 theorem Machine.execute_run (M : Machine Q k) (w : Word) (t : ℕ)
    (hno : ∀ u < t, M.step (M.run w u)≠none) :
    M.program.evolve (M.execState (M.initial w)) (2*t)=M.execState (M.run w t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have ih' := ih (fun u hu => hno u (by omega))
    have hne := hno t (by omega)
    unfold Machine.step at hne
    have htrans : M.transition (M.run w t).control (fun j => ((M.run w t).tapes j).head?)≠none := by
      intro he
      apply hne
      rw [he]
      rfl
    obtain ⟨⟨q,acts⟩,ht⟩ := Option.ne_none_iff_exists'.mp htrans
    rw [show 2*(t+1)=2*t+2 by omega,Program.evolve_add,ih',M.execute_two (M.run w t) q acts ht]
    simp only [Machine.run,Machine.step,ht,Option.map_some,Option.getD_some]

 theorem Machine.compile_outputs (M : Machine Q k) {w out : Word} {T : ℕ}
    (h : M.OutputsWithin w out T) :
    M.program.OutputsWithin w out (4*(w.length+T+1)) := by
  obtain ⟨t,ht,halt,hout⟩ := h
  let haltPred := fun n => M.step (M.run w n)=none
  have hex : ∃ n, haltPred n := ⟨t,halt⟩
  let t₀ := Nat.find hex
  have ht₀ : t₀ ≤ t := Nat.find_min' hex halt
  have hstop : M.step (M.run w t₀)=none := Nat.find_spec hex
  have hn : ∀ u < t₀, M.step (M.run w u)≠none := by
    intro u hu
    exact Nat.find_min hex hu
  have stable {a : ℕ} (ha : M.step (M.run w a)=none) (n : ℕ) :
      M.run w (a+n)=M.run w a := by
    induction n with
    | zero => rfl
    | succ n ih =>
      change (M.step (M.run w (a+n))).getD (M.run w (a+n))=_
      rw [ih,ha]
      rfl
  have hout₀ : (M.run w t₀).tapes M.output=out := by
    have hs := stable hstop (t-t₀)
    rw [Nat.add_sub_of_le ht₀] at hs
    rw [← hs]
    exact hout
  have hlen : out.length ≤ w.length+t₀ := by
    rw [← hout₀]
    exact M.length_run w t₀ M.output
  let elapsed := 3*w.length+1+(2*t₀+(1+out.length))
  have hr : M.program.run w elapsed=M.outputState out [] (M.run w t₀).tapes := by
    rw [← Program.evolve_run]
    unfold elapsed
    rw [Program.evolve_add,Program.evolve_run,M.initialize_,Program.evolve_add,
      M.execute_run w t₀ hn,Program.evolve_add,
      M.program.evolve_one (M.execute_halt (M.run w t₀) hstop),hout₀,M.output_all]
    rfl
  refine ⟨elapsed,by unfold elapsed; omega,?_,?_⟩
  · rw [hr]
    exact M.output_halt _ _
  · rw [hr]
    rfl

 theorem Machine.outputs_compile [Fintype Q] (M : Machine Q k) {w out : Word} {T : ℕ}
    (h : M.OutputsWithin w out T) :
    VariableWL.OutputsWithin M.compile w out (4*(w.length+T+1)) :=
  M.program.compile_outputs (M.compile_outputs h)

end Stack
end VariableWL.Computation

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_StackSimulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9 uVariable10 uVariable11 uVariable12 uVariable13 uVariable14 uVariable15 uVariable16 uVariable17 uVariable18 uVariable19

namespace VariableWL.BoundedSimulation

namespace Steps
variable {S : Type uVariable10} {f : S → Option S} {a b c : S} {n m : ℕ}
theorem trans (h : Steps f n a b) (h' : Steps f m b c) : Steps f (n+m) a c := by
  induction h with
  | zero => simpa only [Nat.zero_add] using h'
  | @succ n a b c hab h ih => simpa only [Nat.succ_add] using Steps.succ hab (ih h')

theorem single (h : f a=some b) : Steps f 1 a b := Steps.succ h (Steps.zero b)

theorem tail (h : Steps f n a b) (h' : f b=some c) : Steps f (n+1) a c := h.trans (single h')

theorem head (h : f a=some b) (h' : Steps f n b c) : Steps f (n+1) a c := Steps.succ h h'
end Steps

theorem evolve_add {S : Type uVariable12} (f : S → Option S) (a : S) (n m : ℕ) :
    evolve f a (n+m)=evolve f (evolve f a n) m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change (f (evolve f a (n+m))).getD (evolve f a (n+m))=
      (f (evolve f (evolve f a n) m)).getD (evolve f (evolve f a n) m)
    rw [ih]

theorem Steps.evolve {S : Type uVariable13} {f : S → Option S} {n : ℕ} {a b : S}
    (h : Steps f n a b) : evolve f a n=b := by
  induction h with
  | zero => rfl
  | @succ n a b c hab h ih =>
    rw [Nat.add_comm,evolve_add]
    have he : BoundedSimulation.evolve f a 1=b := by change (f a).getD a=b; rw [hab]; rfl
    rw [he]
    exact ih

end VariableWL.BoundedSimulation

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_Encoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace VariableWL.Computation.Stack
open VariableWL.BoundedSimulation

namespace Code
variable {k : ℕ}

theorem machine_step (C : Code k) (o : Fin (k+1)) : (C.machine o).step=C.step := rfl

theorem lift_steps {A B : Code k} (f : A.Control → B.Control)
    (hf : ∀ q h q' u, A.transition q h=some (q',u) → B.transition (f q) h=some (f q',u))
    {s t : State A.Control k} {n : ℕ} (hst : Steps A.step n s t) :
    Steps B.step n (liftState f s) (liftState f t) := by
  induction hst with
  | zero => exact Steps.zero _
  | @succ n s t u hst htu ih =>
    apply Steps.succ ?_ ih
    unfold step at hst ⊢
    cases ht : A.transition s.control (heads s.tapes) with
    | none => simp [ht] at hst
    | some data =>
      rcases data with ⟨q,a⟩
      simp only [ht,Option.map_some,Option.some.injEq] at hst
      subst t
      change (B.transition (f s.control) (heads s.tapes)).map _ = _
      rw [hf _ _ _ _ ht]
      rfl

 theorem eval_steps {C : Code k} {s t : Stores k} {n : ℕ} (h : Eval C s n t) :
    ∃ q, Steps C.step n ⟨C.start,s⟩ ⟨q,t⟩ ∧ C.transition q (heads t)=none := by
  induction h with
  | skip s => exact ⟨(),Steps.zero _,rfl⟩
  | action a s => exact ⟨true,Steps.single rfl,rfl⟩
  | @seq a b s t u n m ha hb ia ib =>
    obtain ⟨qa,hqa,hhalt⟩ := ia
    obtain ⟨qb,hqb,hhaltb⟩ := ib
    refine ⟨.inr qb,?_,?_⟩
    · have hleft := lift_steps (B := .seq a b) Sum.inl
        (by intro q h q' v hv; simp only [transition,hv]) hqa
      have hcross : (Code.seq a b).step ⟨.inl qa,t⟩=some ⟨.inr b.start,t⟩ := by
        simp only [step,transition,hhalt,Option.map_some,execute_nop]
      have hright := lift_steps (B := .seq a b) Sum.inr
        (by intro q h q' v hv; simp only [transition,hv,Option.map_some]) hqb
      exact (hleft.tail hcross).trans hright
    · simp only [transition,hhaltb,Option.map_none]
  | @branch_true p a b s t n hp ha ih =>
    obtain ⟨q,hq,hh⟩ := ih
    refine ⟨.inr (.inl q),?_,?_⟩
    · have hbody := lift_steps (B := .branch p a b) (fun q => Sum.inr (Sum.inl q))
        (by intro q h q' u hu; simp only [transition,hu,Option.map_some]) hq
      exact hbody.head (by simp [step,start,transition,hp,liftState])
    · simp only [transition,hh,Option.map_none]
  | @branch_false p a b s t n hp ha ih =>
    obtain ⟨q,hq,hh⟩ := ih
    refine ⟨.inr (.inr q),?_,?_⟩
    · have hbody := lift_steps (B := .branch p a b) (fun q => Sum.inr (Sum.inr q))
        (by intro q h q' u hu; simp only [transition,hu,Option.map_some]) hq
      exact hbody.head (by simp [step,start,transition,hp,liftState])
    · simp only [transition,hh,Option.map_none]
  | loop_false hp => exact ⟨.inl (),Steps.zero _,by simp [transition,hp]⟩
  | @loop_true p a s t u n m hp ha hb ia ib =>
    obtain ⟨qa,hqa,hhalta⟩ := ia
    obtain ⟨qb,hqb,hhaltb⟩ := ib
    refine ⟨qb,?_,hhaltb⟩
    have hbody := lift_steps (B := .loop p a) Sum.inr
      (by intro q h q' v hv; simp only [transition,hv]) hqa
    have hin : (Code.loop p a).step ⟨.inl (),s⟩=some ⟨.inr a.start,s⟩ := by
      simp [step,transition,hp]
    have hout : (Code.loop p a).step ⟨.inr qa,t⟩=some ⟨.inl (),t⟩ := by
      simp only [step,transition,hhalta,Option.map_some,execute_nop]
    exact ((hbody.head hin).tail hout).trans hqb

 theorem eval_outputs (C : Code k) (o : Fin (k+1)) (w : Word) {t : Stores k} {n : ℕ}
    (h : Eval C (fun j => if j=0 then w.reverse else []) n t) :
    VariableWL.OutputsWithin (C.machine o).compile w (t o) (4*(w.length+n+1)) := by
  obtain ⟨q,hq,hh⟩ := eval_steps h
  apply Machine.outputs_compile
  have hr : (C.machine o).run w n=⟨q,t⟩ := by
    have he := hq.evolve
    have hrun (i) : (C.machine o).run w i=BoundedSimulation.evolve C.step ⟨C.start,fun j => if j=0 then w.reverse else []⟩ i := by
      induction i with
      | zero => rfl
      | succ i ih => change ((C.machine o).step _).getD _=_; rw [machine_step,ih]; rfl
    rw [hrun]
    exact he
  refine ⟨n,le_rfl,?_,?_⟩
  · rw [hr,machine_step]
    simp only [step,hh,Option.map_none]
  · rw [hr]
    rfl

end Code
end VariableWL.Computation.Stack

namespace VariableWL.Encoding
attribute [local instance] Classical.propDecidable

theorem header_code (n : ℕ) (v : Word) : header (List.replicate n true ++ false::v)=some (n,v) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ,List.cons_append,header,ih,Option.map_some]

 theorem header_sound {w v : Word} {n : ℕ} (h : header w=some (n,v)) :
    w=List.replicate n true ++ false::v := by
  induction w generalizing n with
  | nil => cases h
  | cons b w ih =>
    cases b with
    | false => simp only [header,Option.some.injEq,Prod.mk.injEq] at h; rcases h with ⟨rfl,rfl⟩; rfl
    | true =>
      simp only [header,Option.map_eq_some_iff] at h
      obtain ⟨⟨m,u⟩,hm,he⟩ := h
      cases he
      rw [ih hm,List.replicate_succ,List.cons_append]

 theorem integer_code (n : ℕ) (v : Word) : integer (integerCode n ++ v)=some (n,v) := by
  unfold integerCode
  simp only [List.append_assoc,List.singleton_append]
  change integer (List.replicate n.bits.length true ++ false::(n.bits++v))=_
  unfold integer
  rw [header_code]
  simp only [List.length_append,Nat.le_add_right,ite_true,
    List.take_left,value_bits,List.drop_left]

 theorem integer_sound {w v : Word} {n : ℕ} (h : integer w=some (n,v)) : w=integerCode n++v := by
  unfold integer at h
  cases hh : header w with
  | none => simp [hh] at h
  | some q =>
    rcases q with ⟨m,u⟩
    simp only [hh] at h
    split_ifs at h with hm hb
    · simp only [Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      rw [header_sound hh]
      have hlen : (u.take m).length=m := List.length_take_of_le hm
      simp only [integerCode,hb,hlen,List.append_assoc,List.cons_append]
      rw [List.take_append_drop,List.nil_append]

 theorem integer_prefix_injective {n m : ℕ} {u v : Word}
    (h : integerCode n++u=integerCode m++v) : n=m ∧ u=v := by
  have he := congrArg integer h
  rw [integer_code,integer_code] at he
  exact Prod.mk.inj (Option.some.inj he)

 theorem matrix_flat (G : Graph) : matrix G =
    (List.ofFn fun i : Fin G.order => List.ofFn fun j : Fin G.order => decide (G.graph.Adj i j)).flatten := by
  classical
  unfold matrix
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have hn : 0 < G.order := Nat.zero_lt_of_lt i.isLt
  have hd : (⟨i.val*G.order+j.val,by have := Nat.mul_le_mul_right G.order (Nat.succ_le_of_lt i.isLt); nlinarith [j.isLt]⟩ : Fin (G.order*G.order)).divNat=i := by
    apply Fin.ext
    simp [Fin.divNat,Nat.add_div,Nat.div_eq_of_lt j.isLt,hn,Nat.mod_lt _ hn]
  have hm : (⟨i.val*G.order+j.val,by have := Nat.mul_le_mul_right G.order (Nat.succ_le_of_lt i.isLt); nlinarith [j.isLt]⟩ : Fin (G.order*G.order)).modNat=j := by
    apply Fin.ext
    simp [Fin.modNat,Nat.add_mod,Nat.mod_eq_of_lt j.isLt]
  rw [hd,hm]

 theorem graphCode_eq (G : Graph) : graphCode G=integerCode G.order++matrix G := by
  rw [matrix_flat]
  rfl

 theorem graph_prefix_injective {G H : Graph} {u v : Word}
    (h : graphCode G++u=graphCode H++v) : G=H ∧ u=v := by
  classical
  rw [graphCode_eq,graphCode_eq,List.append_assoc,List.append_assoc] at h
  obtain ⟨hn,ht⟩ := integer_prefix_injective h
  rcases G with ⟨n,g⟩
  rcases H with ⟨m,hg⟩
  change n=m at hn
  subst m
  obtain ⟨hm,hu⟩ := List.append_inj ht (by simp)
  refine ⟨?_,hu⟩
  have hadj : g.Adj=hg.Adj := by
    funext i j
    have hf := List.ofFn_inj.mp hm
    let p : Fin (n*n) := ⟨i.val*n+j.val,by nlinarith [i.isLt,j.isLt]⟩
    have hp := congrFun hf p
    have hn : 0<n := Nat.zero_lt_of_lt i.isLt
    have hd : p.divNat=i := by apply Fin.ext; simp [p,Fin.divNat,Nat.add_div,Nat.div_eq_of_lt j.isLt,hn,Nat.mod_lt _ hn]
    have hmod : p.modNat=j := by apply Fin.ext; simp [p,Fin.modNat,Nat.add_mod,Nat.mod_eq_of_lt j.isLt]
    change decide (g.Adj p.divNat p.modNat)=decide (hg.Adj p.divNat p.modNat) at hp
    rw [hd,hmod] at hp
    exact propext (by simpa only [decide_eq_decide] using hp)
  have hgEq := SimpleGraph.ext hadj
  subst hg
  rfl

 theorem pair_injective {G H G' H' : Graph} {k k' : ℕ}
    (h : pairCode G H k=pairCode G' H' k') : G=G' ∧ H=H' ∧ k=k' := by
  unfold pairCode at h
  rw [List.append_assoc,List.append_assoc] at h
  obtain ⟨hg,ht⟩ := graph_prefix_injective h
  obtain ⟨hh,hk⟩ := graph_prefix_injective ht
  have hi := integer_prefix_injective (u := []) (v := []) (by simpa using hk)
  exact ⟨hg,hh,hi.1⟩

 theorem pair_mem_WL (G H : Graph) (k : ℕ) : pairCode G H k ∈ WL ↔ 2≤k ∧ Equivalent G H k := by
  constructor
  · rintro ⟨G',H',k',he,hk,hh⟩
    obtain ⟨rfl,rfl,rfl⟩ := pair_injective he
    exact ⟨hk,hh⟩
  · rintro ⟨hk,hh⟩
    exact ⟨G,H,k,rfl,hk,hh⟩

 theorem pair_mem_SubWL (G H : Graph) (k : ℕ) : pairCode G H k ∈ SubWL ↔
    2≤k ∧ 0<G.order ∧ G.order=H.order ∧ G.graph.Connected ∧ H.graph.Connected ∧
      Subcubic G ∧ Subcubic H ∧ Equivalent G H k := by
  constructor
  · rintro ⟨G',H',k',he,hh⟩
    obtain ⟨rfl,rfl,rfl⟩ := pair_injective he
    exact hh
  · intro hh
    exact ⟨G,H,k,rfl,hh⟩

end VariableWL.Encoding

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_RefinementTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace VariableWL.RefinementTable
attribute [local instance] Classical.propDecidable

theorem sameCounts_iff {α β : Type} [DecidableEq β] (f : α → β)
    (eq : α → α → Bool) (heq : ∀ a b, eq a b=true ↔ f a=f b) (xs ys : List α) :
    sameCounts eq xs ys=true ↔ (xs.map f : Multiset β)=(ys.map f : Multiset β) := by
  have hcount (a) (zs : List α) : (zs.filter (eq a)).length=(zs.map f).count (f a) := by
    induction zs with
    | nil => rfl
    | cons b zs ih =>
      by_cases h : f a=f b
      · have he : eq a b=true := (heq a b).mpr h
        simp [he,h,ih]
      · have he : eq a b=false := Bool.eq_false_iff.mpr (fun hb => h ((heq a b).mp hb))
        simp [he,Ne.symm h,ih]
  simp only [sameCounts,List.all_eq_true,decide_eq_true_eq]
  constructor
  · intro h
    apply Multiset.ext.mpr
    intro b
    by_cases hb : b ∈ xs.map f ∨ b ∈ ys.map f
    · rcases hb with hb|hb
      · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
        simpa only [Multiset.coe_count,← hcount] using h a (List.mem_append_left ys ha)
      · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
        simpa only [Multiset.coe_count,← hcount] using h a (List.mem_append_right xs ha)
    · have hx : b ∉ xs.map f := fun hx => hb (.inl hx)
      have hy : b ∉ ys.map f := fun hy => hb (.inr hy)
      simp only [Multiset.coe_count,List.count_eq_zero.mpr hx,List.count_eq_zero.mpr hy]
  · intro h a _
    rw [hcount,hcount]
    simpa only [Multiset.coe_count] using congrArg (Multiset.count (f a)) h

variable (G H : Graph) (k : ℕ)

 theorem vectorEqual_iff (R : Entry G H k → Entry G H k → Bool) (s : ℕ)
    (hr : ∀ a b, R a b=true ↔ tagColor G H k s a=tagColor G H k s b)
    (x y : Vector G H k) : vectorEqual G H k R x y=true ↔
      (fun i => tagColor G H k s (x i))=(fun i => tagColor G H k s (y i)) := by
  simp only [vectorEqual,List.all_eq_true,List.mem_finRange,forall_const,hr,funext_iff]

 theorem neighbors_color (x : Entry G H k) (s : ℕ) :
    ((neighbors G H k x).map (fun a i => tagColor G H k s (a i)) : Multiset (Fin k → Color k s)) =
      (tagColor G H k (s+1) x).2 := by
  classical
  cases x with
  | inl v =>
    rw [neighbors,List.map_ofFn]
    change (List.ofFn (fun z : Fin G.order => fun i => color G k s (Function.update v i z)) : Multiset (Fin k → Color k s)) = Finset.univ.val.map (fun z : Fin G.order => fun i => color G k s (Function.update v i z))
    exact (Fin.univ_val_map _).symm
  | inr v =>
    rw [neighbors,List.map_ofFn]
    change (List.ofFn (fun z : Fin H.order => fun i => color H k s (Function.update v i z)) : Multiset (Fin k → Color k s)) = Finset.univ.val.map (fun z : Fin H.order => fun i => color H k s (Function.update v i z))
    exact (Fin.univ_val_map _).symm

 theorem update_correct (R : Entry G H k → Entry G H k → Bool) (s : ℕ)
    (hr : ∀ a b, R a b=true ↔ tagColor G H k s a=tagColor G H k s b)
    (x y : Entry G H k) : update G H k R x y=true ↔
      tagColor G H k (s+1) x=tagColor G H k (s+1) y := by
  classical
  rw [update,Bool.and_eq_true,hr,sameCounts_iff (fun a i => tagColor G H k s (a i)) _
    (vectorEqual_iff G H k R s hr),neighbors_color,neighbors_color]
  have hx : (tagColor G H k (s+1) x).1=tagColor G H k s x := by cases x <;> rfl
  have hy : (tagColor G H k (s+1) y).1=tagColor G H k s y := by cases y <;> rfl
  rw [← hx,← hy]
  exact Prod.ext_iff.symm

 theorem table_correct (s : ℕ) (x y : Entry G H k) : table G H k s x y=true ↔
    tagColor G H k s x=tagColor G H k s y := by
  induction s generalizing x y with
  | zero => simp [table,initial]
  | succ s ih => exact update_correct G H k (table G H k s) s (fun a b => ih a b) x y

 theorem histogramEqual_correct (R : Entry G H k → Entry G H k → Bool) (s : ℕ)
    (hr : ∀ a b, R a b=true ↔ tagColor G H k s a=tagColor G H k s b) :
    histogramEqual G H k R=true ↔ histogram G k s=histogram H k s := by
  classical
  rw [histogramEqual,sameCounts_iff (tagColor G H k s) R hr]
  simp only [List.map_map,Function.comp_def,tagColor,Sum.elim_inl,Sum.elim_inr,
    ← Multiset.map_coe,Finset.coe_toList,histogram]

 theorem accepts_correct : accepts G H k=true ↔ Equivalent G H k := by
  rw [accepts,histogramEqual_correct _ _ _ _ _ (table_correct G H k _),equivalent_iff_bounded_round]

end VariableWL.RefinementTable

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_Decision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace VariableWL.Encoding
attribute [local instance] Classical.propDecidable

 theorem fromMatrix_matrix (G : Graph) : fromMatrix G.order (matrix G) (matrix_valid G)=G := by
  rcases G with ⟨n,g⟩
  have hg : (fromMatrix n (matrix ⟨n,g⟩) (matrix_valid ⟨n,g⟩)).graph=g := by
    apply SimpleGraph.ext
    change (fun i j : Fin n => entry n (matrix ⟨n,g⟩) i j=true)=g.Adj
    funext i j
    apply propext
    rw [entry_matrix ⟨n,g⟩,decide_eq_true_eq]
  exact congrArg (Graph.mk n) hg

 theorem matrix_fromMatrix (n : ℕ) (v : Word) (h : MatrixValid n v) :
    matrix (fromMatrix n v h)=v := by
  unfold matrix
  change List.ofFn (fun p : Fin (n*n) => @decide (entry n v p.divNat p.modNat=true) (Classical.propDecidable _))=v
  have hd (b : Bool) : @decide (b=true) (Classical.propDecidable _)=b := by
    cases b <;> simp
  simp only [hd]
  apply List.ext_getElem
  · simpa only [List.length_ofFn] using h.1.symm
  · intro a ha hb
    have hp : a<n*n := by simpa only [List.length_ofFn] using ha
    rw [List.getElem_ofFn]
    simp only [entry,Fin.divNat,Fin.modNat]
    rw [Nat.mul_comm (a/n) n,Nat.div_add_mod a n,List.getD_eq_getElem v false hb]

 theorem readMatrix_matrix (G : Graph) : readMatrix G.order (matrix G)=some G := by
  simp only [readMatrix,dite_eq_left (matrix_valid G),fromMatrix_matrix]

 theorem readMatrix_sound {n : ℕ} {v : Word} {G : Graph} (h : readMatrix n v=some G) :
    G.order=n ∧ matrix G=v := by
  unfold readMatrix at h
  split_ifs at h with hv
  · cases Option.some.inj h
    exact ⟨rfl,matrix_fromMatrix n v hv⟩

 theorem graph_code (G : Graph) (v : Word) : graph (graphCode G++v)=some (G,v) := by
  rw [graphCode_eq,List.append_assoc]
  unfold graph
  simp only [integer_code]
  have he := matrix_length G
  rw [← he,List.take_left,readMatrix_matrix,List.drop_left]
  rfl

 theorem graph_sound {w v : Word} {G : Graph} (h : graph w=some (G,v)) : w=graphCode G++v := by
  unfold graph at h
  cases hi : integer w with
  | none => simp [hi] at h
  | some q =>
    rcases q with ⟨n,u⟩
    simp only [hi,Option.map_eq_some_iff] at h
    obtain ⟨G',hg,he⟩ := h
    cases he
    obtain ⟨hn,hm⟩ := readMatrix_sound hg
    rw [integer_sound hi,graphCode_eq,hn,hm,List.append_assoc,List.take_append_drop]

 theorem pair_code (G H : Graph) (k : ℕ) : pair (pairCode G H k)=some (G,H,k) := by
  unfold pairCode
  rw [List.append_assoc]
  unfold pair
  simp only [graph_code]
  have hi := integer_code k []
  simp only [List.append_nil] at hi
  simp [hi]

 theorem pair_sound {w : Word} {G H : Graph} {k : ℕ} (h : pair w=some (G,H,k)) : w=pairCode G H k := by
  unfold pair at h
  cases hg : graph w with
  | none => simp [hg] at h
  | some p =>
    rcases p with ⟨G',u⟩
    simp only [hg] at h
    cases hh : graph u with
    | none => simp [hh] at h
    | some q =>
      rcases q with ⟨H',v⟩
      simp only [hh] at h
      cases hi : integer v with
      | none => simp [hi] at h
      | some z =>
        rcases z with ⟨k',t⟩
        simp only [hi] at h
        split_ifs at h with ht
        · cases ht
          simp only [Option.some.injEq,Prod.mk.injEq] at h
          rcases h with ⟨rfl,rfl,rfl⟩
          rw [graph_sound hg,graph_sound hh,integer_sound hi,List.append_nil]
          exact List.append_assoc _ _ _ |>.symm

 theorem malformed_not_WL {w : Word} (h : pair w=none) : w ∉ WL := by
  rintro ⟨G,H,k,rfl,_⟩
  rw [pair_code] at h
  cases h

 theorem malformed_not_SubWL {w : Word} (h : pair w=none) : w ∉ SubWL := by
  rintro ⟨G,H,k,rfl,_⟩
  rw [pair_code] at h
  cases h

end VariableWL.Encoding

namespace VariableWL.RefinementArray
open RefinementTable
variable (G H : Graph) (k : ℕ)

 theorem lookup_pack (R : Entry G H k → Entry G H k → Bool) (x y : Entry G H k) :
    lookup G H k (pack G H k R) x y=R x y := by
  let a := numbering G H k x
  let b := numbering G H k y
  have hn : 0<count G H k := Nat.zero_lt_of_lt a.isLt
  have hp : a.val*count G H k+b.val<count G H k*count G H k := by
    have := Nat.mul_le_mul_right (count G H k) (Nat.succ_le_of_lt a.isLt)
    nlinarith [b.isLt]
  unfold lookup pack
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hp),List.getElem_ofFn]
  have hd : (⟨a.val*count G H k+b.val,hp⟩ : Fin (count G H k*count G H k)).divNat=a := by
    apply Fin.ext
    simp [Fin.divNat,Nat.add_div,Nat.div_eq_of_lt b.isLt,hn,Nat.mod_lt _ hn]
  have hm : (⟨a.val*count G H k+b.val,hp⟩ : Fin (count G H k*count G H k)).modNat=b := by
    apply Fin.ext
    simp [Fin.modNat,Nat.add_mod,Nat.mod_eq_of_lt b.isLt]
  rw [hd,hm]
  exact congrArg₂ R ((numbering G H k).symm_apply_apply x) ((numbering G H k).symm_apply_apply y)

 theorem array_correct (s : ℕ) (x y : Entry G H k) :
    lookup G H k (array G H k s) x y=table G H k s x y := by
  induction s generalizing x y with
  | zero => exact lookup_pack G H k _ x y
  | succ s ih =>
    rw [array,lookup_pack]
    have he : lookup G H k (array G H k s)=table G H k s := funext fun a => funext fun b => ih a b
    rw [he]
    rfl

 theorem accepts_correct : accepts G H k=true ↔ Equivalent G H k := by
  have he : lookup G H k (array G H k ((count G H k)^2))=table G H k ((G.order^k+H.order^k)^2) :=
    funext fun a => funext fun b => array_correct G H k _ a b
  rw [accepts,he]
  exact RefinementTable.accepts_correct G H k

end VariableWL.RefinementArray

namespace VariableWL.InputDecision

 theorem equivalent_capped (G H : Graph) {k : ℕ} (hk : 2≤k) :
    Equivalent G H k ↔ Equivalent G H (capped G k) := by
  by_cases h : k ≤ max 2 G.order
  · have he : capped G k=k := Nat.min_eq_left h
    rw [he]
  · have hn : G.order≤k := by omega
    have hc : capped G k=max 2 G.order := Nat.min_eq_right (by omega)
    rw [equivalent_large_iff_iso (by omega) hn,hc,
      equivalent_large_iff_iso (by omega) (le_max_right 2 G.order)]

end VariableWL.InputDecision

namespace VariableWL.PromiseDecision
attribute [local instance] Classical.propDecidable
variable (G : Graph)

 theorem reach_correct (t : ℕ) (u v : Fin G.order) :
    reach G t u v=true ↔ ∃ p : G.graph.Walk u v, p.length≤t := by
  induction t generalizing u v with
  | zero =>
    simp only [reach,decide_eq_true_eq,Nat.le_zero]
    constructor
    · rintro rfl; exact ⟨.nil,rfl⟩
    · rintro ⟨p,hp⟩
      cases p with
      | nil => rfl
      | cons h p => simp at hp
  | succ t ih =>
    simp only [reach,Bool.or_eq_true,List.any_eq_true,List.mem_finRange,true_and,
      Bool.and_eq_true,decide_eq_true_eq,ih]
    constructor
    · rintro (⟨p,hp⟩|⟨z,huz,p,hp⟩)
      · exact ⟨p,Nat.le_succ_of_le hp⟩
      · exact ⟨.cons huz p,Nat.succ_le_succ hp⟩
    · rintro ⟨p,hp⟩
      cases p with
      | nil => exact .inl ⟨.nil,Nat.zero_le _⟩
      | @cons z x y hu p => exact .inr ⟨x,hu,p,Nat.le_of_succ_le_succ hp⟩

 theorem reach_order (u v : Fin G.order) : reach G G.order u v=true ↔ G.graph.Reachable u v := by
  rw [reach_correct]
  constructor
  · rintro ⟨p,_⟩; exact p.reachable
  · intro h
    obtain ⟨p,hp⟩ := h.exists_isPath
    exact ⟨p,by have hh := hp.length_lt; simpa only [Fintype.card_fin] using hh.le⟩

 theorem connected_correct : connected G=true ↔ G.graph.Connected := by
  simp only [connected,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,List.mem_finRange,
    forall_const,reach_order]
  constructor
  · rintro ⟨hn,hr⟩
    let : Nonempty (Fin G.order) := ⟨⟨0,hn⟩⟩
    exact ⟨hr⟩
  · intro h
    exact ⟨by have := h.nonempty; exact Fin.pos_iff_nonempty.mpr this,h.preconnected⟩

 theorem neighbors_length (u : Fin G.order) : (neighbors G u).length=G.graph.degree u := by
  classical
  have hn : (neighbors G u).Nodup := (List.nodup_finRange _).filter _
  have he : (neighbors G u).toFinset=G.graph.neighborFinset u := by
    ext v
    simp [neighbors]
  rw [← List.toFinset_card_of_nodup hn,he]
  rfl

 theorem subcubic_correct : subcubic G=true ↔ Subcubic G := by
  simp only [subcubic,List.all_eq_true,List.mem_finRange,forall_const,decide_eq_true_eq,neighbors_length]
  rfl

end VariableWL.PromiseDecision

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_UnaryPower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace VariableWL.Encoding

 theorem order_le_code_length (G : Graph) : G.order ≤ (graphCode G).length := by
  have hn : G.order ≤ G.order*G.order := by
    by_cases hz : G.order=0
    · simp [hz]
    · have h := Nat.mul_le_mul_left G.order (Nat.one_le_iff_ne_zero.mpr hz)
      simpa only [Nat.mul_one] using h
  rw [graphCode_eq,List.length_append,matrix_length]
  omega

 theorem pair_orders {w : Word} {G H : Graph} {k : ℕ} (h : pair w=some (G,H,k)) :
    G.order ≤ w.length ∧ H.order ≤ w.length := by
  rw [pair_sound h,pairCode,List.length_append,List.length_append]
  have hG := order_le_code_length G
  have hH := order_le_code_length H
  omega

end VariableWL.Encoding

namespace VariableWL.RefinementSize

 theorem count_bound (G H : Graph) (k m : ℕ) (hG : G.order ≤ m) (hH : H.order ≤ m) (hk : k ≤ m) :
    RefinementArray.count G H k ≤ 2^(m*m+1) := by
  have hp (a : ℕ) (ha : a ≤ m) : a^k ≤ 2^(m*m) := by
    calc
      _  ≤  (2^m)^k := Nat.pow_le_pow_left (ha.trans (Nat.le_of_lt (Nat.lt_two_pow_self (n := m)))) k
      _ = 2^(m*k) := (pow_mul 2 m k).symm
      _  ≤  2^(m*m) := Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left m hk)
  have h1 := hp G.order hG
  have h2 := hp H.order hH
  unfold RefinementArray.count
  rw [pow_succ]
  omega

 theorem capped_count_bound {w : Word} {G H : Graph} {k : ℕ}
    (h : Encoding.pair w=some (G,H,k)) :
    RefinementArray.count G H (InputDecision.capped G k) ≤ 2^((w.length+2)^2+1) := by
  obtain ⟨hG,hH⟩ := Encoding.pair_orders h
  have hk : InputDecision.capped G k ≤ w.length+2 := by unfold InputDecision.capped; omega
  simpa only [pow_two] using count_bound G H (InputDecision.capped G k) (w.length+2)
    (by omega) (by omega) hk

 theorem polynomial_of_exponential (c d m N : ℕ) (hN : N ≤ 2^(m*m+1)) :
    c*(N+1)^d ≤ 2^((c+d+1)*(m+2)^2) := by
  have hP : 1 ≤ 2^(m*m+1) := Nat.succ_le_of_lt (pow_pos (by omega) _)
  have hN' : N+1 ≤ 2^(m*m+2) := by
    rw [show m*m+2=(m*m+1)+1 by omega,pow_succ]
    omega
  calc
    _  ≤  2^c*(2^(m*m+2))^d := Nat.mul_le_mul (Nat.le_of_lt (Nat.lt_two_pow_self (n := c))) (Nat.pow_le_pow_left hN' d)
    _ = 2^(c+(m*m+2)*d) := by rw [← pow_mul,← pow_add]
    _  ≤  _ := Nat.pow_le_pow_right (by omega) (by nlinarith)

end VariableWL.RefinementSize

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_BinaryMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace VariableWL.Computation.Stack.BinaryMachine
open Code

 theorem value_bound (w : Word) (q : ℕ) : value w q+1 ≤ (q+1)*2^w.length := by
  induction w generalizing q with
  | nil => simp [value]
  | cons b w ih =>
    have h := ih (2*q+b.toNat)
    have hb : b.toNat ≤ 1 := by cases b <;> decide
    simp only [value,List.length_cons,pow_succ]
    nlinarith [Nat.mul_le_mul_right (2^w.length) (show 2*q+b.toNat+1 ≤ 2*(q+1) by omega)]

 theorem value_append (u v : Word) (q : ℕ) : value (u++v) q=value v (value u q) := by
  induction u generalizing q with
  | nil => rfl
  | cons b u ih => exact ih (2*q+b.toNat)

 theorem value_reverse (w : Word) (q : ℕ) : value w.reverse q=q*2^w.length+Encoding.value w := by
  induction w generalizing q with
  | nil => simp [value,Encoding.value]
  | cons b w ih =>
    rw [List.reverse_cons,value_append,ih]
    simp only [value,List.length_cons,pow_succ,Encoding.value,List.foldr_cons]
    cases b <;> simp [Nat.bit] <;> ring

end VariableWL.Computation.Stack.BinaryMachine

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_BoundedLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace VariableWL.TupleAddress

 theorem encode_lt {n k : ℕ} (v : Fin k → Fin n) : encode v<n^k :=
  (finFunctionFinEquiv v).isLt

 theorem digit_encode {n k : ℕ} (v : Fin k → Fin n) (i : Fin k) :
    digit n (encode v) i.val=(v i).val := by
  have he := congrArg (fun f : Fin k → Fin n => (f i).val) (finFunctionFinEquiv.symm_apply_apply v)
  exact he

 theorem encode_sum {n k : ℕ} (v : Fin k → Fin n) :
    encode v=∑i:Fin k,(v i).val*n^i.val := rfl

 theorem encode_update {n k : ℕ} (v : Fin k → Fin n) (i : Fin k) (z : Fin n) :
    encode (Function.update v i z)=replace n (encode v) i.val z.val := by
  classical
  let rest := ∑j∈Finset.univ.erase i,(v j).val*n^j.val
  have ha : rest+(v i).val*n^i.val=encode v := by
    exact Finset.sum_erase_add _ _ (Finset.mem_univ i)
  have hb : rest+z.val*n^i.val=encode (Function.update v i z) := by
    rw [encode_sum,←Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    simp only [Function.update_self]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  unfold replace
  rw [digit_encode]
  omega

end VariableWL.TupleAddress

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_Procedure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace VariableWL.Computation.Stack.Procedure
open Code
variable {k : ℕ}

 theorem outputs {f : Stores k → Stores k} {T : Stores k → ℕ} (o : Fin (k+1))
    (h : Realizes f T) : ∃ M : VariableWL.Machine, ∀ w : Word,
      VariableWL.OutputsWithin M w
        (f (fun j => if j=0 then w.reverse else []) o)
        (4*(w.length+T (fun j => if j=0 then w.reverse else [])+1)) := by
  obtain ⟨e,C,hC⟩ := h
  let out : Fin (k+e+1) := ⟨o.val,by omega⟩
  refine ⟨(C.machine out).compile,fun w => ?_⟩
  let s : Stores k := fun j => if j=0 then w.reverse else []
  obtain ⟨n,hn,he⟩ := hC s
  have hs : extend e s=(fun j => if j=0 then w.reverse else []) := by
    funext j
    by_cases hj : j.val<k+1
    · simp only [extend,hj,dite_true,s]
      have hz : (⟨j.val,hj⟩ : Fin (k+1))=0 ↔ j=0 := by simp only [Fin.ext_iff,Fin.val_zero]
      simp only [hz]
    · rw [extend_back _ _ _ (by omega)]
      have hz : j≠0 := by intro hz; subst j; simp only [Fin.val_zero] at hj; omega
      simp only [hz,ite_false]
  rw [hs] at he
  have ho := eval_outputs C out w he
  rw [extend_front] at ho
  obtain ⟨t,ht,hh,hout⟩ := ho
  exact ⟨t,ht.trans (by dsimp only [s] at hn; omega),hh,hout⟩

end VariableWL.Computation.Stack.Procedure

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_NumericRefinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace VariableWL.NumericRefinement

 theorem all_range (n : ℕ) (p : ℕ → Bool) :
    (List.range n).all p=true ↔ ∀i:Fin n,p i=true := by
  simp only [List.all_eq_true,List.mem_range]
  exact ⟨fun h i=>h i i.isLt,fun h i hi=>h ⟨i,hi⟩⟩

 theorem ofFn_nat {α : Type} (n : ℕ) (f : ℕ → α) :
    List.ofFn (fun i:Fin n=>f i)=(List.range n).map f := by
  rw [List.ofFn_eq_map,←List.map_coe_finRange_eq_range,List.map_map]
  rfl

 theorem sameCounts_map {α β : Type} (f : α → β) (eq : β → β → Bool) (xs ys : List α) :
    RefinementTable.sameCounts eq (xs.map f) (ys.map f)=
      RefinementTable.sameCounts (fun a b=>eq (f a) (f b)) xs ys := by
  simp only [RefinementTable.sameCounts,←List.map_append,List.all_map,Function.comp_def,List.filter_map,List.length_map]

open RefinementTable
attribute [local instance] Classical.propDecidable
variable (G H : Graph) (k : ℕ)

 theorem address_inl (v : Tuple G k) : address G H k (.inl v)=TupleAddress.encode v := rfl
 theorem address_inr (v : Tuple H k) : address G H k (.inr v)=G.order^k+TupleAddress.encode v := rfl

 theorem left_inl (v : Tuple G k) : (data G H k).isLeft (address G H k (.inl v))=true := by
  change decide (TupleAddress.encode v<G.order^k)=true
  exact decide_eq_true (TupleAddress.encode_lt v)

 theorem left_inr (v : Tuple H k) : (data G H k).isLeft (address G H k (.inr v))=false := by
  change decide (G.order^k+TupleAddress.encode v<G.order^k)=false
  exact decide_eq_false (by omega)

 theorem order_inl (v : Tuple G k) : (data G H k).order (address G H k (.inl v))=G.order := by
  rw [Data.order,left_inl]
  rfl
 theorem order_inr (v : Tuple H k) : (data G H k).order (address G H k (.inr v))=H.order := by
  rw [Data.order,left_inr]
  rfl

 theorem coordinate_inl (v : Tuple G k) (i : Fin k) :
    (data G H k).coordinate (address G H k (.inl v)) i.val=(v i).val := by
  rw [Data.coordinate,order_inl,Data.offset,left_inl]
  simp only [ite_true,Nat.sub_zero,address_inl]
  exact TupleAddress.digit_encode v i

 theorem coordinate_inr (v : Tuple H k) (i : Fin k) :
    (data G H k).coordinate (address G H k (.inr v)) i.val=(v i).val := by
  rw [Data.coordinate,order_inr,Data.offset,left_inr]
  simp only [Bool.false_eq_true,ite_false,data,Data.leftCount,address_inr,Nat.add_sub_cancel_left]
  exact TupleAddress.digit_encode v i

 theorem replacement_inl (v : Tuple G k) (z : Fin G.order) (i : Fin k) :
    (data G H k).replacement (address G H k (.inl v)) z.val i.val=
      address G H k (.inl (Function.update v i z)) := by
  rw [Data.replacement,order_inl,Data.offset,left_inl]
  simp only [ite_true,Nat.sub_zero,Nat.zero_add,address_inl]
  exact (TupleAddress.encode_update v i z).symm

 theorem replacement_inr (v : Tuple H k) (z : Fin H.order) (i : Fin k) :
    (data G H k).replacement (address G H k (.inr v)) z.val i.val=
      address G H k (.inr (Function.update v i z)) := by
  rw [Data.replacement,order_inr,Data.offset,left_inr]
  simp only [Bool.false_eq_true,ite_false,data,Data.leftCount,address_inr,Nat.add_sub_cancel_left]
  rw [TupleAddress.encode_update]

 theorem edge_inl (v : Tuple G k) (i j : Fin k) :
    (data G H k).edge (address G H k (.inl v)) i.val j.val=decide (G.graph.Adj (v i) (v j)) := by
  classical
  rw [Data.edge,left_inl,coordinate_inl,coordinate_inl,order_inl]
  change (Encoding.matrix G).getD ((v i).val*G.order+(v j).val) false=_
  exact Encoding.entry_matrix G (v i) (v j)

 theorem edge_inr (v : Tuple H k) (i j : Fin k) :
    (data G H k).edge (address G H k (.inr v)) i.val j.val=decide (H.graph.Adj (v i) (v j)) := by
  classical
  rw [Data.edge,left_inr,coordinate_inr,coordinate_inr,order_inr]
  change (Encoding.matrix H).getD ((v i).val*H.order+(v j).val) false=_
  exact Encoding.entry_matrix H (v i) (v j)

 theorem get_address (R : Word) (x y : Entry G H k) :
    (data G H k).get R (address G H k x) (address G H k y)=RefinementArray.lookup G H k R x y := rfl

end VariableWL.NumericRefinement

namespace VariableWL.NumericRefinement
open RefinementTable
attribute [local instance] Classical.propDecidable
variable (G H : Graph) (k : ℕ)

 theorem keys_pair (x : Entry G H k) :
    (keys G H k x).map (keyPair G H k)=(data G H k).neighbors (address G H k x) := by
  cases x with
  | inl v => rw [keys,List.map_ofFn,Data.neighbors,order_inl]; exact ofFn_nat _ _
  | inr v => rw [keys,List.map_ofFn,Data.neighbors,order_inr]; exact ofFn_nat _ _

 theorem keys_vector (x : Entry G H k) :
    (keys G H k x).map (keyVector G H k)=RefinementTable.neighbors G H k x := by
  cases x <;> simp only [keys,List.map_ofFn,RefinementTable.neighbors,Function.comp_def,keyVector]

 theorem replacement_key (a : Key G H k) (i : Fin k) :
    (data G H k).replacement (keyPair G H k a).1 (keyPair G H k a).2 i.val =
      address G H k (keyVector G H k a i) := by
  cases a with
  | inl p => exact replacement_inl G H k p.1 p.2 i
  | inr p => exact replacement_inr G H k p.1 p.2 i

 theorem profile_key (R : Word) (a b : Key G H k) :
    (data G H k).profile R (keyPair G H k a) (keyPair G H k b)=
      vectorEqual G H k (RefinementArray.lookup G H k R) (keyVector G H k a) (keyVector G H k b) := by
  apply Bool.eq_iff_iff.mpr
  rw [Data.profile]
  change (List.range k).all _=true ↔ _
  rw [all_range]
  simp only [vectorEqual,List.all_eq_true,List.mem_finRange,forall_const,replacement_key,get_address]

 theorem update_address (R : Word) (a b : Entry G H k) :
    (data G H k).update R (address G H k a) (address G H k b)=
      RefinementTable.update G H k (RefinementArray.lookup G H k R) a b := by
  rw [Data.update,get_address,←keys_pair,←keys_pair,sameCounts_map]
  rw [RefinementTable.update,←keys_vector,←keys_vector,sameCounts_map]
  congr 2
  funext x y
  exact profile_key G H k R x y

 theorem atomic_address (a : Entry G H k) (i j : Fin k) :
    (decide ((data G H k).coordinate (address G H k a) i.val=
      (data G H k).coordinate (address G H k a) j.val),
      (data G H k).edge (address G H k a) i.val j.val)=tagColor G H k 0 a i j := by
  cases a with
  | inl v =>
    rw [coordinate_inl,coordinate_inl,edge_inl]
    change (decide ((v i).val=(v j).val),decide (G.graph.Adj (v i) (v j)))=
      (decide (v i=v j),decide (G.graph.Adj (v i) (v j)))
    simp only [Fin.val_inj]
  | inr v =>
    rw [coordinate_inr,coordinate_inr,edge_inr]
    change (decide ((v i).val=(v j).val),decide (H.graph.Adj (v i) (v j)))=
      (decide (v i=v j),decide (H.graph.Adj (v i) (v j)))
    simp only [Fin.val_inj]

 theorem initial_address (a b : Entry G H k) :
    (data G H k).initial (address G H k a) (address G H k b)=RefinementTable.initial G H k a b := by
  apply Bool.eq_iff_iff.mpr
  rw [Data.initial]
  change (List.range k).all (fun i=>(List.range k).all _)=true ↔ _
  simp only [all_range,Bool.and_eq_true,decide_eq_true_eq,RefinementTable.initial]
  change _ ↔ (fun i j=>tagColor G H k 0 a i j)=(fun i j=>tagColor G H k 0 b i j)
  simp only [funext_iff,←atomic_address,Prod.mk.injEq,decide_eq_decide]

 theorem pack_correct (f : ℕ → ℕ → Bool) (R : Entry G H k → Entry G H k → Bool)
    (h : ∀a b,f (address G H k a) (address G H k b)=R a b) :
    (data G H k).pack f=RefinementArray.pack G H k R := by
  change (List.range (RefinementArray.count G H k*RefinementArray.count G H k)).map _=_
  rw [←ofFn_nat,RefinementArray.pack]
  congr 1
  funext p
  have he := h ((RefinementArray.numbering G H k).symm p.divNat)
    ((RefinementArray.numbering G H k).symm p.modNat)
  unfold address at he
  rw [Equiv.apply_symm_apply,Equiv.apply_symm_apply] at he
  exact he

 theorem array_correct (s : ℕ) : (data G H k).array s=RefinementArray.array G H k s := by
  induction s with
  | zero => exact pack_correct G H k _ _ (initial_address G H k)
  | succ s ih =>
    rw [Data.array,RefinementArray.array,ih]
    exact pack_correct G H k _ _ (update_address G H k _)

end VariableWL.NumericRefinement

namespace VariableWL.NumericRefinement
open RefinementTable
attribute [local instance] Classical.propDecidable

 theorem sameCounts_perm {α : Type} (eq : α → α → Bool) {xs ys xs' ys' : List α}
    (hx : xs.Perm xs') (hy : ys.Perm ys') :
    sameCounts eq xs ys=sameCounts eq xs' ys' := by
  unfold sameCounts
  have hf : (fun a=>decide ((xs.filter (eq a)).length=(ys.filter (eq a)).length))=
      (fun a=>decide ((xs'.filter (eq a)).length=(ys'.filter (eq a)).length)) := by
    funext a
    rw [(hx.filter (eq a)).length_eq,(hy.filter (eq a)).length_eq]
  rw [hf]
  exact (hx.append hy).all_eq

 theorem ofFn_perm_univ {α : Type} [Fintype α] {n : ℕ} (e : α ≃ Fin n) :
    (List.ofFn e.symm).Perm (Finset.univ : Finset α).toList := by
  apply (List.perm_ext_iff_of_nodup (List.nodup_ofFn_ofInjective e.symm.injective)
    (Finset.nodup_toList _)).mpr
  intro x
  simp only [List.mem_ofFn,Finset.mem_toList,Finset.mem_univ,iff_true]
  exact ⟨e x,e.symm_apply_apply x⟩

variable (G H : Graph) (k : ℕ)

 theorem leftEntries_address : (leftEntries G H k).map (address G H k)=List.range (G.order^k) := by
  rw [leftEntries,List.map_ofFn,←List.map_coe_finRange_eq_range,←List.ofFn_eq_map]
  congr 1
  funext p
  change (finFunctionFinEquiv (finFunctionFinEquiv.symm p)).val=p.val
  rw [Equiv.apply_symm_apply]

 theorem rightEntries_address : (rightEntries G H k).map (address G H k)=
    (List.range (H.order^k)).map (G.order^k+·) := by
  rw [rightEntries,List.map_ofFn,←ofFn_nat]
  congr 1
  funext p
  change G.order^k+(finFunctionFinEquiv (finFunctionFinEquiv.symm p)).val=G.order^k+p.val
  rw [Equiv.apply_symm_apply]

 theorem leftEntries_perm : (leftEntries G H k).Perm
    ((Finset.univ : Finset (Tuple G k)).toList.map Sum.inl) := by
  have h := (ofFn_perm_univ (finFunctionFinEquiv : Tuple G k ≃ Fin (G.order^k))).map
    (Sum.inl : Tuple G k → Entry G H k)
  simpa only [List.map_ofFn,leftEntries,Function.comp_def] using h

 theorem rightEntries_perm : (rightEntries G H k).Perm
    ((Finset.univ : Finset (Tuple H k)).toList.map Sum.inr) := by
  have h := (ofFn_perm_univ (finFunctionFinEquiv : Tuple H k ≃ Fin (H.order^k))).map
    (Sum.inr : Tuple H k → Entry G H k)
  simpa only [List.map_ofFn,rightEntries,Function.comp_def] using h

 theorem histogram_correct (R : Word) : (data G H k).histogram R=
    histogramEqual G H k (RefinementArray.lookup G H k R) := by
  change sameCounts ((data G H k).get R) (List.range (G.order^k))
    ((List.range (H.order^k)).map (G.order^k+·))=_
  rw [←leftEntries_address G H k,←rightEntries_address G H k,sameCounts_map]
  change sameCounts (RefinementArray.lookup G H k R) (leftEntries G H k) (rightEntries G H k)=_
  exact sameCounts_perm _ (leftEntries_perm G H k) (rightEntries_perm G H k)

 theorem accepts_correct : (data G H k).accepts=true ↔ Equivalent G H k := by
  rw [Data.accepts,histogram_correct,array_correct]
  exact RefinementArray.accepts_correct G H k

end VariableWL.NumericRefinement

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_CertifiedRecipe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace VariableWL.Computation.Stack.Recipe
variable {n m : ℕ}

 theorem power_value (B E : Certified n) (v : Env n) :
    (power B E).value v=List.replicate ((B.value v).length^(E.value v).length) true := by
  rw [power,iterate_value]
  generalize (E.value v).length=j
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [foldValue,times_value,input_value,cons_zero,ih,List.length_replicate,reindex_value,pow_succ]
    rfl

end VariableWL.Computation.Stack.Recipe

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_NumericProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace VariableWL.NumericProgram
open Computation.Stack Computation.Stack.Recipe Computation.Stack.PolyRecipe
variable {n m : ℕ}

 theorem good_up {D : Data n} {v : Env n} (h : D.Good v) (w : Word) : D.up.Good (cons w v) := h
 theorem good_up₂ {D : Data n} {v : Env n} (h : D.Good v) (w z : Word) : D.up₂.Good (cons z (cons w v)) := h

 theorem power_bound (a i k C : ℕ) (hi : i≤k) (h1 : 1≤C) (h : a^k≤C) : a^i≤C := by
  by_cases ha : a=0
  · subst a
    by_cases hz : i=0
    · simpa [hz] using h1
    · simp [zero_pow hz]
  · exact (Nat.pow_le_pow_right (Nat.pos_of_ne_zero ha) hi).trans h

theorem leftCount_number (D : Data n) (v : Env n) (h : D.Good v) :
    D.leftCount.number v=(D.eval v).leftCount := by
  rw [Data.leftCount,capPow_number,min_eq_left h.2.1]
  rfl
theorem rightCount_number (D : Data n) (v : Env n) (h : D.Good v) :
    D.rightCount.number v=(D.eval v).rightCount := by
  rw [Data.rightCount,capPow_number,min_eq_left h.2.2]
  rfl
theorem count_number (D : Data n) (v : Env n) (h : D.Good v) :
    D.count.number v=(D.eval v).count := by
  rw [Data.count,add_number,leftCount_number _ _ h,rightCount_number _ _ h]
  rfl
theorem isLeft_bit (D : Data n) (a : Expr n) (v : Env n) (h : D.Good v) :
    (D.isLeft a).bit v=(D.eval v).isLeft (a.number v) := by
  rw [Data.isLeft,PolyRecipe.lt_bit,leftCount_number _ _ h]
  rfl
theorem order_number (D : Data n) (a : Expr n) (v : Env n) (h : D.Good v) :
    (D.order a).number v=(D.eval v).order (a.number v) := by
  rw [Data.order,choose_number,isLeft_bit _ _ _ h]
  rfl
theorem offset_number (D : Data n) (a : Expr n) (v : Env n) (h : D.Good v) :
    (D.offset a).number v=(D.eval v).offset (a.number v) := by
  rw [Data.offset,choose_number,isLeft_bit _ _ _ h,numeral_number,leftCount_number _ _ h]
  rfl
theorem power_number (D : Data n) (a i : Expr n) (v : Env n) (h : D.Good v)
    (hi : i.number v≤D.dimension.number v) :
    (D.power a i).number v=(D.eval v).order (a.number v)^i.number v := by
  rw [Data.power,capPow_number,order_number _ _ _ h]
  apply min_eq_left
  unfold NumericRefinement.Data.order
  split
  · exact power_bound _ _ _ _ hi h.1 h.2.1
  · exact power_bound _ _ _ _ hi h.1 h.2.2

theorem coordinate_number (D : Data n) (a i : Expr n) (v : Env n) (h : D.Good v)
    (hi : i.number v≤D.dimension.number v) :
    (D.coordinate a i).number v=(D.eval v).coordinate (a.number v) (i.number v) := by
  rw [Data.coordinate,mod_number,div_number,sub_number,offset_number _ _ _ h,
    power_number _ _ _ _ h hi,order_number _ _ _ h]
  rfl

theorem replacement_number (D : Data n) (a z i : Expr n) (v : Env n) (h : D.Good v)
    (hi : i.number v≤D.dimension.number v) :
    (D.replacement a z i).number v=(D.eval v).replacement (a.number v) (z.number v) (i.number v) := by
  simp only [Data.replacement,add_number,sub_number,mul_number,offset_number _ _ _ h,
    coordinate_number _ _ _ _ h hi,power_number _ _ _ _ h hi]
  rfl

theorem edge_bit (D : Data n) (a i j : Expr n) (v : Env n) (h : D.Good v)
    (hi : i.number v≤D.dimension.number v) (hj : j.number v≤D.dimension.number v) :
    (D.edge a i j).bit v=(D.eval v).edge (a.number v) (i.number v) (j.number v) := by
  rw [Data.edge,lookup_bit,PolyRecipe.choose_value,isLeft_bit _ _ _ h,add_number,mul_number,
    coordinate_number _ _ _ _ h hi,coordinate_number _ _ _ _ h hj,order_number _ _ _ h]
  rfl

theorem list_all_congr {α : Type} (xs : List α) {f g : α → Bool} (h : ∀a∈xs,f a=g a) : xs.all f=xs.all g := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [List.all_cons,List.all_cons,h a (by simp),ih (by intro b hb; exact h b (by simp [hb]))]

theorem initial_bit (D : Data n) (a b : Expr n) (v : Env n) (h : D.Good v) :
    (D.initial a b).bit v=(D.eval v).initial (a.number v) (b.number v) := by
  rw [Data.initial,all_bit]
  unfold NumericRefinement.Data.initial
  apply list_all_congr
  intro i hi
  rw [all_bit]
  change (List.range (D.dimension.number v)).all _=_
  apply list_all_congr
  intro j hj
  have hi' : (PolyRecipe.input (1 : Fin (n+2))).number (cons (List.replicate j true) (cons (List.replicate i true) v))≤
      D.up₂.dimension.number (cons (List.replicate j true) (cons (List.replicate i true) v)) := by
    change (List.replicate i true).length≤D.dimension.number v
    simpa only [List.length_replicate] using Nat.le_of_lt (List.mem_range.mp hi)
  have hj' : (PolyRecipe.input (0 : Fin (n+2))).number (cons (List.replicate j true) (cons (List.replicate i true) v))≤
      D.up₂.dimension.number (cons (List.replicate j true) (cons (List.replicate i true) v)) := by
    change (List.replicate j true).length≤D.dimension.number v
    simpa only [List.length_replicate] using Nat.le_of_lt (List.mem_range.mp hj)
  simp only [conj_bit,bitEq_bit,eq_bit,coordinate_number _ _ _ _ (good_up₂ h _ _) hi',
    coordinate_number _ _ _ _ (good_up₂ h _ _) hj',edge_bit _ _ _ _ _ (good_up₂ h _ _) hi' hj',
    eval_up₂,up₂_number,input_number,cons_one,cons_zero,List.length_replicate]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq]

end VariableWL.NumericProgram

namespace VariableWL.NumericProgram
open Computation.Stack Computation.Stack.Recipe Computation.Stack.PolyRecipe
variable {n : ℕ}

theorem sameRanges_bit (A B : Expr n) (AA AB BA BB : Expr (n+2)) (v : Env n) :
    (sameRanges A B AA AB BA BB).bit v=
      (((List.range (A.number v)).all fun x=>decide
        ((List.range (A.number v)).countP (fun y=>AA.bit (cons (List.replicate y true) (cons (List.replicate x true) v)))=
         (List.range (B.number v)).countP (fun y=>AB.bit (cons (List.replicate y true) (cons (List.replicate x true) v))))) &&
      ((List.range (B.number v)).all fun x=>decide
        ((List.range (A.number v)).countP (fun y=>BA.bit (cons (List.replicate y true) (cons (List.replicate x true) v)))=
         (List.range (B.number v)).countP (fun y=>BB.bit (cons (List.replicate y true) (cons (List.replicate x true) v)))))) := by
  simp only [sameRanges,conj_bit,all_bit,eq_bit,PolyRecipe.count_number,up_number]

theorem sameCounts_ranges {α : Type} (e : α → α → Bool) (A B : ℕ) (f g : ℕ → α) :
    RefinementTable.sameCounts e ((List.range A).map f) ((List.range B).map g)=
      (((List.range A).all fun x=>decide ((List.range A).countP (fun y=>e (f x) (f y))=
        (List.range B).countP (fun y=>e (f x) (g y)))) &&
      ((List.range B).all fun x=>decide ((List.range A).countP (fun y=>e (g x) (f y))=
        (List.range B).countP (fun y=>e (g x) (g y))))) := by
  simp only [RefinementTable.sameCounts,List.all_append,List.all_map,List.filter_map,List.length_map,
    Function.comp_def,List.countP_eq_length_filter]

theorem get_bit (D : Data n) (R a b : Expr n) (v : Env n) (h : D.Good v) :
    (D.get R a b).bit v=(D.eval v).get (R.value v) (a.number v) (b.number v) := by
  rw [Data.get,lookup_bit,add_number,mul_number,count_number _ _ h]
  rfl

theorem profile_bit (D : Data n) (R a z b w : Expr n) (v : Env n) (h : D.Good v) :
    (D.profile R a z b w).bit v=(D.eval v).profile (R.value v) (a.number v,z.number v) (b.number v,w.number v) := by
  rw [Data.profile,all_bit]
  unfold NumericRefinement.Data.profile
  apply list_all_congr
  intro i hi
  have hi' : (PolyRecipe.input (0 : Fin (n+1))).number (cons (List.replicate i true) v)≤D.up.dimension.number (cons (List.replicate i true) v) := by
    change (List.replicate i true).length≤D.dimension.number v
    simpa only [List.length_replicate] using Nat.le_of_lt (List.mem_range.mp hi)
  rw [get_bit _ _ _ _ _ (good_up h _),replacement_number _ _ _ _ _ (good_up h _) hi',
    replacement_number _ _ _ _ _ (good_up h _) hi']
  simp only [eval_up,up_value,up_number,input_number,cons_zero,List.length_replicate]

theorem comparison_bit (D : Data n) (R a b : Expr n) (v : Env n) (h : D.Good v) :
    (D.comparison R a b).bit v=RefinementTable.sameCounts ((D.eval v).profile (R.value v))
      ((D.eval v).neighbors (a.number v)) ((D.eval v).neighbors (b.number v)) := by
  rw [Data.comparison,sameRanges_bit]
  unfold NumericRefinement.Data.neighbors
  rw [sameCounts_ranges]
  simp only [order_number _ _ _ h,profile_bit _ _ _ _ _ _ _ (good_up₂ h _ _),
    eval_up₂,up₂_value,up₂_number,input_number,cons_one,cons_zero,List.length_replicate]

theorem update_bit (D : Data n) (R a b : Expr n) (v : Env n) (h : D.Good v) :
    (D.update R a b).bit v=(D.eval v).update (R.value v) (a.number v) (b.number v) := by
  rw [Data.update,conj_bit,get_bit _ _ _ _ _ h,comparison_bit _ _ _ _ _ h]
  rfl

theorem initialArray_value (D : Data n) (v : Env n) (h : D.Good v) :
    D.initialArray.value v=(D.eval v).array 0 := by
  rw [Data.initialArray,PolyRecipe.collect_value]
  simp only [mul_number,count_number _ _ h,initial_bit _ _ _ _ (good_up h _),
    eval_up,div_number,mod_number,input_number,cons_zero,List.length_replicate,count_number _ _ (good_up h _)]
  rfl

theorem nextArray_value (D : Data n) (R : Expr n) (v : Env n) (h : D.Good v) :
    (D.nextArray R).value v=(D.eval v).pack ((D.eval v).update (R.value v)) := by
  rw [Data.nextArray,PolyRecipe.collect_value]
  simp only [mul_number,count_number _ _ h,update_bit _ _ _ _ _ (good_up h _),
    eval_up,up_value,div_number,mod_number,input_number,cons_zero,List.length_replicate,count_number _ _ (good_up h _)]
  rfl

end VariableWL.NumericProgram

namespace VariableWL.NumericProgram
open Computation.Stack Computation.Stack.Recipe Computation.Stack.PolyRecipe
variable {n : ℕ}

theorem arrayPrefix_value (D : Data n) (v : Env n) (h : D.Good v) (j : ℕ) :
    Recipe.foldValue D.arrayBody.program v (D.initialArray.value v) j=(D.eval v).array j := by
  induction j with
  | zero => exact initialArray_value D v h
  | succ j ih =>
    change (D.up₂.nextArray (PolyRecipe.input 0)).value _=_
    rw [nextArray_value _ _ _ (good_up₂ h _ _)]
    simp only [eval_up₂,PolyRecipe.input_value,cons_zero,ih]
    rfl

theorem array_value (D : Data n) (v : Env n) (h : D.Good v) :
    D.array.value v=(D.eval v).array ((D.eval v).count^2) := by
  change (Recipe.iterate (mul D.count D.count).program D.initialArray.program D.arrayBody.program).value v=_
  rw [Recipe.iterate_value]
  change Recipe.foldValue D.arrayBody.program v (D.initialArray.value v) ((mul D.count D.count).number v)=_
  rw [arrayPrefix_value _ _ h]
  rw [mul_number,count_number _ _ h,pow_two]

theorem histogram_bit (D : Data n) (R : Expr n) (v : Env n) (h : D.Good v) :
    (D.histogram R).bit v=(D.eval v).histogram (R.value v) := by
  rw [Data.histogram,sameRanges_bit]
  unfold NumericRefinement.Data.histogram
  have hs := sameCounts_ranges ((D.eval v).get (R.value v)) (D.eval v).leftCount (D.eval v).rightCount id ((D.eval v).leftCount+·)
  rw [List.map_id] at hs
  rw [hs]
  simp only [leftCount_number _ _ h,rightCount_number _ _ h,get_bit _ _ _ _ _ (good_up₂ h _ _),
    add_number,leftCount_number _ _ (good_up₂ h _ _),eval_up₂,up₂_value,input_number,cons_one,cons_zero,List.length_replicate,id_eq]

theorem sameRanges_singleton (A B : Expr n) (AA AB BA BB : Expr (n+2)) (v : Env n) :
    (sameRanges A B AA AB BA BB).value v=[(sameRanges A B AA AB BA BB).bit v] := by
  rw [sameRanges,PolyRecipe.conj_value,conj_bit]

theorem accepts_value (D : Data n) (v : Env n) (h : D.Good v) :
    D.accepts.value v=[(D.eval v).accepts] := by
  change (sameRanges _ _ _ _ _ _).value _=_
  rw [sameRanges_singleton]
  change [(D.histogram D.array).bit v]=_
  rw [histogram_bit _ _ _ h,array_value _ _ h]
  rfl

end VariableWL.NumericProgram

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n : ℕ}

theorem foldWordProgram_value (W Z : Expr n) (Q : Expr (n+2)) (v : Env n) :
    (foldWordProgram W Z Q).value v=(W.value v).foldl (foldWordStep Q v) (Z.value v) := by
  rw [foldWordProgram,Recipe.iterate_value]
  change foldValue (foldWordBody W Q).program v (Z.value v) ((length W).number v)=_
  rw [length_number,foldWord_prefix _ _ _ _ _ le_rfl,List.take_length]

end VariableWL.Computation.Stack.PolyRecipe

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_MatrixOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n : ℕ}

theorem binary_value (W C : Expr n) (v : Env n) :
    (binary W C).value v=List.replicate (min (Encoding.value (W.value v)) (C.number v)) true := by
  change (foldWordProgram (reverse W) (numeral 0) (binaryStep C)).value v=_
  rw [foldWordProgram_value,reverse_value]
  have h0 : (numeral (0 : ℕ) : Expr n).value v=List.replicate (min 0 (C.number v)) true := by simp [numeral]
  rw [h0,binary_fold,BinaryMachine.value_reverse]
  simp only [Nat.zero_mul,Nat.zero_add]

@[simp] theorem binary_number (W C : Expr n) (v : Env n) :
    (binary W C).number v=min (Encoding.value (W.value v)) (C.number v) := by
  unfold Expr.number
  rw [binary_value,List.length_replicate]
  rfl

theorem prefixValue_append (u w : Word) (q : ℕ) : prefixValue (u++w) q=prefixValue w (prefixValue u q) := by
  induction u generalizing q with
  | nil => rfl
  | cons b u ih => cases b <;> simp only [List.cons_append,prefixValue,ih]

theorem prefixValue_reverse (w : Word) (q : ℕ) :
    prefixValue w.reverse q=headCount w+(if w.all id then q else 0) := by
  induction w with
  | nil => simp [prefixValue,headCount]
  | cons b w ih =>
    rw [List.reverse_cons,prefixValue_append]
    cases b with
    | false => simp [prefixValue,headCount]
    | true =>
      simp only [prefixValue,headCount,List.all_cons,id_eq,Bool.true_and]
      rw [ih]
      omega

theorem prefix_value (W : Expr n) (v : Env n) : (prefixLength W).value v=List.replicate (headCount (W.value v)) true := by
  change (foldWordProgram (reverse W) (numeral 0) prefixStep).value v=_
  rw [foldWordProgram_value,reverse_value]
  change (W.value v).reverse.foldl (foldWordStep prefixStep v) (List.replicate 0 true)=_
  rw [prefix_fold,prefixValue_reverse]
  simp

@[simp] theorem prefix_number (W : Expr n) (v : Env n) : (prefixLength W).number v=headCount (W.value v) := by
  unfold Expr.number
  rw [prefix_value,List.length_replicate]

end VariableWL.Computation.Stack.PolyRecipe

namespace VariableWL.Encoding
open Computation.Stack.PolyRecipe

theorem header_headCount (w : Word) : header w=
    if headCount w<w.length then some (headCount w,w.drop (headCount w+1)) else none := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b with
    | false => simp [header,headCount]
    | true =>
      simp only [header,ih,headCount,List.length_cons]
      by_cases h : headCount w<w.length
      · simp [h,List.drop_succ_cons]
      · simp [h]

theorem bits_nonempty {a : ℕ} (h : a≠0) : a.bits≠[] := by
  intro he
  have hv := value_bits a
  rw [he] at hv
  exact h hv.symm

theorem bits_last (a : ℕ) : a.bits=[] ∨ a.bits.getLast?=some true := by
  induction a using Nat.binaryRec' with
  | zero => exact Or.inl rfl
  | bit b a ha ih =>
    rw [Nat.bits_append_bit _ _ ha]
    apply Or.inr
    by_cases h : a=0
    · subst a
      simp [ha rfl]
    · rw [List.getLast?_cons_of_ne_nil (bits_nonempty h)]
      exact ih.resolve_left (bits_nonempty h)

theorem value_positive {w : Word} (h : w.getLast?=some true) : 0<value w := by
  induction w with
  | nil => cases h
  | cons b w ih =>
    by_cases hw : w=[]
    · subst w
      simp only [List.getLast?_singleton,Option.some.injEq] at h
      subst b
      decide
    · rw [List.getLast?_cons_of_ne_nil hw] at h
      have hp := ih h
      change 0<Nat.bit b (value w)
      cases b <;> simp only [Nat.bit_false,Nat.bit_true] <;> omega

theorem canonical_iff (w : Word) : (value w).bits=w ↔ w=[] ∨ w.getLast?=some true := by
  constructor
  · intro h
    simpa only [h] using bits_last (value w)
  · intro h
    induction w with
    | nil => rfl
    | cons b w ih =>
      have hh : (b::w).getLast?=some true := h.resolve_left (by simp)
      by_cases hw : w=[]
      · subst w
        simp only [List.getLast?_singleton,Option.some.injEq] at hh
        subst b
        rfl
      · rw [List.getLast?_cons_of_ne_nil hw] at hh
        have hp := value_positive hh
        change (Nat.bit b (value w)).bits=b::w
        rw [Nat.bits_append_bit _ _ (by omega),ih (Or.inr hh)]

end VariableWL.Encoding

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n : ℕ}

theorem canonical_bit (W : Expr n) (v : Env n) : (canonical W).bit v=decide ((Encoding.value (W.value v)).bits=W.value v) := by
  apply Bool.eq_iff_iff.mpr
  rw [canonical,disj_bit,Bool.or_eq_true,eq_bit,decide_eq_true_eq,length_number,numeral_number]
  change ((W.value v).length=0 ∨ decide (((reverse W).value v).head?=some true)=true) ↔ _
  rw [reverse_value,List.head?_reverse,decide_eq_true_eq,decide_eq_true_eq,Encoding.canonical_iff,List.length_eq_zero_iff]

@[simp] theorem afterHeader_value (W : Expr n) (v : Env n) :
    (afterHeader W).value v=(W.value v).drop (headCount (W.value v)+1) := by
  rw [afterHeader,drop_value,add_number,prefix_number,numeral_number]
@[simp] theorem integerBits_value (W : Expr n) (v : Env n) :
    (integerBits W).value v=((W.value v).drop (headCount (W.value v)+1)).take (headCount (W.value v)) := by
  rw [integerBits,take_value,afterHeader_value,prefix_number]
@[simp] theorem afterInteger_value (W : Expr n) (v : Env n) :
    (afterInteger W).value v=((W.value v).drop (headCount (W.value v)+1)).drop (headCount (W.value v)) := by
  rw [afterInteger,drop_value,afterHeader_value,prefix_number]

theorem integer_spec (W : Expr n) (v : Env n) : Encoding.integer (W.value v)=
    if (integerValid W).bit v then some (Encoding.value ((integerBits W).value v),(afterInteger W).value v) else none := by
  rw [Encoding.integer,Encoding.header_headCount]
  simp only [integerValid,conj_bit,lt_bit,le_bit,prefix_number,length_number,canonical_bit,
    afterHeader_value,integerBits_value,afterInteger_value]
  simp only [Bool.and_eq_true,decide_eq_true_eq]
  split_ifs <;> simp_all

theorem integer_number_exact (W C : Expr n) (v : Env n)
    (h : Encoding.value ((integerBits W).value v)≤C.number v) :
    (integerNumber W C).number v=Encoding.value ((integerBits W).value v) := by
  rw [integerNumber,binary_number,min_eq_left h]

theorem integer_success (W C : Expr n) (v : Env n) (a : ℕ) (t : Word)
    (h : Encoding.value ((integerBits W).value v)≤C.number v) :
    Encoding.integer (W.value v)=some (a,t) ↔
    (integerValid W).bit v=true ∧ (integerNumber W C).number v=a ∧ (afterInteger W).value v=t := by
  rw [integer_spec,integer_number_exact W C v h]
  cases (integerValid W).bit v <;> simp

end VariableWL.Computation.Stack.PolyRecipe

namespace VariableWL.Encoding

theorem graph_spec (w u : Word) (a : ℕ) (b : Bool) (hi : integer w=if b then some (a,u) else none)
    (G : Graph) (t : Word) :
    graph w=some (G,t) ↔ (b=true ∧ MatrixValid a (u.take (a*a))) ∧
      G.order=a ∧ matrix G=u.take (a*a) ∧ u.drop (a*a)=t := by
  rw [graph,hi]
  cases b with
  | false => simp
  | true =>
    simp only [ite_true,Option.map_eq_some_iff,true_and]
    constructor
    · rintro ⟨G',hr,he⟩
      cases he
      have hs := readMatrix_sound hr
      have hv := matrix_valid G
      rw [hs.1,hs.2] at hv
      exact ⟨hv,hs.1,hs.2,rfl⟩
    · rintro ⟨hv,hn,hm,ht⟩
      refine ⟨G,?_,by rw [ht]⟩
      rw [← hm,← hn,readMatrix_matrix]

theorem matrix_exists (a : ℕ) (w : Word) (h : MatrixValid a w) :
    ∃G : Graph,G.order=a ∧ matrix G=w :=
  ⟨fromMatrix a w h,rfl,matrix_fromMatrix a w h⟩

end VariableWL.Encoding

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n : ℕ}

theorem matrixValid_bit (A N : Expr n) (v : Env n) :
    (matrixValid A N).bit v=true ↔ Encoding.MatrixValid (N.number v) (A.value v) := by
  simp only [matrixValid,conj_bit,Bool.and_eq_true,eq_bit,decide_eq_true_eq,length_number,mul_number,
    all_bit,List.all_eq_true,List.mem_range,bitEq_bit,matrixEntry_bit,
    up₂_value,up₂_number,up_value,up_number,input_number,cons_zero,NumericProgram.cons_one,
    List.length_replicate,neg_bit,Bool.not_eq_true']
  unfold Encoding.MatrixValid Encoding.entry
  constructor
  · rintro ⟨hlen,hs,hd⟩
    exact ⟨hlen,fun i j=>hs i.val i.isLt j.val j.isLt,fun i=>hd i.val i.isLt⟩
  · rintro ⟨hlen,hs,hd⟩
    exact ⟨hlen,fun i hi j hj=>hs ⟨i,hi⟩ ⟨j,hj⟩,fun i hi=>hd ⟨i,hi⟩⟩

theorem graph_success (W C : Expr n) (v : Env n) (G : Graph) (t : Word)
    (h : Encoding.value ((integerBits W).value v)≤C.number v) :
    Encoding.graph (W.value v)=some (G,t) ↔
    (graphValid W C).bit v=true ∧ G.order=(integerNumber W C).number v ∧
      Encoding.matrix G=(graphMatrix W C).value v ∧ (afterGraph W C).value v=t := by
  have hs := integer_spec W v
  rw [← integer_number_exact W C v h] at hs
  rw [graphValid,conj_bit,Bool.and_eq_true,matrixValid_bit,graphMatrix_value,afterGraph_value]
  exact Encoding.graph_spec _ _ _ _ hs G t

theorem graph_fields_valid (W C : Expr n) (v : Env n) (h : (graphValid W C).bit v=true) :
    Encoding.MatrixValid ((integerNumber W C).number v) ((graphMatrix W C).value v) := by
  rw [graphValid,conj_bit,Bool.and_eq_true,matrixValid_bit] at h
  exact h.2

end VariableWL.Computation.Stack.PolyRecipe

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n : ℕ}

theorem value_le_two_pow (w : Word) : Encoding.value w≤2^w.length := by
  have h := BinaryMachine.value_bound w.reverse 0
  rw [BinaryMachine.value_reverse] at h
  simp only [Nat.zero_mul,Nat.zero_add,List.length_reverse,Nat.one_mul] at h
  omega

theorem integerBits_length (W : Expr n) (v : Env n) : ((integerBits W).value v).length≤(W.value v).length := by
  rw [integerBits_value,List.length_take,List.length_drop]
  omega

theorem enough_integer (W C : Expr n) (v : Env n) (h : Enough W C v) :
    Encoding.value ((integerBits W).value v)≤C.number v :=
  (value_le_two_pow _).trans ((Nat.pow_le_pow_right (by omega) (integerBits_length W v)).trans h)

theorem afterGraph_length (W C : Expr n) (v : Env n) : ((afterGraph W C).value v).length≤(W.value v).length := by
  rw [afterGraph,drop_value,afterInteger_value,List.length_drop,List.length_drop,List.length_drop]
  omega

theorem enough_afterGraph (W C : Expr n) (v : Env n) (h : Enough W C v) : Enough (afterGraph W C) C v :=
  (Nat.pow_le_pow_right (by omega) (afterGraph_length W C v)).trans h

theorem pair_success (W C : Expr n) (v : Env n) (G H : Graph) (k : ℕ) (hc : Enough W C v) :
    Encoding.pair (W.value v)=some (G,H,k) ↔
    (pairValid W C).bit v=true ∧
      G.order=(integerNumber W C).number v ∧ Encoding.matrix G=(graphMatrix W C).value v ∧
      H.order=(integerNumber (secondWord W C) C).number v ∧ Encoding.matrix H=(graphMatrix (secondWord W C) C).value v ∧
      k=(integerNumber (dimensionWord W C) C).number v := by
  have h1 := enough_integer W C v hc
  have hc2 := enough_afterGraph W C v hc
  have h2 := enough_integer (secondWord W C) C v hc2
  have hc3 := enough_afterGraph (secondWord W C) C v hc2
  have h3 := enough_integer (dimensionWord W C) C v hc3
  constructor
  · intro hp
    unfold Encoding.pair at hp
    cases hg : Encoding.graph (W.value v) with
    | none => simp [hg] at hp
    | some q =>
      rcases q with ⟨G',u⟩
      have hG := (graph_success W C v G' u h1).mp hg
      have hu : (secondWord W C).value v=u := hG.2.2.2
      cases hh : Encoding.graph u with
      | none => simp [hg,hh] at hp
      | some q =>
        rcases q with ⟨H',t⟩
        have hH := (graph_success (secondWord W C) C v H' t h2).mp (hu.symm ▸ hh)
        have ht : (dimensionWord W C).value v=t := hH.2.2.2
        cases hk : Encoding.integer t with
        | none => simp [hg,hh,hk] at hp
        | some q =>
          rcases q with ⟨k',z⟩
          have hK := (integer_success (dimensionWord W C) C v k' z h3).mp (ht.symm ▸ hk)
          simp only [hg,hh,hk] at hp
          split_ifs at hp with hz
          cases Option.some.inj hp
          refine ⟨?_,hG.2.1,hG.2.2.1,hH.2.1,hH.2.2.1,hK.2.1.symm⟩
          simp only [pairValid,conj_bit,Bool.and_eq_true,eq_bit,decide_eq_true_eq,length_number,numeral_number]
          exact ⟨hG.1,hH.1,hK.1,by rw [hK.2.2,hz]; rfl⟩
  · rintro ⟨hp,hGn,hGm,hHn,hHm,hk⟩
    simp only [pairValid,conj_bit,Bool.and_eq_true,eq_bit,decide_eq_true_eq,length_number,numeral_number] at hp
    have hg := (graph_success W C v G ((secondWord W C).value v) h1).mpr ⟨hp.1,hGn,hGm,rfl⟩
    have hh := (graph_success (secondWord W C) C v H ((dimensionWord W C).value v) h2).mpr
      ⟨hp.2.1,hHn,hHm,rfl⟩
    have hz : (afterInteger (dimensionWord W C)).value v=[] := List.length_eq_zero_iff.mp hp.2.2.2
    have hki := (integer_success (dimensionWord W C) C v k [] h3).mpr ⟨hp.2.2.1,hk.symm,hz⟩
    simp only [Encoding.pair,hg,hh,hki,ite_true]

theorem pairValid_exists (W C : Expr n) (v : Env n) (hc : Enough W C v) :
    (pairValid W C).bit v=true ↔ ∃G H k,Encoding.pair (W.value v)=some (G,H,k) := by
  constructor
  · intro h
    have h' := h
    simp only [pairValid,conj_bit,Bool.and_eq_true] at h'
    obtain ⟨G,hGn,hGm⟩ := Encoding.matrix_exists _ _ (graph_fields_valid W C v h'.1)
    obtain ⟨H,hHn,hHm⟩ := Encoding.matrix_exists _ _ (graph_fields_valid (secondWord W C) C v h'.2.1)
    refine ⟨G,H,(integerNumber (dimensionWord W C) C).number v,?_⟩
    apply (pair_success W C v G H _ hc).mpr
    exact ⟨h,hGn,hGm,hHn,hHm,rfl⟩
  · rintro ⟨G,H,k,h⟩
    exact ((pair_success W C v G H k hc).mp h).1

end VariableWL.Computation.Stack.PolyRecipe

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_ExponentialRecipe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n : ℕ}

theorem strong_enough (W C : Expr n) (v : Env n) (h : StrongEnough W C v) : Enough W C v := by
  apply (Nat.pow_le_pow_right (by omega : 0<2) (show (W.value v).length≤((W.value v).length+2)^2+1 by nlinarith)).trans h

theorem parsed_eval (W C : Expr n) (v : Env n) (G H : Graph) (k : ℕ)
    (hc : Enough W C v) (hp : Encoding.pair (W.value v)=some (G,H,k)) :
    (parsedData W C).eval v=NumericRefinement.data G H (InputDecision.capped G k) := by
  obtain ⟨_,hGn,hGm,hHn,hHm,hk⟩ := (pair_success W C v G H k hc).mp hp
  unfold parsedData NumericProgram.Data.eval
  rw [minimum_number,maximum_number,numeral_number]
  change NumericRefinement.Data.mk ((integerNumber W C).number v) ((integerNumber (secondWord W C) C).number v)
    (min ((rawDimension W C).number v) (max 2 ((integerNumber W C).number v)))
    ((graphMatrix W C).value v) ((graphMatrix (secondWord W C) C).value v)=_
  change k=(rawDimension W C).number v at hk
  rw [← hGn,← hGm,← hHn,← hHm,← hk]
  rfl

theorem parsed_good (W C : Expr n) (v : Env n) (G H : Graph) (k : ℕ)
    (hc : StrongEnough W C v) (hp : Encoding.pair (W.value v)=some (G,H,k)) :
    (parsedData W C).Good v := by
  obtain ⟨_,hGn,_,hHn,_,hk⟩ := (pair_success W C v G H k (strong_enough W C v hc)).mp hp
  have hcount := (RefinementSize.capped_count_bound hp).trans hc
  have h1 : 1≤C.number v := (Nat.succ_le_of_lt (pow_pos (by omega : 0<2) _)).trans hc
  change k=(rawDimension W C).number v at hk
  simp only [NumericProgram.Data.Good,parsedData,minimum_number,maximum_number,numeral_number]
  rw [← hGn,← hHn,← hk]
  change 1≤C.number v ∧ G.order^InputDecision.capped G k≤C.number v ∧ H.order^InputDecision.capped G k≤C.number v
  unfold RefinementArray.count at hcount
  exact ⟨h1,by omega,by omega⟩

theorem generalProgram_correct (W C : Expr n) (v : Env n) (hc : StrongEnough W C v) :
    (generalProgram W C).bit v=true ↔ W.value v ∈ WL := by
  have hc' := strong_enough W C v hc
  cases hp : Encoding.pair (W.value v) with
  | none =>
    have hf : (pairValid W C).bit v≠true := by
      intro h
      obtain ⟨G,H,k,h⟩ := (pairValid_exists W C v hc').mp h
      rw [hp] at h
      contradiction
    rw [generalProgram,conj_bit,Bool.and_eq_true]
    constructor
    · rintro ⟨h,_⟩; exact (hf h).elim
    · intro h; exact (Encoding.malformed_not_WL hp h).elim
  | some q =>
    rcases q with ⟨G,H,k⟩
    obtain ⟨hv,_,_,_,_,hk⟩ := (pair_success W C v G H k hc').mp hp
    change k=(rawDimension W C).number v at hk
    have hgood := parsed_good W C v G H k hc hp
    have heval := parsed_eval W C v G H k hc' hp
    have he : (parsedData W C).accepts.bit v=true ↔ Equivalent G H (InputDecision.capped G k) := by
      unfold Expr.bit
      rw [NumericProgram.accepts_value _ _ hgood,heval]
      simp only [List.head?_cons,Option.some.injEq,decide_bool]
      exact NumericRefinement.accepts_correct G H (InputDecision.capped G k)
    simp only [generalProgram,conj_bit,Bool.and_eq_true,hv,true_and]
    rw [le_bit,numeral_number,← hk,decide_eq_true_eq,he,Encoding.pair_sound hp,Encoding.pair_mem_WL]
    exact and_congr_right fun h => (InputDecision.equivalent_capped G H h).symm

theorem generalProgram_value (W C : Expr n) (v : Env n) :
    (generalProgram W C).value v=[(generalProgram W C).bit v] := by
  simp only [generalProgram,conj_value,conj_bit]

end VariableWL.Computation.Stack.PolyRecipe

namespace VariableWL.Computation.Stack.Recipe
variable {n : ℕ}

theorem iterate_controlled {B Z : Certified n} {Q : Certified (n+2)}
    (hB : Poly B) (hZ : Poly Z) (hQ : Poly Q) :
    ∃f : ℕ → ℕ, Growth f ∧ ∀C v,EnvBound C v →
      (∀j≤(B.value v).length,(foldValue Q v (Z.value v) j).length≤C) →
      (iterate B Z Q).time v+((iterate B Z Q).value v).length≤f C := by
  obtain ⟨b,hb,hB⟩ := hB
  obtain ⟨z,hz,hZ⟩ := hZ
  obtain ⟨q,hq,hQ⟩ := hQ
  let D : ℕ → ℕ := fun C=>b C+C+C
  have hD : Growth D := (hb.add Growth.ident).add Growth.ident
  refine ⟨fun C=>13*(b C+z C+C)+(q (D C)+3*C+6)*b C+24,?_,?_⟩
  · exact (((Growth.constant 13).mul ((hb.add hz).add Growth.ident)).add
      ((((hq.comp hD).add ((Growth.constant 3).mul Growth.ident)).add (Growth.constant 6)).mul hb)).add (Growth.constant 24)
  · intro C v hv hacc
    have h1 := hB C v hv
    have h2 := hZ C v hv
    have h3 := hacc (B.value v).length le_rfl
    have hcost (j : ℕ) (hj : j<(B.value v).length) : foldTime Q v (Z.value v) j≤q (D C)+3*C+2 := by
      have h4 := hacc j (by omega)
      have hev : EnvBound (D C) (cons (foldValue Q v (Z.value v) j) (cons (List.replicate j true) v)) := by
        apply envBound_cons
        · apply envBound_cons
          · intro i; have := hv i; dsimp only [D]; omega
          · simp only [List.length_replicate]; dsimp only [D]; omega
        · dsimp only [D]; omega
      have h5 := hQ (D C) _ hev
      unfold foldTime
      omega
    have htot := BoundedLoop.total_bound (B.value v).length (q (D C)+3*C+2) _ hcost
    have htot' : BoundedLoop.total (B.value v).length (foldTime Q v (Z.value v))≤
        (q (D C)+3*C+6)*b C := by
      apply htot.trans
      have hm := Nat.mul_le_mul_left (q (D C)+3*C+6) (show (B.value v).length≤b C by omega)
      simpa only [Nat.add_assoc] using hm
    rw [iterate_time,iterate_value]
    dsimp only
    omega

theorem power_prefix (B : Certified n) (v : Env n) (j : ℕ) :
    foldValue (times (input 0) (B.reindex (fun i=>i.succ.succ))) v [true] j=
      List.replicate ((B.value v).length^j) true := by
  have h := power_value B (literal (List.replicate j true)) v
  rw [power,iterate_value] at h
  simpa only [literal_value,List.length_replicate] using h

theorem outputs (P : Certified 1) : ∃M : VariableWL.Machine,∀w : Word,
    OutputsWithin M w (P.value (fun _=>w.reverse)) (4*(w.length+P.time (fun _=>w.reverse)+1)) := by
  obtain ⟨M,hM⟩ := Procedure.outputs (1 : Fin 2) (P.compiled 1 (fun _=>0) 1)
  refine ⟨M,fun w=>?_⟩
  have h := hM w
  have he : (fun j : Fin 2=>if j=0 then w.reverse else []) ∘ (fun _ : Fin 1=>(0 : Fin 2))=(fun _=>w.reverse) := rfl
  simp only [Function.update_self,he,show (1 : Fin 2)≠0 by decide,ite_false,List.length_nil,Nat.mul_zero,Nat.add_zero] at h
  exact h

end VariableWL.Computation.Stack.Recipe

namespace VariableWL.Computation.Stack.ExponentialRecipe
open Recipe PolyRecipe

theorem exponent_number (v : Env 1) : exponent.number v=((v 0).length+2)^2+1 := by
  simp only [exponent,add_number,mul_number,length_number,PolyRecipe.input_value,numeral_number,pow_two]

theorem capacity_value (v : Env 1) : capacity.value v=List.replicate (size v) true := by
  rw [capacity,Recipe.power_value]
  change List.replicate (2^exponent.number v) true=_
  rw [exponent_number]
  rfl

theorem input_le_size (v : Env 1) : (v 0).length≤ size v := by
  have hh := Nat.lt_two_pow_self (n := ((v 0).length+2)^2+1)
  unfold size
  nlinarith

theorem envBound_size (v : Env 1) : EnvBound (size v) v := by
  intro i
  have hi : i=0 := Fin.eq_zero i
  subst i
  exact input_le_size v

theorem capacity_cost : ∃f : ℕ → ℕ,Growth f ∧ ∀v,capacity.time v+(capacity.value v).length≤f (size v) := by
  obtain ⟨f,hf,h⟩ := Recipe.iterate_controlled exponent.polynomial (poly_literal [true])
    (poly_times (poly_input (0 : Fin 3)) (poly_reindex (poly_literal [true,true]) (fun i : Fin 1=>i.succ.succ)))
  refine ⟨f,hf,fun v=>h (size v) v (envBound_size v) ?_⟩
  intro j hj
  rw [Recipe.literal_value,Recipe.power_prefix,Recipe.literal_value,List.length_replicate]
  change 2^j≤ size v
  apply Nat.pow_le_pow_right (by omega)
  change j≤exponent.number v at hj
  rw [exponent_number] at hj
  exact hj

theorem full_value (Q : Expr 2) (v : Env 1) :
    (full Q).value v=Q.value (cons (List.replicate (size v) true) v) := by
  change Q.value (cons (capacity.value v) v)=_
  rw [capacity_value]

theorem full_cost (Q : Expr 2) : ∃f : ℕ → ℕ,Growth f ∧ ∀v,(full Q).time v≤f (size v) := by
  obtain ⟨a,ha,hA⟩ := capacity_cost
  obtain ⟨b,hb,hB⟩ := Q.polynomial
  refine ⟨fun C=>a C+b C+3*C+2,((ha.add hb).add ((Growth.constant 3).mul Growth.ident)).add (Growth.constant 2),?_⟩
  intro v
  have hbv : EnvBound (size v) (cons (capacity.value v) v) :=
    envBound_cons (envBound_size v) (by rw [capacity_value,List.length_replicate])
  have ht := hB (size v) _ hbv
  have hc := hA v
  change capacity.time v+Q.program.time (cons (capacity.value v) v)+3*(capacity.value v).length+2≤_
  simp only [capacity_value,List.length_replicate] at hc ht ⊢
  omega

theorem inEXPTIME (Q : Expr 2) (L : Language)
    (hword : ∀w,Q.value (environment w)=[Q.bit (environment w)])
    (hcorrect : ∀w,Q.bit (environment w)=true ↔ w∈L) : InEXPTIME L := by
  obtain ⟨M,hM⟩ := Recipe.outputs (full Q)
  obtain ⟨f,hf,hF⟩ := full_cost Q
  let g : ℕ → ℕ := fun C=>4*(C+f C+1)
  have hg : Growth g := (Growth.constant 4).mul ((Growth.ident.add hf).add (Growth.constant 1))
  obtain ⟨c,d,hg⟩ := hg
  refine ⟨M,16*(c+d+1),2,fun w=>⟨Q.bit (environment w),hcorrect w,?_⟩⟩
  have hm := hM w
  rw [full_value] at hm
  have hs : size (fun _ : Fin 1=>w.reverse)=2^((w.length+2)^2+1) := by simp only [size,List.length_reverse]
  rw [hs] at hm
  change OutputsWithin M w (Q.value (environment w)) _ at hm
  rw [hword] at hm
  have htime := hF (fun _ : Fin 1=>w.reverse)
  have hlen := input_le_size (fun _ : Fin 1=>w.reverse)
  rw [List.length_reverse] at hlen
  have hbound : 4*(w.length+(full Q).time (fun _=>w.reverse)+1)≤g (size (fun _ : Fin 1=>w.reverse)) := by
    dsimp only [g]
    omega
  have hp := RefinementSize.polynomial_of_exponential c d (w.length+2) (size (fun _ : Fin 1=>w.reverse))
    (by rw [hs,pow_two])
  have hfinal : (c+d+1)*(w.length+2+2)^2≤(16*(c+d+1))*(w.length+1)^2 := by
    have hb : w.length+2+2≤4*(w.length+1) := by omega
    have hh := Nat.pow_le_pow_left hb 2
    have hm := Nat.mul_le_mul_left (c+d+1) hh
    nlinarith
  obtain ⟨t,ht,hhalt,hout⟩ := hm
  exact ⟨t,ht.trans (hbound.trans ((hg _).trans (hp.trans (Nat.pow_le_pow_right (by omega) hfinal)))),hhalt,hout⟩

end VariableWL.Computation.Stack.ExponentialRecipe

namespace VariableWL.Computation.Stack.ExponentialRecipe
open Recipe PolyRecipe

theorem general_upper : InEXPTIME WL := by
  apply inEXPTIME general WL
  · intro w; exact generalProgram_value _ _ _
  · intro w
    have hv : (PolyRecipe.reverse (PolyRecipe.input (1 : Fin 2))).value (environment w)=w := by
      change w.reverse.reverse=w
      exact List.reverse_reverse w
    have hc : StrongEnough (PolyRecipe.reverse (PolyRecipe.input 1)) (PolyRecipe.input 0) (environment w) := by
      unfold StrongEnough
      rw [hv,input_number]
      simp only [environment,cons_zero,List.length_replicate]
      exact le_rfl
    have h := generalProgram_correct _ _ _ hc
    rw [hv] at h
    exact h

end VariableWL.Computation.Stack.ExponentialRecipe

namespace VariableWL.NumericPromise
attribute [local instance] Classical.propDecidable

theorem get_pack (n : ℕ) (f : ℕ → ℕ → Bool) (a b : Fin n) :
    get n (pack n f) a b=f a b := by
  have hn : 0<n := Nat.zero_lt_of_lt a.isLt
  have hp : a.val*n+b.val<n*n := by
    have := Nat.mul_le_mul_right n (Nat.succ_le_of_lt a.isLt)
    nlinarith [b.isLt]
  unfold get pack
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map,List.length_range] using hp)]
  simp only [List.getElem_map,List.getElem_range]
  have hd : (a.val*n+b.val)/n=a.val := by
    rw [Nat.mul_comm a.val n,Nat.mul_add_div hn,Nat.div_eq_of_lt b.isLt,Nat.add_zero]
  rw [hd]
  rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt b.isLt]

theorem get_matrix (G : Graph) (a b : Fin G.order) :
    get G.order (Encoding.matrix G) a b=decide (G.graph.Adj a b) := Encoding.entry_matrix G a b

theorem array_correct (G : Graph) (j : ℕ) (a b : Fin G.order) :
    get G.order (array G.order (Encoding.matrix G) j) a b=PromiseDecision.reach G j a b := by
  induction j generalizing a b with
  | zero =>
    rw [array,get_pack,PromiseDecision.reach]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq,Fin.val_inj]
  | succ j ih =>
    rw [array,get_pack,update,ih,PromiseDecision.reach]
    congr 1
    rw [← List.map_coe_finRange_eq_range,List.any_map]
    apply congrArg (fun p : Fin G.order → Bool=>(List.finRange G.order).any p)
    funext z
    dsimp only [Function.comp_def]
    rw [get_matrix,ih]

theorem connected_correct (G : Graph) : connected G.order (Encoding.matrix G)=PromiseDecision.connected G := by
  unfold connected PromiseDecision.connected
  rw [← List.map_coe_finRange_eq_range]
  simp only [List.all_map,Function.comp_def,array_correct]

theorem subcubic_correct (G : Graph) : subcubic G.order (Encoding.matrix G)=PromiseDecision.subcubic G := by
  unfold subcubic PromiseDecision.subcubic PromiseDecision.neighbors
  rw [← List.map_coe_finRange_eq_range]
  simp only [List.all_map,List.filter_map,Function.comp_def,get_matrix,List.length_map,List.countP_eq_length_filter]

end VariableWL.NumericPromise

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_Descriptor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n : ℕ}

theorem reachPrefix_value (N A : Expr n) (v : Env n) (j : ℕ) :
    Recipe.foldValue (reachBody N A).program v ((reachInitial N).value v) j=
      NumericPromise.array (N.number v) (A.value v) j := by
  induction j with
  | zero => exact reachInitial_value N v
  | succ j ih =>
    change (reachNext N.up₂ A.up₂ (input 0)).value _=_
    rw [reachNext_value]
    simp only [up₂_number,up₂_value,input_value,cons_zero,ih]
    rfl

theorem reachArray_value (N A : Expr n) (v : Env n) :
    (reachArray N A).value v=NumericPromise.array (N.number v) (A.value v) (N.number v) := by
  change (Recipe.iterate N.program (reachInitial N).program (reachBody N A).program).value v=_
  rw [Recipe.iterate_value]
  exact reachPrefix_value N A v (N.number v)

theorem connectedProgram_bit (N A : Expr n) (v : Env n) :
    (connectedProgram N A).bit v=NumericPromise.connected (N.number v) (A.value v) := by
  simp only [connectedProgram,conj_bit,lt_bit,numeral_number,all_bit,matrixEntry_bit,up_number,up₂_number,
    up₂_value,reachArray_value,input_number,NumericProgram.cons_one,cons_zero,List.length_replicate]
  rfl

theorem subcubicProgram_bit (N A : Expr n) (v : Env n) :
    (subcubicProgram N A).bit v=NumericPromise.subcubic (N.number v) (A.value v) := by
  simp only [subcubicProgram,all_bit,le_bit,count_number,matrixEntry_bit,up_number,up₂_number,
    up₂_value,numeral_number,input_number,NumericProgram.cons_one,cons_zero,List.length_replicate]
  rfl

end VariableWL.Computation.Stack.PolyRecipe

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n : ℕ}

theorem promiseProgram_correct (N M A B : Expr n) (v : Env n) (G H : Graph)
    (hN : N.number v=G.order) (hM : M.number v=H.order)
    (hA : A.value v=Encoding.matrix G) (hB : B.value v=Encoding.matrix H) :
    (promiseProgram N M A B).bit v=true ↔
      0<G.order ∧ G.order=H.order ∧ G.graph.Connected ∧ H.graph.Connected ∧ Subcubic G ∧ Subcubic H := by
  simp only [promiseProgram,conj_bit,Bool.and_eq_true,lt_bit,eq_bit,numeral_number,
    connectedProgram_bit,subcubicProgram_bit,hN,hM,hA,hB,decide_eq_true_eq,
    NumericPromise.connected_correct,NumericPromise.subcubic_correct,
    PromiseDecision.connected_correct,PromiseDecision.subcubic_correct]

theorem subProgram_correct (W C : Expr n) (v : Env n) (hc : StrongEnough W C v) :
    (subProgram W C).bit v=true ↔ W.value v∈SubWL := by
  have hg := generalProgram_correct W C v hc
  cases hp : Encoding.pair (W.value v) with
  | none =>
    rw [subProgram,conj_bit,Bool.and_eq_true,hg]
    constructor
    · rintro ⟨h,_⟩; exact (Encoding.malformed_not_WL hp h).elim
    · intro h; exact (Encoding.malformed_not_SubWL hp h).elim
  | some q =>
    rcases q with ⟨G,H,k⟩
    obtain ⟨_,hGn,hGm,hHn,hHm,_⟩ := (pair_success W C v G H k (strong_enough W C v hc)).mp hp
    have hpromise := promiseProgram_correct (integerNumber W C) (integerNumber (secondWord W C) C)
      (graphMatrix W C) (graphMatrix (secondWord W C) C) v G H hGn.symm hHn.symm hGm.symm hHm.symm
    rw [subProgram,conj_bit,Bool.and_eq_true,hg,hpromise,Encoding.pair_sound hp,
      Encoding.pair_mem_WL,Encoding.pair_mem_SubWL]
    constructor
    · rintro ⟨⟨h₁,h₈⟩,h₂,h₃,h₄,h₅,h₆,h₇⟩
      exact ⟨h₁,h₂,h₃,h₄,h₅,h₆,h₇,h₈⟩
    · rintro ⟨h₁,h₂,h₃,h₄,h₅,h₆,h₇,h₈⟩
      exact ⟨⟨h₁,h₈⟩,h₂,h₃,h₄,h₅,h₆,h₇⟩

theorem subProgram_value (W C : Expr n) (v : Env n) :
    (subProgram W C).value v=[(subProgram W C).bit v] := by
  simp only [subProgram,conj_value,conj_bit]

end VariableWL.Computation.Stack.PolyRecipe

namespace VariableWL.Computation.Stack.ExponentialRecipe
open Recipe PolyRecipe

theorem subcubic_upper : InEXPTIME SubWL := by
  apply inEXPTIME subcubic SubWL
  · intro w; exact subProgram_value _ _ _
  · intro w
    have hv : (PolyRecipe.reverse (PolyRecipe.input (1 : Fin 2))).value (environment w)=w := by
      change w.reverse.reverse=w
      exact List.reverse_reverse w
    have hc : StrongEnough (PolyRecipe.reverse (PolyRecipe.input 1)) (PolyRecipe.input 0) (environment w) := by
      unfold StrongEnough
      rw [hv,input_number]
      simp only [environment,cons_zero,List.length_replicate]
      exact le_rfl
    have h := subProgram_correct _ _ _ hc
    rw [hv] at h
    exact h

end VariableWL.Computation.Stack.ExponentialRecipe

end OAI
end

section
-- module Solutions.OAIQ6_WL.VariableWL_Completeness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uVariable1 uVariable2

namespace VariableWL
 theorem main_oai : EXPTIMEComplete WL ∧ EXPTIMEComplete SubWL :=
  ⟨⟨Computation.Stack.ExponentialRecipe.general_upper,general_hard⟩,
    ⟨Computation.Stack.ExponentialRecipe.subcubic_upper,subcubic_hard⟩⟩
end VariableWL

end OAI
end

theorem solution : type_of% @OAI.VariableWL.main_oai := @OAI.VariableWL.main_oai
