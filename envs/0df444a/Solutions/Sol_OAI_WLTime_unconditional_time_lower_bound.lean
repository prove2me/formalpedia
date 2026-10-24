-- Prove2me | solution 1 for OAI.WLTime.unconditional_time_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T21:51:43.717351+00:00
-- url     : https://prove2.me/submissions/0e8d2e5b-1b95-4e7c-81e7-d9d7831d93b4

import Mathlib
import Definitions.Def_WeisfeilerLeman
import Definitions.Def_OAIQWWLT000
import Theorems.Thm_OAI_WLTime_OneTape_Symbolic_FullWriter_consumer_correct
import Theorems.Thm_OAI_WLTime_OneTape_Symbolic_RAMWriter_correct

section
-- module Solutions.OAIQW_WLTime.Colors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα uβ uC uγ

namespace WLTime

theorem equiv_of_multiset_match {α : Type uα} {β : Type uβ} {C : Type uC} [Fintype α] [Fintype β]
    (f : α → C) (g : β → C)
    (h : Finset.univ.val.map f = Finset.univ.val.map g) :
    ∃ e : α ≃ β, ∀ a, f a = g (e a) := by
  classical
  have hfiber (c : C) : Fintype.card {a // f a = c} = Fintype.card {b // g b = c} := by
    have hc := congrArg (Multiset.count c) h
    simpa only [Multiset.count_map, Fintype.card_subtype, Finset.card_def,
      Finset.filter_val, eq_comm] using hc
  let e (c : C) := Fintype.equivOfCardEq (hfiber c)
  exact ⟨Equiv.ofFiberEquiv e, fun a => (Equiv.ofFiberEquiv_map e a).symm⟩

theorem multiset_match_of_equiv {α : Type uα} {β : Type uβ} {C : Type uC} [Fintype α] [Fintype β]
    (f : α → C) (g : β → C) (e : α ≃ β) (h : ∀ a, f a = g (e a)) :
    Finset.univ.val.map f = Finset.univ.val.map g := by
  have he : Finset.univ.val.map e = (Finset.univ : Finset β).val := by
    exact (Finset.map_val e.toEmbedding Finset.univ).symm.trans
      (congrArg Finset.val (Finset.univ_map_equiv_to_embedding e))
  rw [← he, Multiset.map_map]
  exact Multiset.map_congr rfl (fun a _ => h a)

theorem finite_decreasing_choice {α : Type uα} [Fintype α] (R : ℕ → α → Prop)
    (mono : ∀ s t, s ≤ t → ∀ a, R t a → R s a)
    (exists_at : ∀ t, ∃ a, R t a) : ∃ a, ∀ t, R t a := by
  classical
  by_contra! h
  choose t ht using h
  obtain ⟨a, ha⟩ := exists_at (Finset.univ.sup t)
  exact ht a (mono _ _ (Finset.le_sup (Finset.mem_univ a)) a ha)

theorem tupleColor_eq_of_le {n k s t : ℕ} {c : Convention} {G H : Graph n}
    {v w : Fin k → Fin n} (hst : s ≤ t)
    (heq : tupleColor c k G t v = tupleColor c k H t w) :
    tupleColor c k G s v = tupleColor c k H s w := by
  induction hst with
  | refl => exact heq
  | @step t h ih =>
    apply ih
    cases c <;> exact congrArg Prod.fst heq

theorem equivalent_stable_matching {n k : ℕ} {c : Convention} {G H : Graph n}
    (heq : Equivalent c k G H) :
    ∃ e : (Fin k → Fin n) ≃ (Fin k → Fin n), ∀ v, Stable c k G H v (e v) := by
  classical
  have h := finite_decreasing_choice
    (fun t (e : (Fin k → Fin n) ≃ (Fin k → Fin n)) =>
      ∀ v, tupleColor c k G t v = tupleColor c k H t (e v))
    (fun s t hst e he v => tupleColor_eq_of_le hst (he v))
    (fun t => equiv_of_multiset_match _ _ (heq t))
  obtain ⟨e, he⟩ := h
  exact ⟨e, fun v t => he t v⟩

theorem stable_joint_extension {n k : ℕ} {G H : Graph n} {v w : Fin k → Fin n}
    (h : Stable .joint k G H v w) :
    ∃ e : Fin n ≃ Fin n, ∀ z i,
      Stable .joint k G H (Function.update v i z) (Function.update w i (e z)) := by
  classical
  have hmatch (t : ℕ) : ∃ e : Fin n ≃ Fin n, ∀ z i,
      tupleColor .joint k G t (Function.update v i z) =
        tupleColor .joint k H t (Function.update w i (e z)) := by
    have ht := congrArg Prod.snd (h (t + 1))
    dsimp only [tupleColor] at ht
    obtain ⟨e, he⟩ := equiv_of_multiset_match _ _ ht
    exact ⟨e, fun z i => congrFun (he z) i⟩
  obtain ⟨e, he⟩ := finite_decreasing_choice _
    (fun s t hst e he z i => tupleColor_eq_of_le hst (he z i)) hmatch
  exact ⟨e, fun z i t => he t z i⟩

theorem stable_separate_extension {n k : ℕ} {G H : Graph n} {v w : Fin k → Fin n}
    (h : Stable .separate k G H v w) (i : Fin k) :
    ∃ e : Fin n ≃ Fin n, ∀ z,
      Stable .separate k G H (Function.update v i z) (Function.update w i (e z)) := by
  classical
  have hmatch (t : ℕ) : ∃ e : Fin n ≃ Fin n, ∀ z,
      tupleColor .separate k G t (Function.update v i z) =
        tupleColor .separate k H t (Function.update w i (e z)) := by
    have ht := congrFun (congrArg Prod.snd (h (t + 1))) i
    dsimp only [tupleColor] at ht
    exact equiv_of_multiset_match _ _ ht
  obtain ⟨e, he⟩ := finite_decreasing_choice _
    (fun s t hst e he z => tupleColor_eq_of_le hst (he z)) hmatch
  exact ⟨e, fun z t => he t z⟩

end WLTime

namespace WLTime

theorem tupleColor_permute {n k : ℕ} (c : Convention) (G : Graph n)
    (π : Equiv.Perm (Fin k)) (t : ℕ) (v : Fin k → Fin n) :
    tupleColor c k G t (v ∘ π) = permuteColor c k π t (tupleColor c k G t v) := by
  induction t generalizing v with
  | zero => rfl
  | succ t ih =>
    cases c with
    | joint =>
      apply Prod.ext (ih v)
      dsimp only [tupleColor, permuteColor]
      rw [Multiset.map_map]
      apply Multiset.map_congr rfl
      intro z _
      funext i
      rw [← Function.update_comp_eq_of_injective v π.injective i z]
      exact ih (Function.update v (π i) z)
    | separate =>
      apply Prod.ext (ih v)
      funext i
      dsimp only [tupleColor, permuteColor]
      rw [Multiset.map_map]
      apply Multiset.map_congr rfl
      intro z _
      rw [← Function.update_comp_eq_of_injective v π.injective i z]
      exact ih (Function.update v (π i) z)

theorem Stable.permute {n k : ℕ} {c : Convention} {G H : Graph n}
    {v w : Fin k → Fin n} (h : Stable c k G H v w) (π : Equiv.Perm (Fin k)) :
    Stable c k G H (v ∘ π) (w ∘ π) := by
  intro t
  rw [tupleColor_permute, tupleColor_permute, h t]

end WLTime

namespace WLTime

theorem Wins.forget {n K : ℕ} {G H : Graph n} {P Q : Position K n}
    (h : Wins G H Q) (hPQ : P.Sub Q) : Wins G H P := by
  obtain ⟨I, hI⟩ := h
  exact ⟨I, I.forget hI hPQ⟩

theorem Wins.atomic {n K : ℕ} {G H : Graph n} {P : Position K n}
    (h : Wins G H P) : P.PartialIso G H := by
  obtain ⟨I, hI⟩ := h
  exact I.atomic hI

theorem Wins.extend {n K : ℕ} {G H : Graph n} {P : Position K n}
    (h : Wins G H P) (i : Fin K) (hi : P i = none) :
    ∃ e : Fin n ≃ Fin n, ∀ z, Wins G H (Function.update P i (some (z, e z))) := by
  obtain ⟨I, hI⟩ := h
  obtain ⟨e, he⟩ := I.extend hI i hi
  exact ⟨e, fun z => ⟨I, he z⟩⟩

private theorem injective_update_fresh {α : Type uα} {β : Type uβ} [DecidableEq α]
    {f : α → β} (hf : Function.Injective f) (i : α) (b : β)
    (fresh : ∀ a, f a ≠ b) : Function.Injective (Function.update f i b) := by
  intro a c h
  by_cases ha : a = i
  · subst a
    by_cases hc : c = i
    · exact hc.symm
    · simp only [Function.update_self, Function.update_of_ne hc] at h
      exact (fresh c h.symm).elim
  · by_cases hc : c = i
    · subst c
      simp only [Function.update_self, Function.update_of_ne ha] at h
      exact (fresh a h).elim
    · simp only [Function.update_of_ne ha, Function.update_of_ne hc] at h
      exact hf h

private theorem exists_fresh_slot {k K : ℕ} (hk : k < K) (slot : Fin k → Fin K) :
    ∃ j, ∀ i, slot i ≠ j := by
  by_contra! h
  have hc := Fintype.card_le_of_surjective slot h
  simp only [Fintype.card_fin] at hc
  omega

private theorem atomic_of_wins_marks {n K k : ℕ} {G H : Graph n}
    {P : Position K n} {slot : Fin k → Fin K} {v w : Fin k → Fin n}
    (hP : Wins G H P) (hm : Marks P slot v w) (c : Convention) :
    tupleColor c k G 0 v = tupleColor c k H 0 w := by
  apply Prod.ext
  · funext i j
    change decide (v i = v j) = decide (w i = w j)
    exact decide_eq_decide.mpr (hP.atomic (slot i) (slot j)
      (v i) (w i) (v j) (w j) (hm i) (hm j)).1
  · funext i j
    exact (hP.atomic (slot i) (slot j) (v i) (w i) (v j) (w j) (hm i) (hm j)).2

theorem joint_color_of_wins {n K k : ℕ} {G H : Graph n} (hk : k < K)
    (t : ℕ) {P : Position K n} {slot : Fin k → Fin K}
    (hs : Function.Injective slot) {v w : Fin k → Fin n}
    (hP : Wins G H P) (hm : Marks P slot v w) :
    tupleColor .joint k G t v = tupleColor .joint k H t w := by
  classical
  induction t generalizing P slot v w with
  | zero => exact atomic_of_wins_marks hP hm .joint
  | succ t ih =>
    obtain ⟨j, hj⟩ := exists_fresh_slot hk slot
    let P₀ : Position K n := fun l => if l ∈ Set.range slot then P l else none
    have h₀ : Wins G H P₀ := hP.forget (fun l => by
      by_cases hl : l ∈ Set.range slot
      · exact Or.inr (ite_eq_left hl)
      · exact Or.inl (ite_eq_right hl))
    have h₀j : P₀ j = none := by
      simp only [P₀, Set.mem_range]
      exact ite_eq_right (by rintro ⟨i, hi⟩; exact hj i hi)
    obtain ⟨e, he⟩ := h₀.extend j h₀j
    apply Prod.ext (ih hs hP hm)
    apply multiset_match_of_equiv _ _ e
    intro z
    funext i
    apply ih (injective_update_fresh hs i j hj) (he z)
    intro l
    by_cases hl : l = i
    · subst l
      simp only [Function.update_self]
    · simp only [Function.update_of_ne hl, Function.update_of_ne (hj l), P₀]
      rw [ite_eq_left (Set.mem_range_self l)]
      exact hm l

theorem separate_color_of_wins {n K k : ℕ} {G H : Graph n}
    (t : ℕ) {P : Position K n} {slot : Fin k → Fin K}
    (hs : Function.Injective slot) {v w : Fin k → Fin n}
    (hP : Wins G H P) (hm : Marks P slot v w) :
    tupleColor .separate k G t v = tupleColor .separate k H t w := by
  classical
  induction t generalizing P v w with
  | zero => exact atomic_of_wins_marks hP hm .separate
  | succ t ih =>
    apply Prod.ext (ih hP hm)
    funext i
    let P₀ := Function.update P (slot i) none
    have h₀ : Wins G H P₀ := hP.forget (fun l => by
      by_cases hl : l = slot i <;> simp [P₀, hl])
    obtain ⟨e, he⟩ := h₀.extend (slot i) (Function.update_self _ _ _)
    apply multiset_match_of_equiv _ _ e
    intro z
    apply ih (he z)
    intro l
    by_cases hl : l = i
    · subst l
      simp only [Function.update_self]
    · have hl' : slot l ≠ slot i := fun heq => hl (hs heq)
      simp only [Function.update_of_ne hl, Function.update_of_ne hl', P₀]
      exact hm l

end WLTime

namespace WLTime

theorem Position.Sub.refl {n K : ℕ} (P : Position K n) : P.Sub P :=
  fun _ => Or.inr rfl

theorem Position.Sub.trans {n K : ℕ} {P Q R : Position K n}
    (hPQ : P.Sub Q) (hQR : Q.Sub R) : P.Sub R := by
  intro i
  rcases hPQ i with hi | hi
  · exact Or.inl hi
  · rcases hQR i with hj | hj
    · exact Or.inl (hi.trans hj)
    · exact Or.inr (hi.trans hj)

theorem Position.Sub.mark {n K : ℕ} {P Q : Position K n} (hPQ : P.Sub Q)
    {i : Fin K} {x y : Fin n} (hi : P i = some (x, y)) : Q i = some (x, y) := by
  rcases hPQ i with h | h
  · rw [hi] at h
    contradiction
  · exact h.symm.trans hi

theorem wins_matching {n K k : ℕ} {G H : Graph n} {P : Position K n}
    (hP : Wins G H P) (slot : Fin k → Fin K) (hs : Function.Injective slot)
    (hfree : ∀ i, P (slot i) = none) :
    ∃ e : (Fin k → Fin n) ≃ (Fin k → Fin n), ∀ v,
      ∃ Q, Wins G H Q ∧ P.Sub Q ∧ Marks Q slot v (e v) := by
  classical
  induction k generalizing P with
  | zero =>
    refine ⟨Equiv.refl _, fun v => ⟨P, hP, Position.Sub.refl P, ?_⟩⟩
    intro i
    exact Fin.elim0 i
  | succ k ih =>
    obtain ⟨e, he⟩ := hP.extend (slot 0) (hfree 0)
    have hex (z : Fin n) := ih (he z) (slot ∘ Fin.succ)
      (hs.comp (Fin.succ_injective k)) (fun i => by
        have hi : slot i.succ ≠ slot 0 := fun h => Fin.succ_ne_zero i (hs h)
        simpa only [Function.comp_apply, Function.update_of_ne hi] using hfree i.succ)
    choose es hes using hex
    let F : (Fin (k + 1) → Fin n) ≃ (Fin (k + 1) → Fin n) :=
      (Fin.consEquiv (fun _ : Fin (k + 1) => Fin n)).symm |>.trans
        ((Equiv.prodCongrRight es).trans
          ((Equiv.prodCongr e (Equiv.refl _)).trans
            (Fin.consEquiv (fun _ : Fin (k + 1) => Fin n))))
    refine ⟨F, fun v => ?_⟩
    obtain ⟨Q, hQ, hSQ, hm⟩ := hes (v 0) (v ∘ Fin.succ)
    refine ⟨Q, hQ, ?_, ?_⟩
    · apply Position.Sub.trans (Q := Function.update P (slot 0) (some (v 0, e (v 0)))) _ hSQ
      intro i
      by_cases hi : i = slot 0
      · exact Or.inl (hi ▸ hfree 0)
      · exact Or.inr (Function.update_of_ne hi _ _).symm
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hSQ.mark (Function.update_self _ _ _)
      · exact hm j

theorem equivalent_joint_of_wins {n K k : ℕ} {G H : Graph n} (hk : k < K)
    (h : Wins G H (fun _ : Fin K => none)) : Equivalent .joint k G H := by
  let slot : Fin k → Fin K := fun i => ⟨i.val, lt_trans i.isLt hk⟩
  have hs : Function.Injective slot := fun _ _ heq => Fin.ext (congrArg (fun i : Fin K => i.val) heq)
  obtain ⟨e, he⟩ := wins_matching h slot hs (fun _ => rfl)
  intro t
  apply multiset_match_of_equiv _ _ e
  intro v
  obtain ⟨Q, hQ, _, hm⟩ := he v
  exact joint_color_of_wins hk t hs hQ hm

theorem equivalent_separate_of_wins {n K k : ℕ} {G H : Graph n} (hk : k ≤ K)
    (h : Wins G H (fun _ : Fin K => none)) : Equivalent .separate k G H := by
  let slot : Fin k → Fin K := fun i => ⟨i.val, lt_of_lt_of_le i.isLt hk⟩
  have hs : Function.Injective slot := fun _ _ heq => Fin.ext (congrArg (fun i : Fin K => i.val) heq)
  obtain ⟨e, he⟩ := wins_matching h slot hs (fun _ => rfl)
  intro t
  apply multiset_match_of_equiv _ _ e
  intro v
  obtain ⟨Q, hQ, _, hm⟩ := he v
  exact separate_color_of_wins t hs hQ hm

end WLTime

namespace WLTime

theorem atomic_of_stable {n k : ℕ} {c : Convention} {G H : Graph n}
    {v w : Fin k → Fin n} (h : Stable c k G H v w) (i j : Fin k) :
    (v i = v j ↔ w i = w j) ∧ G.adj (v i) (v j) = H.adj (w i) (w j) := by
  have h₀ := h 0
  constructor
  · exact decide_eq_decide.mp (congrFun (congrFun (congrArg Prod.fst h₀) i) j)
  · exact congrFun (congrFun (congrArg Prod.snd h₀) i) j

theorem partialIso_of_stable {n k : ℕ} {c : Convention} {G H : Graph n}
    {v w : Fin k → Fin n} (h : Stable c k G H v w) {P : Position k n}
    (hP : P.Sub (completePosition v w)) : P.PartialIso G H := by
  intro i j x y u z hi hj
  have hi' := Prod.mk.inj (Option.some.inj (hP.mark hi))
  have hj' := Prod.mk.inj (Option.some.inj (hP.mark hj))
  change v i = x ∧ w i = y at hi'
  change v j = u ∧ w j = z at hj'
  rw [← hi'.1, ← hi'.2, ← hj'.1, ← hj'.2]
  exact atomic_of_stable h i j

theorem sub_complete_update {n k : ℕ} {v w : Fin k → Fin n} {P : Position k n}
    (hP : P.Sub (completePosition v w)) (i : Fin k) (x y : Fin n) :
    Position.Sub (Function.update P i (some (x, y)))
      (completePosition (Function.update v i x) (Function.update w i y)) := by
  intro j
  by_cases hj : j = i
  · subst j
    right
    simp only [Function.update_self, completePosition]
  · simpa only [Function.update_of_ne hj, completePosition] using hP j

theorem wins_of_stable_separate {n k : ℕ} {G H : Graph n} {v w : Fin k → Fin n}
    (h : Stable .separate k G H v w) {P : Position k n}
    (hP : P.Sub (completePosition v w)) : Wins G H P := by
  let I : GameInvariant G H k := {
    safe := fun Q => ∃ a b, Stable .separate k G H a b ∧ Q.Sub (completePosition a b)
    forget := by
      rintro Q R ⟨a, b, hab, hR⟩ hQR
      exact ⟨a, b, hab, hQR.trans hR⟩
    atomic := by
      rintro Q ⟨a, b, hab, hQ⟩
      exact partialIso_of_stable hab hQ
    extend := by
      rintro Q ⟨a, b, hab, hQ⟩ i _
      obtain ⟨e, he⟩ := stable_separate_extension hab i
      exact ⟨e, fun z => ⟨_, _, he z, sub_complete_update hQ i z (e z)⟩⟩ }
  exact ⟨I, v, w, h, hP⟩

theorem wins_of_equivalent_separate {n k : ℕ} {G H : Graph n} (hn : 0 < n)
    (h : Equivalent .separate k G H) : Wins G H (fun _ : Fin k => none) := by
  obtain ⟨e, he⟩ := equivalent_stable_matching h
  let v : Fin k → Fin n := fun _ => ⟨0, hn⟩
  exact wins_of_stable_separate (he v) (fun _ => Or.inl rfl)

theorem separate_equivalent_iff_wins {n k : ℕ} {G H : Graph n} (hn : 0 < n) :
    Equivalent .separate k G H ↔ Wins G H (fun _ : Fin k => none) :=
  ⟨wins_of_equivalent_separate hn, equivalent_separate_of_wins le_rfl⟩

end WLTime

namespace WLTime

private theorem factor_injective {α : Type uα} {β : Type uβ} [Finite α] {f g : α → β}
    (hg : Function.Injective g) (hcover : ∀ a, ∃ b, f b = g a) :
    ∃ π : Equiv.Perm α, ∀ a, f (π a) = g a := by
  classical
  choose p hp using hcover
  have hinj : Function.Injective p := by
    intro a b hab
    apply hg
    rw [← hp a, ← hp b, hab]
  exact ⟨Equiv.ofBijective p ⟨hinj, Finite.surjective_of_injective hinj⟩, hp⟩

private theorem projection_factor {k : ℕ} (i : Fin (k + 1))
    (τ : Fin k → Fin (k + 1)) (hτ : Function.Injective τ) :
    (∃ π : Equiv.Perm (Fin k), ∀ b, i.succAbove (π b) = τ b) ∨
    ∃ a, ∃ π : Equiv.Perm (Fin k),
      ∀ b, Function.update i.succAbove a i (π b) = τ b := by
  classical
  by_cases hi : ∃ a, τ a = i
  · right
    obtain ⟨b, hb⟩ := hi
    obtain ⟨o, ho⟩ := exists_fresh_slot (Nat.lt_succ_self k) τ
    have hoi : o ≠ i := by
      intro h
      exact ho b (hb.trans h.symm)
    obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hoi
    refine ⟨a, factor_injective hτ ?_⟩
    intro d
    by_cases hd : τ d = i
    · exact ⟨a, (Function.update_self _ _ _).trans hd.symm⟩
    · obtain ⟨c, hc⟩ := Fin.exists_succAbove_eq hd
      have hca : c ≠ a := by
        intro h
        exact ho d (hc.symm.trans (h ▸ ha))
      exact ⟨c, (Function.update_of_ne hca _ _).trans hc⟩
  · left
    apply factor_injective hτ
    intro a
    apply Fin.exists_succAbove_eq
    intro h
    exact hi ⟨a, h⟩

private theorem update_projection {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq α] [DecidableEq β]
    (u : β → γ) (σ : α → β) (i : β) (fresh : ∀ a, σ a ≠ i) (a : α) (z : γ) :
    Function.update u i z ∘ Function.update σ a i = Function.update (u ∘ σ) a z := by
  funext b
  by_cases hb : b = a
  · subst b
    simp only [Function.comp_apply, Function.update_self]
  · simp only [Function.comp_apply, Function.update_of_ne hb, Function.update_of_ne (fresh b)]

theorem joint_full_extend {n k : ℕ} {G H : Graph n} {v w : Fin (k + 1) → Fin n}
    (i : Fin (k + 1))
    (h : Stable .joint k G H (v ∘ i.succAbove) (w ∘ i.succAbove)) :
    ∃ e : Fin n ≃ Fin n, ∀ z,
      JointFull G H (Function.update v i z) (Function.update w i (e z)) := by
  classical
  obtain ⟨e, he⟩ := stable_joint_extension h
  refine ⟨e, fun z τ => ?_⟩
  rcases projection_factor i τ τ.injective with ⟨π, hπ⟩ | ⟨a, π, hπ⟩
  · have hv : Function.update v i z ∘ τ = (v ∘ i.succAbove) ∘ π := by
      funext b
      simp only [Function.comp_apply, ← hπ b, Function.update_of_ne (Fin.succAbove_ne i (π b))]
    have hw : Function.update w i (e z) ∘ τ = (w ∘ i.succAbove) ∘ π := by
      funext b
      simp only [Function.comp_apply, ← hπ b, Function.update_of_ne (Fin.succAbove_ne i (π b))]
    rw [hv, hw]
    exact h.permute π
  · have hτ : (τ : Fin k → Fin (k + 1)) = Function.update i.succAbove a i ∘ π :=
      funext (fun b => (hπ b).symm)
    rw [hτ, ← Function.comp_assoc, ← Function.comp_assoc,
      update_projection v i.succAbove i (Fin.succAbove_ne i),
      update_projection w i.succAbove i (Fin.succAbove_ne i)]
    exact (he z a).permute π

private theorem exists_third_slot {k : ℕ} (hk : 2 ≤ k) (i j : Fin (k + 1)) :
    ∃ o, o ≠ i ∧ o ≠ j := by
  classical
  have hc : ({i, j} : Finset (Fin (k + 1))).card < (Finset.univ : Finset (Fin (k + 1))).card := by
    have h := Finset.card_insert_le i ({j} : Finset (Fin (k + 1)))
    simp only [Finset.card_singleton, Finset.card_univ, Fintype.card_fin] at *
    omega
  obtain ⟨o, _, ho⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  refine ⟨o, ?_⟩
  simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using ho

theorem partialIso_of_jointFull {n k : ℕ} {G H : Graph n} (hk : 2 ≤ k)
    {v w : Fin (k + 1) → Fin n} (h : JointFull G H v w) {P : Position (k + 1) n}
    (hP : P.Sub (completePosition v w)) : P.PartialIso G H := by
  intro i j x y u z hi hj
  have hi' := Prod.mk.inj (Option.some.inj (hP.mark hi))
  have hj' := Prod.mk.inj (Option.some.inj (hP.mark hj))
  change v i = x ∧ w i = y at hi'
  change v j = u ∧ w j = z at hj'
  rw [← hi'.1, ← hi'.2, ← hj'.1, ← hj'.2]
  obtain ⟨o, hoi, hoj⟩ := exists_third_slot hk i j
  obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hoi.symm
  obtain ⟨b, hb⟩ := Fin.exists_succAbove_eq hoj.symm
  have hab := atomic_of_stable (h o.succAboveEmb) a b
  simpa only [Function.comp_apply, Fin.succAboveEmb_apply, ha, hb] using hab

end WLTime

namespace WLTime

theorem wins_of_jointFull {n k : ℕ} {G H : Graph n} (hk : 2 ≤ k)
    {v w : Fin (k + 1) → Fin n} (h : JointFull G H v w) {P : Position (k + 1) n}
    (hP : P.Sub (completePosition v w)) : Wins G H P := by
  let I : GameInvariant G H (k + 1) := {
    safe := fun Q => ∃ a b, JointFull G H a b ∧ Q.Sub (completePosition a b)
    forget := by
      rintro Q R ⟨a, b, hab, hR⟩ hQR
      exact ⟨a, b, hab, hQR.trans hR⟩
    atomic := by
      rintro Q ⟨a, b, hab, hQ⟩
      exact partialIso_of_jointFull hk hab hQ
    extend := by
      rintro Q ⟨a, b, hab, hQ⟩ i _
      obtain ⟨e, he⟩ := joint_full_extend i (hab i.succAboveEmb)
      exact ⟨e, fun z => ⟨_, _, he z, sub_complete_update hQ i z (e z)⟩⟩ }
  exact ⟨I, v, w, h, hP⟩

theorem wins_of_stable_joint {n k : ℕ} {G H : Graph n} (hn : 0 < n) (hk : 2 ≤ k)
    {v w : Fin k → Fin n} (h : Stable .joint k G H v w) :
    Wins G H (sparePosition v w) := by
  let z : Fin n := ⟨0, hn⟩
  let v' : Fin (k + 1) → Fin n := Fin.snoc v z
  let w' : Fin (k + 1) → Fin n := Fin.snoc w z
  have hv : v' ∘ (Fin.last k).succAbove = v := by
    funext i
    simp [v', Fin.succAbove_last]
  have hw : w' ∘ (Fin.last k).succAbove = w := by
    funext i
    simp [w', Fin.succAbove_last]
  obtain ⟨e, he⟩ := joint_full_extend (Fin.last k) (show Stable .joint k G H
    (v' ∘ (Fin.last k).succAbove) (w' ∘ (Fin.last k).succAbove) from hv ▸ hw ▸ h)
  apply wins_of_jointFull hk (he z)
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · left
    exact Fin.snoc_last _ _
  · right
    simp only [sparePosition, Fin.snoc_castSucc, completePosition,
      Function.update_of_ne (Fin.castSucc_ne_last j), v', w']

theorem wins_of_equivalent_joint {n k : ℕ} {G H : Graph n} (hn : 0 < n) (hk : 2 ≤ k)
    (h : Equivalent .joint k G H) : Wins G H (fun _ : Fin (k + 1) => none) := by
  obtain ⟨e, he⟩ := equivalent_stable_matching h
  let v : Fin k → Fin n := fun _ => ⟨0, hn⟩
  exact (wins_of_stable_joint hn hk (he v)).forget (fun _ => Or.inl rfl)

theorem joint_equivalent_iff_wins {n k : ℕ} {G H : Graph n} (hn : 0 < n) (hk : 2 ≤ k) :
    Equivalent .joint k G H ↔ Wins G H (fun _ : Fin (k + 1) => none) :=
  ⟨wins_of_equivalent_joint hn hk, equivalent_joint_of_wins (Nat.lt_succ_self k)⟩

end WLTime

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Consistency
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uP uE uΛ uT uLabel uL uB uV

namespace WLTime.Compression

namespace ConsistencyData
variable {r m : ℕ} {P : Type uP} {E : Type uE} (I : ConsistencyData r m P E)

theorem leftForm_section_zero (K : ℕ) (l : TypeLink K E) (h0 : l.2.val = 0)
    (h : (t : TypeNode K P E) → I.Value K t) :
    I.leftForm K l (h (linkLeft K I.src l)) = I.linearSrc l.1 (h (.inl (I.src l.1))) := by
  simp only [leftForm, dite_eq_left h0]
  exact I.transportForm_apply K _ _ h

theorem rightForm_section_last (K : ℕ) (l : TypeLink K E) (h4 : l.2.val = 4 * K)
    (h : (t : TypeNode K P E) → I.Value K t) :
    I.rightForm K l (h (linkRight K I.dst l)) = I.linearDst l.1 (h (.inl (I.dst l.1))) := by
  simp only [rightForm, dite_eq_left h4]
  exact I.transportForm_apply K _ _ h

theorem arcConsistent_iff : I.ArcConsistent ↔ Nonempty I.ArcWitness := by
  constructor
  · rintro ⟨Q, hne, hi⟩; exact ⟨⟨Q, hne, hi⟩⟩
  · rintro ⟨Q⟩; exact ⟨Q.sets, Q.nonempty, Q.images⟩

end ConsistencyData
end WLTime.Compression

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Pebbles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA uB uD uState

namespace WLTime.Pebble

namespace Position
variable {K : ℕ} {A : Type uA} {B : Type uB}

theorem erase_sub (P : Position K A B) (i : Fin K) : Position.Sub (Function.update P i none) P := by
  intro j
  by_cases h : j = i
  · subst j; exact Or.inl (Function.update_self i none P)
  · exact Or.inr (Function.update_of_ne h none P)

end Position

namespace Wins
variable {K : ℕ} {A : Type uA} {B : Type uB} {G : SimpleGraph A} {H : SimpleGraph B}
    {C : A → B → Prop} {P Q : Position K A B}

theorem forget (h : Wins G H C Q) (hPQ : P.Sub Q) : Wins G H C P := by
  obtain ⟨I,hI⟩ := h
  exact ⟨I,I.forget hI hPQ⟩

theorem atomic (h : Wins G H C P) : P.PartialIso G H C := by
  obtain ⟨I,hI⟩ := h
  exact I.atomic hI

theorem extend (h : Wins G H C P) (i : Fin K) (hi : P i = none) :
    ∃ e : A ≃ B, ∀ z, Wins G H C (Function.update P i (some (z,e z))) := by
  obtain ⟨I,hI⟩ := h
  obtain ⟨e,he⟩ := I.extend hI i hi
  exact ⟨e,fun z => ⟨I,he z⟩⟩

theorem erase (h : Wins G H C P) (i : Fin K) : Wins G H C (Function.update P i none) :=
  h.forget (P.erase_sub i)

theorem rename (h : Wins G H C P) (e : Equiv.Perm (Fin K)) :
    Wins G H C (fun i => P (e i)) := by
  classical
  obtain ⟨I,hI⟩ := h
  let J : Invariant G H C K := {
    safe := fun Q => I.safe (fun i => Q (e.symm i))
    forget := by
      intro Q R hR hQR
      exact I.forget hR (fun i => hQR (e.symm i))
    atomic := by
      intro Q hQ
      obtain ⟨hc,ha⟩ := I.atomic hQ
      constructor
      · intro i x y hi
        exact hc (e i) x y (by simpa using hi)
      · intro i j x y u v hi hj
        exact ha (e i) (e j) x y u v (by simpa using hi) (by simpa using hj)
    extend := by
      intro Q hQ i hi
      obtain ⟨f,hf⟩ := I.extend hQ (e i) (by simpa using hi)
      refine ⟨f,fun z => ?_⟩
      have heq : (fun j => (Function.update Q i (some (z,f z))) (e.symm j)) =
          Function.update (fun j => Q (e.symm j)) (e i) (some (z,f z)) := by
        funext j
        by_cases hj : j = e i
        · subst j; simp
        · have hji : e.symm j ≠ i := by intro hh; exact hj (by simpa using congrArg e hh)
          simp only [Function.update_of_ne hj, Function.update_of_ne hji]
      rw [heq]
      exact hf z }
  exact ⟨J,by simpa only [J, Equiv.apply_symm_apply] using hI⟩

end Wins

end WLTime.Pebble

namespace WLTime.Pebble

namespace ExactLocalSystem
variable {K : ℕ} {A : Type uA} {B : Type uB} {D : Type uD} {G : SimpleGraph A} {H : SimpleGraph B}
    {C : A → B → Prop} {tag : A → Option D}
    (S : ExactLocalSystem.{uA, uB, uD, uState} G H C tag K)

include S in
theorem wins_empty : Wins G H C (fun _ : Fin K => none) := by
  obtain ⟨R,hR⟩ := S.empty
  refine ⟨S.invariant,R,?_,?_⟩
  · have he : active tag (fun _ : Fin K => (none : Option (A×B))) = ∅ := by
      classical
      ext d
      simp [mem_active]
    rw [he]
    exact hR
  · intro i x y hi
    simp at hi

end ExactLocalSystem
end WLTime.Pebble

namespace WLTime.Pebble.Wins
variable {K : ℕ} {A : Type uA} {B : Type uB} {G : SimpleGraph A} {H : SimpleGraph B}
    {C : A → B → Prop} {P : Position K A B}

theorem replace (h : Wins G H C P) (i s : Fin K) (his : i ≠ s) (hs : P s = none) (x : A) :
    ∃ y, Wins G H C (Function.update P i (some (x,y))) ∧ C x y ∧
      ∀ u v, P i = some (u,v) → (u = x ↔ v = y) ∧ (G.Adj u x ↔ H.Adj v y) := by
  classical
  obtain ⟨e,he⟩ := h.extend s hs
  have hQ := he x
  refine ⟨e x, ?_, hQ.atomic.1 s x (e x) (Function.update_self _ _ _), ?_⟩
  · have hR := (hQ.erase i).rename (Equiv.swap i s)
    have heq : (fun j => Function.update (Function.update P s (some (x,e x))) i none
        ((Equiv.swap i s) j)) = Function.update P i (some (x,e x)) := by
      funext j
      by_cases hji : j = i
      · subst j; simp [his.symm]
      · by_cases hjs : j = s
        · subst j; simp [his.symm,hs]
        · simp [Equiv.swap_apply_of_ne_of_ne hji hjs,hji,hjs]
    rw [heq] at hR
    exact hR
  · intro u v hi
    exact hQ.atomic.2 i s u v x (e x)
      (by simpa only [Function.update_of_ne his] using hi) (Function.update_self _ _ _)

theorem realize (h : Wins G H C (fun _ : Fin K => none)) (X : Fin K → Option A) :
    ∃ P : Position K A B, Wins G H C P ∧ ∀ i, (P i).map Prod.fst = X i := by
  classical
  have aux (S : Finset (Fin K)) : ∃ P : Position K A B, Wins G H C P ∧
      (∀ i ∈ S, (P i).map Prod.fst = X i) ∧ (∀ i ∉ S, P i = none) := by
    induction S using Finset.induction_on with
    | empty =>
      exact ⟨fun _ => none,h,by simp,by simp⟩
    | @insert i S hi ih =>
      obtain ⟨Q,hQ,hqin,hqout⟩ := ih
      cases hx : X i with
      | none =>
        refine ⟨Q,hQ,?_,fun j hj => hqout j (fun h => hj (Finset.mem_insert_of_mem h))⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · simpa only [hqout j hi,Option.map_none] using hx.symm
        · exact hqin j hj
      | some x =>
        obtain ⟨e,he⟩ := hQ.extend i (hqout i hi)
        refine ⟨Function.update Q i (some (x,e x)),he x,?_,?_⟩
        · intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hj
          · simp only [Function.update_self,Option.map_some,hx]
          · have hji : j ≠ i := by intro hh; subst j; exact hi hj
            simpa only [Function.update_of_ne hji] using hqin j hj
        · intro j hj
          have hji : j ≠ i := by intro hh; subst j; exact hj (Finset.mem_insert_self i S)
          rw [Function.update_of_ne hji]
          exact hqout j (fun hh => hj (Finset.mem_insert_of_mem hh))
  obtain ⟨P,hP,hin,_⟩ := aux Finset.univ
  exact ⟨P,hP,fun i => hin i (Finset.mem_univ i)⟩

end WLTime.Pebble.Wins

namespace WLTime.Pebble

theorem Wins.neighborhood_bijection {K : ℕ} {A : Type uA} {B : Type uB}
    {G : SimpleGraph A} {H : SimpleGraph B} {C : A → B → Prop}
    (hK : 2 ≤ K) {P : Position K A B} (hP : Wins G H C P)
    {i : Fin K} {x : A} {y : B} (hi : P i = some (x,y)) :
    ∃ e : A ≃ B, e x = y ∧ ∀ z, G.Adj x z ↔ H.Adj y (e z) := by
  classical
  let j : Fin K := if i.val=0 then ⟨1,by omega⟩ else ⟨0,by omega⟩
  have hij : i ≠ j := by
    intro h
    have hh := congrArg Fin.val h
    by_cases h0 : i.val=0
    · simp only [j,ite_eq_left h0,Fin.val_mk] at hh
      omega
    · simp only [j,ite_eq_right h0,Fin.val_mk] at hh
      exact h0 hh
  let Q : Position K A B := fun a => if a=i then P a else none
  have hQ : Wins G H C Q := hP.forget (fun a => by
    by_cases ha : a=i
    · exact Or.inr (ite_eq_left ha)
    · exact Or.inl (ite_eq_right ha))
  obtain ⟨e,he⟩ := hQ.extend j (ite_eq_right hij.symm)
  have hat (z : A) := (he z).atomic.2 i j x y z (e z)
    (by simp only [Function.update_of_ne hij,Q,hi,ite_true])
    (Function.update_self _ _ _)
  exact ⟨e,((hat x).1.mp rfl).symm,fun z => (hat z).2⟩

theorem Wins.degree_eq {K : ℕ} {A : Type uA} {B : Type uB} [Fintype A] [Fintype B]
    {G : SimpleGraph A} {H : SimpleGraph B} {C : A → B → Prop}
    (hK : 2 ≤ K) {P : Position K A B} (hP : Wins G H C P)
    {i : Fin K} {x : A} {y : B} (hi : P i = some (x,y)) :
    degree G x = degree H y := by
  classical
  obtain ⟨e,_,he⟩ := hP.neighborhood_bijection hK hi
  exact Fintype.card_congr (Equiv.subtypeEquiv e he)

end WLTime.Pebble

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Gadgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA uB uA' uB' uP uE

namespace WLTime.Pebble

theorem Wins.transport {K : ℕ} {A : Type uA} {B : Type uB} {A' : Type uA'} {B' : Type uB'}
    {G : SimpleGraph A} {H : SimpleGraph B} {G' : SimpleGraph A'} {H' : SimpleGraph B'}
    (f : A ≃ A') (g : B ≃ B')
    (hf : ∀ x y, G.Adj x y ↔ G'.Adj (f x) (f y))
    (hg : ∀ x y, H.Adj x y ↔ H'.Adj (g x) (g y))
    {P : Position K A B} (h : Wins G H (fun _ _ => True) P) :
    Wins G' H' (fun _ _ => True) (Position.map f g P) := by
  classical
  let J : Invariant G' H' (fun _ _ => True) K := {
    safe Q := Wins G H (fun _ _ => True) (Position.map f.symm g.symm Q)
    forget := by
      intro Q R hR hQR
      apply hR.forget
      intro i
      rcases hQR i with hi | hi
      · exact Or.inl (by simp [Position.map,hi])
      · exact Or.inr (by simp [Position.map,hi])
    atomic := by
      intro Q hQ
      refine ⟨fun _ _ _ _ => True.intro,?_⟩
      intro i j x y u v hi hj
      have ha := hQ.atomic.2 i j (f.symm x) (g.symm y) (f.symm u) (g.symm v)
        (by simp [hi]) (by simp [hj])
      simpa only [Equiv.apply_eq_iff_eq, hf, hg, Equiv.apply_symm_apply] using ha
    extend := by
      intro Q hQ i hi
      obtain ⟨e,he⟩ := hQ.extend i (by simp [hi])
      refine ⟨f.symm.trans (e.trans g),fun x => ?_⟩
      simpa only [Position.map_update,Equiv.trans_apply,Equiv.symm_apply_apply] using he (f.symm x) }
  exact ⟨J,by simpa only [J,Position.map_inverse] using h⟩

end WLTime.Pebble

namespace WLTime.Compression
namespace ConsistencyData
variable {r m : ℕ} {P : Type uP} {E : Type uE} (I : ConsistencyData (r+1) m P E)

theorem ac_colored_wins [DecidableEq E] [DecidableEq P] (Q : I.ArcWitness)
    (K : ℕ) (hK : 0 < K) (hr : 2 ≤ r) (hKr : K ≤ r+2) :
    Pebble.Wins (I.valuationGraph K 0) (I.valuationGraph K 1)
      (fun x y => x.1 = y.1) (fun _ : Fin K => none) :=
  (I.valuationSystem Q K hK hr hKr).wins_empty

end ConsistencyData
end WLTime.Compression

namespace WLTime.Compression
namespace ConsistencyData
variable {r m : ℕ} {P : Type uP} {E : Type uE} (I : ConsistencyData (r+1) m P E)

theorem queried_color (K : ℕ) {s : ℕ} {f : Fin s → I.Block K} {y : Fin s → I.Vertex K 1}
    (h : I.Queried K f y) (i : Fin s) : f i = (y i).1 := by
  exact h.atomic.1 i.castSucc (I.zeroVertex K (f i)) (y i) (by simp [queryPosition])

theorem queried_exists (K : ℕ) {s : ℕ}
    (h : Pebble.Wins (I.valuationGraph K 0) (I.valuationGraph K 1)
      (fun x y => x.1 = y.1) (fun _ : Fin (s+1) => none)) (f : Fin s → I.Block K) :
    ∃ y, I.Queried K f y := by
  classical
  let X : Fin (s+1) → Option (I.Vertex K 0) := Fin.lastCases none (fun i => some (I.zeroVertex K (f i)))
  obtain ⟨Q,hQ,hsrc⟩ := h.realize X
  have hget (i : Fin s) : ∃ y, Q i.castSucc = some (I.zeroVertex K (f i),y) := by
    have he := hsrc i.castSucc
    simp only [X,Fin.lastCases_castSucc] at he
    cases hqi : Q i.castSucc with
    | none => simp [hqi] at he
    | some xy =>
      rcases xy with ⟨x,y⟩
      simp only [hqi,Option.map_some,Option.some.injEq] at he
      subst x
      exact ⟨y,rfl⟩
  choose y hy using hget
  have hlast : Q (Fin.last s) = none := by
    have he := hsrc (Fin.last s)
    simpa only [X,Fin.lastCases_last,Option.map_eq_none_iff] using he
  have heq : Q = I.queryPosition K f y := by
    funext j
    induction j using Fin.lastCases with
    | last => simpa only [queryPosition,Fin.lastCases_last] using hlast
    | cast i => simpa only [queryPosition,Fin.lastCases_castSucc] using hy i
  refine ⟨y,?_⟩
  change Pebble.Wins _ _ _ _
  rw [← heq]
  exact hQ

theorem queried_change_one (K : ℕ) {s : ℕ} {f : Fin s → I.Block K} {ys : Fin s → I.Vertex K 1}
    (h : I.Queried K f ys) (i : Fin s) (b : I.Block K) :
    ∃ y, I.Queried K (Function.update f i b) (Function.update ys i y) ∧
      ∀ n ∈ I.footprint K (f i).val, n ∈ I.footprint K b.val → (ys i).read n = y.read n := by
  classical
  obtain ⟨y,hy,hcolor,hcomp⟩ := h.replace i.castSucc (Fin.last s) (Fin.castSucc_ne_last i)
    (by simp [queryPosition]) (I.zeroVertex K b)
  have hpos : Function.update (I.queryPosition K f ys) i.castSucc (some (I.zeroVertex K b,y)) =
      I.queryPosition K (Function.update f i b) (Function.update ys i y) := by
    funext j
    induction j using Fin.lastCases with
    | last => simp [queryPosition,(Fin.castSucc_ne_last i).symm]
    | cast j =>
      by_cases he : j = i
      · subst j; simp [queryPosition]
      · have hcast : j.castSucc ≠ i.castSucc := fun hh => he (Fin.castSucc_inj.mp hh)
        simp only [Function.update_of_ne hcast,queryPosition,Fin.lastCases_castSucc,Function.update_of_ne he]
  refine ⟨y,?_,?_⟩
  · change Pebble.Wins _ _ _ _
    rw [← hpos]
    exact hy
  · intro n hn hm
    have hc := hcomp (I.zeroVertex K (f i)) (ys i) (by simp [queryPosition])
    by_cases hb : f i = b
    · have he : I.zeroVertex K (f i) = I.zeroVertex K b := congrArg (I.zeroVertex K) hb
      exact congrArg (fun z : I.Vertex K 1 => z.read n) (hc.1.mp he)
    · have ha : (I.valuationGraph K 0).Adj (I.zeroVertex K (f i)) (I.zeroVertex K b) := by
        refine ⟨hb,⟨n,Finset.mem_inter.mpr ⟨hn,hm⟩⟩,?_⟩
        intro k _ _
        rfl
      have ha' := hc.2.mp ha
      exact ha'.2.2 n (by rwa [← I.queried_color K h i]) (by rwa [← hcolor])

theorem queried_transform (K : ℕ) {s : ℕ} {f : Fin s → I.Block K} {ys : Fin s → I.Vertex K 1}
    (h : I.Queried K f ys) (g : Fin s → I.Block K) :
    ∃ zs, I.Queried K g zs ∧ ∀ i n, n ∈ I.footprint K (f i).val → n ∈ I.footprint K (g i).val →
      (ys i).read n = (zs i).read n := by
  classical
  let blend (S : Finset (Fin s)) : Fin s → I.Block K := fun i => if i ∈ S then g i else f i
  have aux (S : Finset (Fin s)) : ∃ zs, I.Queried K (blend S) zs ∧
      (∀ i ∉ S, zs i = ys i) ∧
      (∀ i ∈ S, ∀ n, n ∈ I.footprint K (f i).val → n ∈ I.footprint K (g i).val →
        (ys i).read n = (zs i).read n) := by
    induction S using Finset.induction_on with
    | empty => exact ⟨ys,by simpa only [blend,Finset.notMem_empty,ite_false] using h,by simp,by simp⟩
    | @insert i S hi ih =>
      obtain ⟨zs,hzs,hout,hin⟩ := ih
      obtain ⟨z,hz,hkeep⟩ := I.queried_change_one K hzs i (g i)
      have heq : Function.update (blend S) i (g i) = blend (insert i S) := by
        funext j
        by_cases he : j = i
        · subst j; simp [blend]
        · simp [blend,he]
      refine ⟨Function.update zs i z,heq ▸ hz,?_,?_⟩
      · intro j hj
        have hji : j ≠ i := by intro hh; subst j; exact hj (Finset.mem_insert_self i S)
        rw [Function.update_of_ne hji]
        exact hout j (fun hh => hj (Finset.mem_insert_of_mem hh))
      · intro j hj n hn hm
        rcases Finset.mem_insert.mp hj with rfl | hj
        · rw [Function.update_self]
          rw [← hout j hi]
          apply hkeep n
          · simpa only [blend,ite_eq_right hi] using hn
          · exact hm
        · have hji : j ≠ i := by intro hh; subst j; exact hi hj
          rw [Function.update_of_ne hji]
          exact hin j hj n hn hm
  obtain ⟨zs,hzs,_,hkeep⟩ := aux Finset.univ
  exact ⟨zs,by simpa only [blend,Finset.mem_univ,ite_true] using hzs,
    fun i n hn hm => hkeep i (Finset.mem_univ i) n hn hm⟩

end ConsistencyData
end WLTime.Compression

namespace WLTime.Compression
namespace ConsistencyData
variable {r m : ℕ} {P : Type uP} {E : Type uE} (I : ConsistencyData (r+1) m P E)

theorem queried_legal (K : ℕ) {s : ℕ} {f : Fin s → I.Block K} {y : Fin s → I.Vertex K 1}
    (h : I.Queried K f y) (i : Fin s) :
    I.blockForm K (f i).val (y i).read = I.blockBias K (f i).val := by
  rw [I.queried_color K h i]
  simpa only [one_mul] using (y i).2.property

theorem queried_shared (K : ℕ) {s : ℕ} {f : Fin s → I.Block K} {y : Fin s → I.Vertex K 1}
    (h : I.Queried K f y) (i j : Fin s) (hne : f i ≠ f j)
    (n : RawName (r := r) (m := m) (P := P) (E := E) K)
    (hi : n ∈ I.footprint K (f i).val) (hj : n ∈ I.footprint K (f j).val) :
    (y i).read n = (y j).read n := by
  classical
  have ha : (I.valuationGraph K 0).Adj (I.zeroVertex K (f i)) (I.zeroVertex K (f j)) :=
    ⟨hne,⟨n,Finset.mem_inter.mpr ⟨hi,hj⟩⟩,fun _ _ _ => rfl⟩
  have hpair := h.atomic.2 i.castSucc j.castSucc (I.zeroVertex K (f i)) (y i)
    (I.zeroVertex K (f j)) (y j) (by simp [queryPosition]) (by simp [queryPosition])
  exact (hpair.2.mp ha).2.2 n (by rwa [← I.queried_color K h i]) (by rwa [← I.queried_color K h j])

theorem squareRing_injective (K : ℕ) (l : TypeLink K E) (a : I.Address) (ha : I.Allowed l.1 a) :
    Function.Injective (I.squareRing K l a ha) := by
  intro i j h
  exact congrArg (fun b : I.Block K => BlockName.row b.val) h

theorem squareRing_vertical (K : ℕ) (hr : 1 ≤ r) (l : TypeLink K E) (a : I.Address)
    (ha : I.Allowed l.1 a) {ys : Fin (r+1) → I.Vertex K 1}
    (h : I.Queried K (I.squareRing K l a ha) ys) (i : Fin (r+1)) :
    (ys i).read (I.verticalName K l a (finRotate (r+1) i)) =
      (ys (finRotate (r+1) i)).read (I.verticalName K l a (finRotate (r+1) i)) := by
  apply I.queried_shared K h i (finRotate (r+1) i)
  · intro he
    exact rotate_ne_self hr i ((I.squareRing_injective K l a ha he).symm)
  · simp [squareRing,footprint,verticalName]
  · simp [squareRing,footprint,verticalName]

theorem squareRing_equation (K : ℕ) (hr : 1 ≤ r) (l : TypeLink K E) (a : I.Address)
    (ha : I.Allowed l.1 a) {ys : Fin (r+1) → I.Vertex K 1}
    (h : I.Queried K (I.squareRing K l a ha) ys) :
    I.leftForm K l (I.horizontalSum K (linkLeft K I.src l) a ys) +
      I.rightForm K l (I.horizontalSum K (linkRight K I.dst l) (I.matchedAddress K l a) ys) =
        I.linkBias K l := by
  have heq (i : Fin (r+1)) :
      I.leftForm K l ((ys i).read (I.horizontalName K (linkLeft K I.src l) a i)) +
      I.rightForm K l ((ys i).read (I.horizontalName K (linkRight K I.dst l) (I.matchedAddress K l a) i)) +
      ((ys i).read (I.verticalName K l a i) : F₂) +
      ((ys i).read (I.verticalName K l a (finRotate (r+1) i)) : F₂) = seam i * I.linkBias K l :=
    I.queried_legal K h i
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => heq i)
  simp only [Finset.sum_add_distrib] at hsum
  have hver : (∑ i, (ys i).read (I.verticalName K l a (finRotate (r+1) i)) : F₂) =
      (∑ i, (ys i).read (I.verticalName K l a i) : F₂) := by
    calc
      _ = (∑ i, (ys (finRotate (r+1) i)).read (I.verticalName K l a (finRotate (r+1) i)) : F₂) :=
        Finset.sum_congr rfl (fun i _ => I.squareRing_vertical K hr l a ha h i)
      _ = _ := Equiv.sum_comp (M := F₂) (finRotate (r+1)) (fun i => (ys i).read (I.verticalName K l a i))
  have hseam : (∑ i : Fin (r+1), seam i * I.linkBias K l) = I.linkBias K l := by simp [seam]
  rw [hver,hseam] at hsum
  simpa only [horizontalSum,map_sum,add_assoc,CharTwo.add_self_eq_zero,add_zero] using hsum

theorem ring_transfer_left (K : ℕ) (hr : 1 ≤ r) (l : TypeLink K E) (a : I.Address)
    (ha : I.Allowed l.1 a) {ys : Fin (r+1) → I.Vertex K 1}
    (h : I.Queried K (I.siteRing K (linkLeft K I.src l) a (I.leftAddress_allowed K l a ha)) ys) :
    ∃ zs, I.Queried K (I.siteRing K (linkRight K I.dst l) (I.matchedAddress K l a)
      (I.rightAddress_allowed K l a ha)) zs ∧
      I.leftForm K l (I.horizontalSum K (linkLeft K I.src l) a ys) +
      I.rightForm K l (I.horizontalSum K (linkRight K I.dst l) (I.matchedAddress K l a) zs) = I.linkBias K l := by
  obtain ⟨qs,hqs,hleft⟩ := I.queried_transform K h (I.squareRing K l a ha)
  obtain ⟨zs,hzs,hright⟩ := I.queried_transform K hqs
    (I.siteRing K (linkRight K I.dst l) (I.matchedAddress K l a) (I.rightAddress_allowed K l a ha))
  have hl : I.horizontalSum K (linkLeft K I.src l) a ys = I.horizontalSum K (linkLeft K I.src l) a qs := by
    apply Finset.sum_congr rfl
    intro i _
    apply hleft i
    · simp [siteRing,footprint,horizontalName]
    · simp [squareRing,footprint,horizontalName]
  have hr' : I.horizontalSum K (linkRight K I.dst l) (I.matchedAddress K l a) qs =
      I.horizontalSum K (linkRight K I.dst l) (I.matchedAddress K l a) zs := by
    apply Finset.sum_congr rfl
    intro i _
    apply hright i
    · simp [squareRing,footprint,horizontalName,matchedAddress]
    · simp [siteRing,footprint,horizontalName]
  exact ⟨zs,hzs,by rw [hl,← hr']; exact I.squareRing_equation K hr l a ha hqs⟩

theorem ring_transfer_right (K : ℕ) (hr : 1 ≤ r) (l : TypeLink K E) (a : I.Address)
    (ha : I.Allowed l.1 a) {ys : Fin (r+1) → I.Vertex K 1}
    (h : I.Queried K (I.siteRing K (linkRight K I.dst l) (I.matchedAddress K l a)
      (I.rightAddress_allowed K l a ha)) ys) :
    ∃ zs, I.Queried K (I.siteRing K (linkLeft K I.src l) a (I.leftAddress_allowed K l a ha)) zs ∧
      I.leftForm K l (I.horizontalSum K (linkLeft K I.src l) a zs) +
      I.rightForm K l (I.horizontalSum K (linkRight K I.dst l) (I.matchedAddress K l a) ys) = I.linkBias K l := by
  obtain ⟨qs,hqs,hright⟩ := I.queried_transform K h (I.squareRing K l a ha)
  obtain ⟨zs,hzs,hleft⟩ := I.queried_transform K hqs
    (I.siteRing K (linkLeft K I.src l) a (I.leftAddress_allowed K l a ha))
  have hl : I.horizontalSum K (linkLeft K I.src l) a qs = I.horizontalSum K (linkLeft K I.src l) a zs := by
    apply Finset.sum_congr rfl
    intro i _
    apply hleft i
    · simp [squareRing,footprint,horizontalName]
    · simp [siteRing,footprint,horizontalName]
  have hr' : I.horizontalSum K (linkRight K I.dst l) (I.matchedAddress K l a) ys =
      I.horizontalSum K (linkRight K I.dst l) (I.matchedAddress K l a) qs := by
    apply Finset.sum_congr rfl
    intro i _
    apply hright i
    · simp [siteRing,footprint,horizontalName]
    · simp [squareRing,footprint,horizontalName,matchedAddress]
  exact ⟨zs,hzs,by rw [← hl,hr']; exact I.squareRing_equation K hr l a ha hqs⟩

end ConsistencyData
end WLTime.Compression

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Marking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uP uE uV uW uD uS uState

namespace WLTime.Compression
namespace ConsistencyData
variable {r m : ℕ} {P : Type uP} {E : Type uE} (I : ConsistencyData (r+1) m P E)

theorem attainable_nonempty (K : ℕ)
    (h : Pebble.Wins (I.valuationGraph K 0) (I.valuationGraph K 1)
      (fun x y => x.1 = y.1) (fun _ : Fin (r+2) => none))
    (t : TypeNode K P E) (a : I.Address) (ha : I.AddressAllowed K t a) :
    (I.Attainable K t a).Nonempty := by
  obtain ⟨ys,hys⟩ := I.queried_exists K h (I.siteRing K t a ha)
  exact ⟨_,ha,ys,hys,rfl⟩

private theorem add_eq_rotate {x y b : F₂} (h : x+y=b) : x = y+b := by
  rw [← h,add_left_comm,CharTwo.add_self_eq_zero,add_zero]

theorem attainable_link (K : ℕ) (hr : 1 ≤ r) (l : TypeLink K E) (a : I.Address)
    (ha : I.Allowed l.1 a) :
    I.leftForm K l '' I.Attainable K (linkLeft K I.src l) a =
      (fun z => I.rightForm K l z + I.linkBias K l) ''
        I.Attainable K (linkRight K I.dst l) (I.matchedAddress K l a) := by
  ext v
  constructor
  · rintro ⟨x,⟨hx,ys,hys,rfl⟩,rfl⟩
    obtain ⟨zs,hzs,heq⟩ := I.ring_transfer_left K hr l a ha hys
    exact ⟨_,⟨_,zs,hzs,rfl⟩,(add_eq_rotate heq).symm⟩
  · rintro ⟨x,⟨hx,ys,hys,rfl⟩,rfl⟩
    obtain ⟨zs,hzs,heq⟩ := I.ring_transfer_right K hr l a ha hys
    exact ⟨_,⟨_,zs,hzs,rfl⟩,add_eq_rotate heq⟩

theorem mem_attainable_image (K : ℕ) (t : TypeNode K P E) (a : I.Address)
    (f : I.Value K t → F₂) (v : F₂) :
    v ∈ f '' I.Attainable K t a ↔
      ∃ ha ys, I.Queried K (I.siteRing K t a ha) ys ∧ f (I.horizontalSum K t a ys) = v := by
  constructor
  · rintro ⟨x,⟨ha,ys,hys,rfl⟩,hf⟩
    exact ⟨ha,ys,hys,hf⟩
  · rintro ⟨ha,ys,hys,hf⟩
    exact ⟨_,⟨ha,ys,hys,rfl⟩,hf⟩

theorem matchedAddress_internal (K : ℕ) (l : TypeLink K E) (h : l.2.val ≠ 4*K)
    (a : I.Address) : I.matchedAddress K l a = a := by
  funext i
  simp only [matchedAddress,linkMatch,ite_eq_right h,Equiv.refl_apply]

theorem matchedAddress_last (K : ℕ) (l : TypeLink K E) (h : l.2.val = 4*K)
    (a : I.Address) : I.matchedAddress K l a = I.permuteAddress l.1 a := by
  funext i
  simp only [matchedAddress,linkMatch,ite_eq_left h,permuteAddress]

theorem attainable_first (K : ℕ) (hK : 0 < K) (hr : 1 ≤ r) (e : E) (a : I.Address)
    (ha : I.Allowed e a) :
    I.affineSrc e '' I.Attainable K (.inl (I.src e)) a =
      I.Attainable K (.inr (e,⟨0,by omega⟩)) a := by
  let l : TypeLink K E := (e,⟨0,by omega⟩)
  have h0 : l.2.val = 0 := rfl
  have h4 : l.2.val ≠ 4*K := by dsimp [l]; omega
  have he := I.attainable_link K hr l a ha
  rw [I.matchedAddress_internal K l h4 a] at he
  have hl (ys : Fin (r+1) → I.Vertex K 1) :=
    I.leftForm_section_zero K l h0 (fun t => I.horizontalSum K t a ys)
  have hr' (ys : Fin (r+1) → I.Vertex K 1) :=
    I.rightForm_section_internal K l h4 (fun t => I.horizontalSum K t a ys)
  ext v
  have hv := Set.ext_iff.mp he (v + I.biasSrc e)
  simp only [I.mem_attainable_image] at hv
  simp only [hl,hr'] at hv
  have h4' : (0 : ℕ) ≠ 4*K := by omega
  unfold siteRing at hv
  simp only [linkLeft,linkRight,l,linkBias] at hv
  simp only [dite_eq_right h4'] at hv
  constructor
  · rintro ⟨x,⟨hh,ys,hys,rfl⟩,heq⟩
    have heq' : I.linearSrc e (I.horizontalSum K (.inl (I.src e)) a ys) = v+I.biasSrc e := by
      rw [← heq,affineSrc,add_assoc,CharTwo.add_self_eq_zero,add_zero]
    obtain ⟨hh',zs,hzs,hz⟩ := hv.mp ⟨hh,ys,hys,heq'⟩
    exact ⟨hh',zs,hzs,add_right_cancel hz⟩
  · rintro ⟨hh,zs,hzs,hz⟩
    obtain ⟨hh',ys,hys,hy⟩ := hv.mpr ⟨hh,zs,hzs,congrArg (fun z : F₂ => z + I.biasSrc e) hz⟩
    refine ⟨_,⟨hh',ys,hys,rfl⟩,?_⟩
    rw [affineSrc,hy,add_assoc,CharTwo.add_self_eq_zero,add_zero]

theorem attainable_internal (K : ℕ) (hr : 1 ≤ r) (e : E) (a : I.Address)
    (ha : I.Allowed e a) (j : Fin (4*K)) (hj : j.val+1 < 4*K) :
    I.Attainable K (.inr (e,j)) a =
      I.Attainable K (.inr (e,⟨j.val+1,hj⟩)) a := by
  let l : TypeLink K E := (e,⟨j.val+1,by omega⟩)
  have h0 : l.2.val ≠ 0 := by dsimp [l]; omega
  have h4 : l.2.val ≠ 4*K := by dsimp [l]; omega
  have he := I.attainable_link K hr l a ha
  rw [I.matchedAddress_internal K l h4 a] at he
  have hl (ys : Fin (r+1) → I.Vertex K 1) :=
    I.leftForm_section_internal K l h0 (fun t => I.horizontalSum K t a ys)
  have hr' (ys : Fin (r+1) → I.Vertex K 1) :=
    I.rightForm_section_internal K l h4 (fun t => I.horizontalSum K t a ys)
  ext v
  have hv := Set.ext_iff.mp he v
  simp only [I.mem_attainable_image,hl,hr',linkBias,ite_eq_right h0,ite_eq_right h4,add_zero] at hv
  unfold siteRing at hv
  simp only [linkLeft,dite_eq_right h0,linkRight,dite_eq_right h4] at hv
  simp only [Attainable,Set.mem_ofPred_eq]
  unfold siteRing
  dsimp only [l] at hv
  simp only [Nat.add_sub_cancel] at hv
  exact hv

theorem attainable_last (K : ℕ) (hK : 0 < K) (hr : 1 ≤ r) (e : E) (a : I.Address)
    (ha : I.Allowed e a) :
    I.Attainable K (.inr (e,⟨4*K-1,by omega⟩)) a =
      I.affineDst e '' I.Attainable K (.inl (I.dst e)) (I.permuteAddress e a) := by
  let l : TypeLink K E := (e,⟨4*K,by omega⟩)
  have h0 : l.2.val ≠ 0 := by dsimp [l]; omega
  have h4 : l.2.val = 4*K := rfl
  have he := I.attainable_link K hr l a ha
  rw [I.matchedAddress_last K l h4 a] at he
  have hl (ys : Fin (r+1) → I.Vertex K 1) :=
    I.leftForm_section_internal K l h0 (fun t => I.horizontalSum K t a ys)
  have hr' (ys : Fin (r+1) → I.Vertex K 1) :=
    I.rightForm_section_last K l h4 (fun t => I.horizontalSum K t (I.permuteAddress l.1 a) ys)
  ext v
  have hv := Set.ext_iff.mp he v
  simp only [I.mem_attainable_image,hl,hr',linkBias,ite_eq_right h0,ite_eq_left h4] at hv
  unfold siteRing at hv
  simp only [linkLeft,dite_eq_right h0,linkRight,dite_eq_left h4] at hv
  rw [I.mem_attainable_image K (.inl (I.dst e)) (I.permuteAddress e a) (I.affineDst e) v]
  simp only [Attainable,Set.mem_ofPred_eq,affineDst]
  unfold siteRing
  dsimp only [l] at hv
  exact hv

theorem attainable_internal_all (K : ℕ) (hK : 0 < K) (hr : 1 ≤ r) (e : E) (a : I.Address)
    (ha : I.Allowed e a) (j : Fin (4*K)) :
    I.Attainable K (.inr (e,⟨0,by omega⟩)) a = I.Attainable K (.inr (e,j)) a := by
  have aux (n : ℕ) (hn : n < 4*K) :
      I.Attainable K (.inr (e,⟨0,by omega⟩)) a = I.Attainable K (.inr (e,⟨n,hn⟩)) a := by
    induction n with
    | zero => rfl
    | succ n ih =>
      exact (ih (by omega)).trans (I.attainable_internal K hr e a ha ⟨n,by omega⟩ hn)
  exact aux j.val j.isLt

theorem colored_wins_ac (K : ℕ) (hK : 0 < K) (hr : 1 ≤ r)
    (h : Pebble.Wins (I.valuationGraph K 0) (I.valuationGraph K 1)
      (fun x y => x.1 = y.1) (fun _ : Fin (r+2) => none)) : I.ArcConsistent := by
  refine ⟨fun p a => I.Attainable K (.inl p) a,?_,?_⟩
  · intro p a
    exact I.attainable_nonempty K h (.inl p) a (fun _ => True.intro)
  · intro e a ha
    rw [← I.permuteAddress_eq e a ha]
    exact (I.attainable_first K hK hr e a ha).trans
      ((I.attainable_internal_all K hK hr e a ha ⟨4*K-1,by omega⟩).trans
        (I.attainable_last K hK hr e a ha))

theorem colored_wins_iff_ac (hr : 2 ≤ r) :
    Pebble.Wins (I.valuationGraph (r+2) 0) (I.valuationGraph (r+2) 1)
      (fun x y => x.1 = y.1) (fun _ : Fin (r+2) => none) ↔ I.ArcConsistent := by
  classical
  constructor
  · exact I.colored_wins_ac (r+2) (by omega) (by omega)
  · intro h
    obtain ⟨Q⟩ := I.arcConsistent_iff.mp h
    exact I.ac_colored_wins Q (r+2) (by omega) hr le_rfl

end ConsistencyData
end WLTime.Compression

namespace WLTime.Marking
variable {V : Type uV} (count : V → ℕ) (q : ℕ)

theorem card_vertices [Fintype V] :
    Fintype.card (Vertex V count q) = Fintype.card V + ∑ v, count v + 1 + q := by
  rw [Fintype.card_congr (equivSum count q)]
  simp [add_assoc]

theorem sum_vertices [Fintype V] (f : Vertex V count q → ℕ) :
    ∑ x, f x = (∑ v, f (.base v)) + (∑ v, ∑ i, f (.mark v i)) + f .hub + ∑ i, f (.pad i) := by
  rw [← (equivSum count q).symm.sum_comp f]
  simp [equivSum,Fintype.sum_sum_type,Fintype.sum_sigma,add_assoc]

open scoped Classical in
theorem degree_base [Fintype V] (G : SimpleGraph V) (x : V) :
    Pebble.degree (graph G count q) (.base x) = Pebble.degree G x + count x + 1 := by
  simp only [Pebble.degree,Fintype.card_subtype,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [sum_vertices]
  unfold graph Adj
  simp [Finset.sum_boole,add_assoc,apply_ite Finset.card]

open scoped Classical in
theorem degree_mark [Fintype V] (G : SimpleGraph V) (x : V) (i : Fin (count x)) :
    Pebble.degree (graph G count q) (.mark x i) = 2 := by
  simp only [Pebble.degree,Fintype.card_subtype,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [sum_vertices]
  unfold graph Adj
  simp

open scoped Classical in
theorem degree_pad [Fintype V] (G : SimpleGraph V) (i : Fin q) :
    Pebble.degree (graph G count q) (.pad i) = 1 := by
  simp only [Pebble.degree,Fintype.card_subtype,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [sum_vertices]
  simp [graph,Adj]

open scoped Classical in
theorem degree_hub [Fintype V] (G : SimpleGraph V) :
    Pebble.degree (graph G count q) .hub = Fintype.card V + ∑ v, count v + q := by
  simp only [Pebble.degree,Fintype.card_subtype,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [sum_vertices]
  simp [graph,Adj]

end WLTime.Marking

namespace WLTime.Marking
variable {V : Type uV} {W : Type uW} {D : Type uD} [Fintype V] [Fintype W]

open scoped Classical in
theorem base_degree_lt (G : SimpleGraph V) (x : V) : Pebble.degree G x < Fintype.card V := by
  have h := G.degree_lt_card_verts x
  rwa [← SimpleGraph.card_neighborSet_eq_degree] at h

theorem sum_count_gt (count : V → ℕ) (x : V)
    (hN : 2 ≤ Fintype.card V) (hpos : ∀ v, 0 < count v) : count x < ∑ v, count v := by
  classical
  have hne : ∃ y : V, y ≠ x := by
    by_contra h
    push Not at h
    have hcard : Fintype.card V ≤ 1 := Fintype.card_le_of_injective
      (fun _ : V => ()) (by intro a b _; exact (h a).trans (h b).symm)
    omega
  obtain ⟨y,hy⟩ := hne
  have hb : count y ≤ ∑ v ∈ Finset.univ.erase x, count v :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simp [hy])
  have he := Finset.sum_erase_add Finset.univ count (Finset.mem_univ x)
  have hp := hpos y
  omega

theorem hub_above_base (G : SimpleGraph V) (count : V → ℕ) (q : ℕ)
    (hN : 2 ≤ Fintype.card V) (hpos : ∀ v, 0 < count v) (x : V) :
    Pebble.degree (graph G count q) (.base x) < Pebble.degree (graph G count q) .hub := by
  rw [degree_base,degree_hub]
  have hsum := sum_count_gt count x hN hpos
  have hg := base_degree_lt G x
  omega

theorem code_of_degree {N j l dg dh : ℕ} (hg : dg < N) (hh : dh < N)
    (he : dg + j*(N+1)+1 = dh + l*(N+1)+1) : j=l := by
  rcases lt_trichotomy j l with h | h | h
  · have hm := Nat.mul_le_mul_right (N+1) (show j+1 ≤ l by omega)
    nlinarith
  · exact h
  · have hm := Nat.mul_le_mul_right (N+1) (show l+1 ≤ j by omega)
    nlinarith

end WLTime.Marking

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Padding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uV uW uD uP uE uT uL uA uB

namespace WLTime.Compression
namespace ConsistencyData
variable {r m : ℕ} {P : Type uP} {E : Type uE} [Fintype P] [Fintype E]
    (I : ConsistencyData (r+1) m P E)

theorem two_le_card_base [Nonempty P] (K : ℕ) (hm : 2 ≤ m) :
    2 ≤ Fintype.card (I.Vertex K 0) := by
  classical
  let p : P := Classical.choice inferInstance
  let z : Fin m := ⟨0,by omega⟩
  let f : Fin m → I.Vertex K 0 := fun a =>
    ⟨⟨.site 0 (.inl p) a z,True.intro,True.intro⟩,I.zeroValuation K _⟩
  have hf : Function.Injective f := by
    intro a b h
    have he := congrArg (fun x : I.Vertex K 0 => x.1.val) h
    exact (BlockName.site.inj he).2.2.1
  have hc := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin] at hc
  omega

end ConsistencyData
end WLTime.Compression

namespace WLTime

theorem pebble_iff_wins {n K : ℕ} (G H : Graph n) (P : Position K n) :
    Pebble.Wins G.simple H.simple (fun _ _ => True) P ↔ Wins G H P := by
  constructor
  · rintro ⟨I,hI⟩
    let J : GameInvariant G H K := {
      safe := I.safe
      forget := I.forget
      atomic := by
        intro Q hQ i j x y u v hi hj
        obtain ⟨he,ha⟩ := (I.atomic hQ).2 i j x y u v hi hj
        refine ⟨he,?_⟩
        change (G.adj x u = true ↔ H.adj y v = true) at ha
        cases hg : G.adj x u <;> cases hh : H.adj y v <;> simp_all
      extend := I.extend }
    exact ⟨J,hI⟩
  · rintro ⟨I,hI⟩
    let J : Pebble.Invariant G.simple H.simple (fun _ _ => True) K := {
      safe := I.safe
      forget := I.forget
      atomic := by
        intro Q hQ
        refine ⟨fun _ _ _ _ => True.intro,?_⟩
        intro i j x y u v hi hj
        obtain ⟨he,ha⟩ := I.atomic hQ i j x y u v hi hj
        exact ⟨he,by change (_ = true ↔ _ = true); rw [ha]⟩
      extend := I.extend }
    exact ⟨J,hI⟩

theorem wins_ofSimple_iff {A : Type uA} {B : Type uB} {n K : ℕ} (G : SimpleGraph A) (H : SimpleGraph B)
    (e : A ≃ Fin n) (f : B ≃ Fin n) :
    Wins (Graph.ofSimple G e) (Graph.ofSimple H f) (fun _ : Fin K => none) ↔
      Pebble.Wins G H (fun _ _ => True) (fun _ : Fin K => none) := by
  rw [← pebble_iff_wins]
  constructor
  · intro h
    have hh := h.transport (G' := G) (H' := H) e.symm f.symm
      (fun x y => by simp [Graph.ofSimple,Graph.simple,Graph.adj])
      (fun x y => by simp [Graph.ofSimple,Graph.simple,Graph.adj])
    simpa only [Pebble.Position.map_none] using hh
  · intro h
    have hh := h.transport e f (fun x y => (Graph.ofSimple_adj G e x y).symm)
      (fun x y => (Graph.ofSimple_adj H f x y).symm)
    simpa only [Pebble.Position.map_none] using hh

end WLTime

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Enumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uT uL uA uP uE uV uW uD uU

namespace WLTime.Marking
variable {V : Type uV} {W : Type uW} {D : Type uD} [Fintype V] [Fintype W]

theorem degree_detect_base_spaced (G : SimpleGraph V) (H : SimpleGraph W)
    (c : V → D) (d : W → D) (code : D → ℕ) (hcode : Function.Injective code)
    (hpos : ∀ b, 0 < code b) (e : V ≃ W) (hc : ∀ v, c v = d (e v))
    (q B : ℕ) (hB : Fintype.card V ≤ B) (hN : 2 ≤ Fintype.card V) (x : V)
    (y : Vertex W (fun v => code (d v)*(B+1)) q)
    (hd : Pebble.degree (graph G (fun v => code (c v)*(B+1)) q) (.base x) =
      Pebble.degree (graph H (fun v => code (d v)*(B+1)) q) y) :
    ∃ z, y = .base z ∧ c x = d z := by
  have hcard : Fintype.card V = Fintype.card W := Fintype.card_congr e
  have hx : 2 < Pebble.degree (graph G (fun v => code (c v)*(B+1)) q) (.base x) := by
    rw [degree_base]
    have hm := Nat.mul_le_mul_right (B+1) (hpos (c x))
    nlinarith
  cases y with
  | base z =>
    refine ⟨z,rfl,hcode ?_⟩
    rw [degree_base,degree_base] at hd
    exact code_of_degree ((base_degree_lt G x).trans_le hB) ((hcard ▸ base_degree_lt H z).trans_le hB) hd
  | mark z i => rw [degree_mark] at hd; omega
  | pad i => rw [degree_pad] at hd; omega
  | hub =>
    have hsum : (∑ v : W, code (d v)*(B+1)) =
        ∑ v : V, code (c v)*(B+1) := by
      rw [← e.sum_comp (fun v => code (d v)*(B+1))]
      simp_rw [← hc]
    have hh := hub_above_base G (fun v => code (c v)*(B+1)) q hN
      (fun v => Nat.mul_pos (hpos (c v)) (by omega)) x
    rw [degree_hub] at hd hh
    rw [← hcard,hsum] at hd
    omega

theorem wins_bases_spaced (G : SimpleGraph V) (H : SimpleGraph W)
    (c : V → D) (d : W → D) (code : D → ℕ) (hcode : Function.Injective code)
    (hpos : ∀ b, 0 < code b) (e₀ : V ≃ W) (hc : ∀ v, c v = d (e₀ v))
    (q K B : ℕ) (hB : Fintype.card V ≤ B) (hN : 2 ≤ Fintype.card V) (hK : 2 ≤ K)
    (h : Pebble.Wins (graph G (fun v => code (c v)*(B+1)) q)
      (graph H (fun v => code (d v)*(B+1)) q) (fun _ _ => True)
      (fun _ : Fin K => none)) :
    Pebble.Wins G H (fun v w => c v = d w) (fun _ : Fin K => none) := by
  classical
  let J : Pebble.Invariant G H (fun v w => c v = d w) K := {
    safe := fun P => Pebble.Wins (graph G (fun v => code (c v)*(B+1)) q)
      (graph H (fun v => code (d v)*(B+1)) q) (fun _ _ => True) (basePosition P)
    forget := by
      intro P Q hQ hPQ
      refine hQ.forget (fun i => ?_)
      rcases hPQ i with hi | hi
      · exact Or.inl (by simp [basePosition,hi])
      · exact Or.inr (by simp [basePosition,hi])
    atomic := by
      intro P hP
      constructor
      · intro i x y hi
        have hdi := hP.degree_eq hK (i := i) (x := .base x) (y := .base y) (by simp [basePosition,hi])
        obtain ⟨z,hz,hcz⟩ := degree_detect_base_spaced G H c d code hcode hpos e₀ hc q B hB hN x (.base y) hdi
        cases Vertex.base.inj hz
        exact hcz
      · intro i j x y u v hi hj
        have hh := hP.atomic.2 i j (.base x) (.base y) (.base u) (.base v)
          (by simp [basePosition,hi]) (by simp [basePosition,hj])
        simpa only [Vertex.base.injEq,graph,Adj] using hh
    extend := by
      intro P hP i hi
      obtain ⟨e,he⟩ := hP.extend i (by simp [basePosition,hi])
      have hb (x : V) : ∃ y, e (.base x) = .base y ∧ c x = d y := by
        exact degree_detect_base_spaced G H c d code hcode hpos e₀ hc q B hB hN x (e (.base x))
          ((he (.base x)).degree_eq hK (Function.update_self _ _ _))
      choose f hf hcf using hb
      have hinj : Function.Injective f := by
        intro x y hxy
        exact Vertex.base.inj (e.injective (by rw [hf,hf,hxy]))
      let eb : V ≃ W := Equiv.ofBijective f
        ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj,Fintype.card_congr e₀⟩)
      refine ⟨eb,fun x => ?_⟩
      rw [basePosition_update]
      simpa only [hf,eb,Equiv.ofBijective_apply] using he (.base x) }
  refine ⟨J,?_⟩
  unfold J basePosition
  exact h

end WLTime.Marking

namespace WLTime.Marking

variable {V : Type uV} {U : Type uU} {count : V → ℕ}

theorem raw_diameter (G : SimpleGraph V) (decode : U → Option (Slot V count)) (x y : Option U) :
    x=y ∨ (rawGraph G decode).Adj x y ∨
      ∃ z,(rawGraph G decode).Adj x z ∧ (rawGraph G decode).Adj z y := by
  cases x <;> cases y <;> simp only [rawGraph,rawAdj] <;> try tauto

theorem rawEquiv_adj [Fintype U] (G : SimpleGraph V) (decode : U → Option (Slot V count))
    (h : ∀ v,∃!u,decode u=some v) (x y : Option U) :
    (graph G count _).Adj (rawEquiv decode h x) (rawEquiv decode h y) ↔
      (rawGraph G decode).Adj x y := by
  classical
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some y =>
      cases hy : decode y with
      | none => simp only [rawEquiv,Equiv.coe_fn_mk,hy,↓reduceDIte,graph,rawGraph,rawAdj,Adj]
      | some v => cases v <;> simp only [rawEquiv,Equiv.coe_fn_mk,hy,reduceCtorEq,↓reduceDIte,graph,rawGraph,rawAdj,Adj]
  | some x =>
    cases y with
    | none =>
      cases hx : decode x with
      | none => simp only [rawEquiv,Equiv.coe_fn_mk,hx,↓reduceDIte,graph,rawGraph,rawAdj,Adj]
      | some v => cases v <;> simp only [rawEquiv,Equiv.coe_fn_mk,hx,reduceCtorEq,↓reduceDIte,graph,rawGraph,rawAdj,Adj]
    | some y =>
      cases hx : decode x with
      | none =>
        cases hy : decode y with
        | none => simp only [rawEquiv,Equiv.coe_fn_mk,hx,hy,↓reduceDIte,graph,rawGraph,rawAdj,Adj]
        | some v => cases v <;> simp only [rawEquiv,Equiv.coe_fn_mk,hx,hy,reduceCtorEq,↓reduceDIte,graph,rawGraph,rawAdj,Adj]
      | some v =>
        cases hy : decode y with
        | none => cases v <;> simp only [rawEquiv,Equiv.coe_fn_mk,hx,hy,reduceCtorEq,↓reduceDIte,graph,rawGraph,rawAdj,Adj]
        | some w => cases v <;> cases w <;> simp only [rawEquiv,Equiv.coe_fn_mk,hx,hy,reduceCtorEq,↓reduceDIte,graph,rawGraph,rawAdj,Adj,slotAdj]

end WLTime.Marking

namespace WLTime.Marking

variable {D : Type uD} {V : Type uV} {p : D → Prop} {count : V → ℕ}

 theorem decodeSlots_complete (e : {d // p d} ≃ V) (L q : ℕ)
    (hL : ∀ v,count v+1≤L) (v : Slot V count) :
    ∃! u,decodeSlots e L q u=some v := by
  classical
  cases v with
  | inl v =>
    let d := e.symm v
    let j : Fin L := ⟨0,by have := hL v; omega⟩
    refine ⟨.inl (d.val,j),?_,?_⟩
    · have hed : e ⟨d.val,d.property⟩=v := e.apply_symm_apply v
      simp only [decodeSlots,d.property,↓reduceDIte,j,↓reduceIte]
      exact congrArg (fun v => some (Sum.inl v)) hed
    · intro u hu
      cases u with
      | inr u => simp only [decodeSlots,reduceCtorEq] at hu
      | inl u =>
        rcases u with ⟨a,i⟩
        by_cases ha : p a
        · by_cases hi : i.val=0
          · simp only [decodeSlots,dite_eq_left ha,ite_eq_left hi,Option.some.injEq,Sum.inl.injEq] at hu
            have hd : (⟨a,ha⟩ : {d // p d})=d := e.injective (hu.trans (e.apply_symm_apply v).symm)
            have hj : i=j := Fin.ext hi
            rw [← congrArg Subtype.val hd,← hj]
          · simp only [decodeSlots,dite_eq_left ha,ite_eq_right hi] at hu
            split at hu <;> simp only [Option.some.injEq,reduceCtorEq] at hu
        · simp only [decodeSlots,dite_eq_right ha,reduceCtorEq] at hu
  | inr v =>
    rcases v with ⟨v,i⟩
    let d := e.symm v
    let j : Fin L := ⟨i.val+1,by have := hL v; omega⟩
    refine ⟨.inl (d.val,j),?_,?_⟩
    · have hed : e ⟨d.val,d.property⟩=v := e.apply_symm_apply v
      simp only [decodeSlots,d.property,↓reduceDIte,j,Nat.add_eq_zero_iff,
        Nat.one_ne_zero,and_false,↓reduceIte,Nat.add_sub_cancel]
      simp only [hed,i.isLt,↓reduceDIte]
      congr 2
      apply Sigma.ext hed
      exact (Fin.heq_ext_iff (congrArg count hed)).mpr rfl
    · intro u hu
      cases u with
      | inr u => simp only [decodeSlots,reduceCtorEq] at hu
      | inl u =>
        rcases u with ⟨a,t⟩
        by_cases ha : p a
        · by_cases ht : t.val=0
          · simp only [decodeSlots,dite_eq_left ha,ite_eq_left ht,Option.some.injEq,reduceCtorEq] at hu
          · simp only [decodeSlots,dite_eq_left ha,ite_eq_right ht] at hu
            split at hu
            · rename_i hh
              have he : e ⟨a,ha⟩=v := congrArg (fun z : Option (Slot V count) =>
                z.elim (e ⟨a,ha⟩) (Sum.elim id Sigma.fst)) hu
              have hd : (⟨a,ha⟩ : {d // p d})=d := e.injective (he.trans (e.apply_symm_apply v).symm)
              have hx : t.val-1=i.val := congrArg (fun z : Option (Slot V count) =>
                z.elim 0 (Sum.elim (fun _ => 0) (fun v => v.2.val))) hu
              have hj : t=j := Fin.ext (by dsimp [j]; omega)
              rw [← congrArg Subtype.val hd,← hj]
            · simp only [reduceCtorEq] at hu
        · simp only [decodeSlots,dite_eq_right ha,reduceCtorEq] at hu

 theorem raw_holes_eq {W : Type uW} {U : Type uU} [Fintype V] [Fintype W] [Fintype U]
    {count' : W → ℕ} (e : V ≃ W) (he : ∀ v,count v=count' (e v))
    (a : U → Option (Slot V count)) (b : U → Option (Slot W count'))
    (ha : ∀ v,∃!u,a u=some v) (hb : ∀ v,∃!u,b u=some v) :
    Fintype.card {u // a u=none}=Fintype.card {u // b u=none} := by
  classical
  have h1 := Fintype.card_congr (rawEquiv a ha)
  have h2 := Fintype.card_congr (rawEquiv b hb)
  rw [card_vertices] at h1 h2
  have hc := Fintype.card_congr e
  have hs : ∑ v,count v=∑ w,count' w := by
    rw [← e.sum_comp count']; simp_rw [he]
  omega

end WLTime.Marking

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Circuits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA uB uG uE uAlphabet uJ

namespace WLTime.CircuitEncoding

theorem const_image {A : Type uA} {B : Type uB} {S : Set A} (hS : S.Nonempty) (b : B) :
    (fun _ : A => b) '' S = {b} :=
  image_singleton_of_forall hS _ _ (fun _ _ => rfl)

theorem value_of_image_singleton {A : Type uA} {B : Type uB} {S : Set A} {f : A → B} {b : B}
    (h : f '' S = {b}) {x : A} (hx : x ∈ S) : f x=b := by
  have hm := Set.mem_image_of_mem f hx
  rw [h] at hm
  exact hm

end WLTime.CircuitEncoding

namespace WLTime.CircuitEncoding.Circuit
variable {G : Type uG} {E : Type uE} (C : Circuit G E)

namespace Witness
variable {C} (W : C.Witness)

theorem port_zero (e : E) (h : C.output (C.src e) '' W.gate (C.src e) = {0}) :
    (fun x => x (C.port e)) '' W.gate (C.dst e) = {0} := by
  rw [← W.third e]
  apply image_singleton_of_forall (W.buffer_nonempty e)
  intro z hz
  rw [value_of_image_singleton ((W.first e).symm.trans h) hz,
    value_of_image_singleton ((W.second e).symm.trans h) hz,zero_add]

theorem output_zero (g : G)
    (h : ∀ p : Fin (C.kind g).dim, (fun x => x p) '' W.gate g = {0}) :
    C.output g '' W.gate g = {0} := by
  apply image_singleton_of_forall (W.gate_nonempty g)
  intro x hx
  unfold output
  apply Finset.sum_eq_zero
  intro i _
  exact value_of_image_singleton (h i) hx

theorem true_output_zero (g : G) (ht : C.TrueAt g) : C.output g '' W.gate g = {0} := by
  induction g using (measure C.rank).wf.induction with
  | h g ih =>
    rw [TrueAt] at ht
    split_ifs at ht with hs
    · rcases ht with hseed | ⟨e,he,hsrc⟩
      · exact W.seeds g hseed
      · subst g
        have ho := ih (C.src e) (C.forward e) hsrc
        have hp := W.port_zero e ho
        have hf : C.output (C.dst e) = fun x => x (C.port e) :=
          funext (C.output_scalar_eq_port (C.dst e) hs (C.port e))
        rw [hf]
        exact hp
    · apply W.output_zero g
      intro p
      obtain ⟨e,he,hp,hsrc⟩ := ht p
      subst g
      have ho := W.port_zero e (ih (C.src e) (C.forward e) hsrc)
      have hpp : C.port e = p := Fin.ext hp
      simpa only [hpp] using ho

include W in
theorem all_tests_false : ∀ g, C.test g = true → ¬C.TrueAt g := by
  intro g hg ht
  have he := (W.true_output_zero g ht).symm.trans (W.tests g hg)
  have : (0 : Bit)=1 := Set.singleton_injective he
  exact zero_ne_one this

end Witness

theorem witness_iff_tests_false : Nonempty C.Witness ↔ ∀ g, C.test g = true → ¬C.TrueAt g :=
  ⟨fun ⟨W⟩ => W.all_tests_false,fun h => ⟨C.canonicalWitness h⟩⟩

end WLTime.CircuitEncoding.Circuit

namespace WLTime.CircuitEncoding.Circuit
variable {G : Type uG} {E : Type uE} (C : Circuit G E)

theorem truth_iff_of_equations (V : G → Prop)
    (hV : ∀ g, V g ↔ if C.kind g = .scalar then C.seed g = true ∨
      ∃ (e : E) (_h : C.dst e=g), V (C.src e)
      else ∀ p : Fin (C.kind g).dim,
        ∃ (e : E) (_h : C.dst e=g), (C.port e).val = p.val ∧ V (C.src e))
    (g : G) : C.TrueAt g ↔ V g := by
  induction g using (measure C.rank).wf.induction with
  | h g ih =>
    rw [TrueAt,hV g]
    split_ifs
    · apply or_congr Iff.rfl
      apply exists_congr
      intro e
      apply exists_congr
      intro he
      apply ih
      subst g
      exact C.forward e
    · apply forall_congr'
      intro p
      apply exists_congr
      intro e
      apply exists_congr
      intro he
      apply and_congr Iff.rfl
      apply ih
      subst g
      exact C.forward e

end WLTime.CircuitEncoding.Circuit

namespace WLTime.CircuitEncoding.Tableau
variable {Alphabet : Type uAlphabet} {J : Type uJ} (F : Alphabet → Alphabet → Alphabet → Alphabet) (shift : Equiv.Perm J) (initial : J → Alphabet)

variable {H : ℕ}

theorem incoming_first (V : Node Alphabet J H → Prop) (a b c : Alphabet) (t : Fin H) (j : J) (p : Fin 2) :
    (∃ e : Connection Alphabet J H, target F e = (.first a b c,t,j) ∧
      (port F e).val=p.val ∧ V (source shift e)) ↔
    ∃ ht : 0<t.val,
      (p=0 ∧ V (.scalar a,prevTime t ht,shift.symm j)) ∨
      (p=1 ∧ V (.scalar b,prevTime t ht,j)) := by
  constructor
  · rintro ⟨e,he,hp,hv⟩
    cases e with
    | left a' b' c' t' ht' j' =>
      simp only [target,Prod.mk.injEq,Gate.first.injEq] at he
      obtain ⟨⟨rfl,rfl,rfl⟩,rfl,rfl⟩ := he
      exact ⟨ht',Or.inl ⟨Fin.ext hp.symm,hv⟩⟩
    | center a' b' c' t' ht' j' =>
      simp only [target,Prod.mk.injEq,Gate.first.injEq] at he
      obtain ⟨⟨rfl,rfl,rfl⟩,rfl,rfl⟩ := he
      exact ⟨ht',Or.inr ⟨Fin.ext hp.symm,hv⟩⟩
    | bridge => simp [target] at he
    | right => simp [target] at he
    | out => simp [target] at he
  · rintro ⟨ht,⟨rfl,hv⟩ | ⟨rfl,hv⟩⟩
    · exact ⟨.left a b c t ht j,rfl,rfl,hv⟩
    · exact ⟨.center a b c t ht j,rfl,rfl,hv⟩

theorem incoming_second (V : Node Alphabet J H → Prop) (a b c : Alphabet) (t : Fin H) (j : J) (p : Fin 2) :
    (∃ e : Connection Alphabet J H, target F e = (.second a b c,t,j) ∧
      (port F e).val=p.val ∧ V (source shift e)) ↔
    (p=0 ∧ V (.first a b c,t,j)) ∨
      ∃ ht : 0<t.val, p=1 ∧ V (.scalar c,prevTime t ht,shift j) := by
  constructor
  · rintro ⟨e,he,hp,hv⟩
    cases e with
    | bridge a' b' c' t' j' =>
      simp only [target,Prod.mk.injEq,Gate.second.injEq] at he
      obtain ⟨⟨rfl,rfl,rfl⟩,rfl,rfl⟩ := he
      exact Or.inl ⟨Fin.ext hp.symm,hv⟩
    | right a' b' c' t' ht' j' =>
      simp only [target,Prod.mk.injEq,Gate.second.injEq] at he
      obtain ⟨⟨rfl,rfl,rfl⟩,rfl,rfl⟩ := he
      exact Or.inr ⟨ht',Fin.ext hp.symm,hv⟩
    | left => simp [target] at he
    | center => simp [target] at he
    | out => simp [target] at he
  · rintro (⟨rfl,hv⟩ | ⟨ht,rfl,hv⟩)
    · exact ⟨.bridge a b c t j,rfl,rfl,hv⟩
    · exact ⟨.right a b c t ht j,rfl,rfl,hv⟩

theorem incoming_scalar (V : Node Alphabet J H → Prop) (f : Alphabet) (t : Fin H) (j : J) :
    (∃ e : Connection Alphabet J H, target F e = (.scalar f,t,j) ∧ V (source shift e)) ↔
    ∃ a b c, F a b c=f ∧ V (.second a b c,t,j) := by
  constructor
  · rintro ⟨e,he,hv⟩
    cases e with
    | out a b c t' j' =>
      simp only [target,Prod.mk.injEq,Gate.scalar.injEq] at he
      obtain ⟨hf,rfl,rfl⟩ := he
      exact ⟨a,b,c,hf,hv⟩
    | left => simp [target] at he
    | center => simp [target] at he
    | bridge => simp [target] at he
    | right => simp [target] at he
  · rintro ⟨a,b,c,hf,hv⟩
    exact ⟨.out a b c t j,by simp only [target,hf],hv⟩

theorem expected_equations (accepting : Alphabet → Prop) (g : Node Alphabet J H) :
    expected F shift initial g ↔
      if (circuit F shift initial accepting).kind g = .scalar then
        (circuit F shift initial accepting).seed g = true ∨
          ∃ (e : Connection Alphabet J H) (_h : (circuit F shift initial accepting).dst e=g),
            expected F shift initial ((circuit F shift initial accepting).src e)
      else ∀ p : Fin ((circuit F shift initial accepting).kind g).dim,
        ∃ (e : Connection Alphabet J H) (_h : (circuit F shift initial accepting).dst e=g),
          ((circuit F shift initial accepting).port e).val=p.val ∧
            expected F shift initial ((circuit F shift initial accepting).src e) := by
  classical
  rcases g with ⟨g,t,j⟩
  cases g with
  | scalar f =>
    simp only [circuit,Gate.kind,↓reduceIte,exists_prop]
    change (f=run F shift initial t.val j) ↔
      seed initial (.scalar f,t,j) = true ∨
        ∃ e : Connection Alphabet J H, target F e = (.scalar f,t,j) ∧
          expected F shift initial (source shift e)
    rw [incoming_scalar]
    simp only [seed,decide_eq_true_eq,expected]
    constructor
    · intro hf
      by_cases ht : t.val=0
      · exact Or.inl ⟨ht,by simpa only [ht,run_zero] using hf⟩
      · have hp : 0<t.val := Nat.pos_of_ne_zero ht
        have he : t.val-1+1=t.val := Nat.sub_add_cancel hp
        right
        refine ⟨run F shift initial (t.val-1) (shift.symm j),
          run F shift initial (t.val-1) j,run F shift initial (t.val-1) (shift j),?_,hp,rfl,rfl,rfl⟩
        rw [← run_succ F shift initial (t.val-1) j,he]
        exact hf.symm
    · rintro (⟨ht,hf⟩ | ⟨a,b,c,hf,ht,ha,hb,hc⟩)
      · simpa only [ht,run_zero] using hf
      · have he : t.val-1+1=t.val := Nat.sub_add_cancel ht
        rw [ha,hb,hc,← run_succ F shift initial (t.val-1) j,he] at hf
        exact hf.symm
  | first a b c =>
    simp only [circuit,Gate.kind,reduceCtorEq,↓reduceIte,exists_prop]
    change expected F shift initial (.first a b c,t,j) ↔
      ∀ p : Fin 2, ∃ e : Connection Alphabet J H, target F e=(.first a b c,t,j) ∧
        (port F e).val=p.val ∧ expected F shift initial (source shift e)
    simp_rw [incoming_first]
    simp only [Fin.forall_fin_two,expected,prevTime]
    simp
    tauto
  | second a b c =>
    simp only [circuit,Gate.kind,reduceCtorEq,↓reduceIte,exists_prop]
    change expected F shift initial (.second a b c,t,j) ↔
      ∀ p : Fin 2, ∃ e : Connection Alphabet J H, target F e=(.second a b c,t,j) ∧
        (port F e).val=p.val ∧ expected F shift initial (source shift e)
    simp_rw [incoming_second]
    simp only [Fin.forall_fin_two,expected,prevTime]
    simp
    tauto

theorem truth_iff_expected (accepting : Alphabet → Prop) (g : Node Alphabet J H) :
    (circuit F shift initial accepting).TrueAt g ↔ expected F shift initial g :=
  (circuit F shift initial accepting).truth_iff_of_equations
    (expected F shift initial) (expected_equations F shift initial accepting) g

theorem tests_false_iff (hH : 0<H) (accepting : Alphabet → Prop) :
    (∀ g : Node Alphabet J H, (circuit F shift initial accepting).test g = true →
      ¬(circuit F shift initial accepting).TrueAt g) ↔
    ∀ j, ¬accepting (run F shift initial (H-1) j) := by
  classical
  constructor
  · intro h j ha
    have ht : H-1<H := by omega
    apply h (.scalar (run F shift initial (H-1) j),⟨H-1,ht⟩,j)
    · change decide (H-1+1=H ∧ accepting (run F shift initial (H-1) j)) = true
      exact decide_eq_true ⟨by omega,ha⟩
    · exact (truth_iff_expected F shift initial accepting _).mpr rfl
  · rintro h ⟨g,t,j⟩ hg ht
    have he := (truth_iff_expected F shift initial accepting _).mp ht
    cases g with
    | scalar f =>
      change decide (t.val+1=H ∧ accepting f) = true at hg
      obtain ⟨ht,hf⟩ := of_decide_eq_true hg
      have hv : t.val=H-1 := by omega
      change f=run F shift initial t.val j at he
      exact h j (by simpa only [he,hv] using hf)
    | first => exact Bool.false_ne_true hg
    | second => exact Bool.false_ne_true hg

end WLTime.CircuitEncoding.Tableau

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Turing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uJ

namespace WLTime

namespace OneTape
variable (M : OneTape)
open scoped Classical

variable {J : Type uJ}

theorem written_snapshot (C : M.Config J) (j : J) :
    M.written (M.snapshot C j) =
      if j=C.head then (M.action C.state (C.tape C.head)).2.1 else C.tape j := by
  classical
  by_cases hj : j=C.head <;> simp [written,snapshot,hj]

theorem arrival_snapshot (C : M.Config J) (j : J) (d : Move) :
    M.arrival d (M.snapshot C j) =
      if j=C.head ∧ (M.action C.state (C.tape C.head)).2.2=d then
        some (M.action C.state (C.tape C.head)).1 else none := by
  classical
  by_cases hj : j=C.head <;> simp [arrival,snapshot,hj]

theorem moveAt_eq_iff (shift : Equiv.Perm J) (d : Move) (h j : J) :
    j=moveAt shift d h ↔ (j=h ∧ d=.stay) ∨
      (shift.symm j=h ∧ d=.right) ∨ (shift j=h ∧ d=.left) := by
  cases d with
  | left => simp [moveAt,Equiv.eq_symm_apply]
  | stay => simp [moveAt]
  | right => simp [moveAt,Equiv.symm_apply_eq]

theorem snapshot_step (shift : Equiv.Perm J) (C : M.Config J) (j : J) :
    M.snapshot (M.step shift C) j =
      M.localRule (M.snapshot C (shift.symm j)) (M.snapshot C j) (M.snapshot C (shift j)) := by
  classical
  apply Prod.ext
  · change (Function.update C.tape C.head (M.action C.state (C.tape C.head)).2.1) j =
      M.written (M.snapshot C j)
    rw [M.written_snapshot]
    exact Function.update_apply _ _ _ _
  · change (if j=moveAt shift (M.action C.state (C.tape C.head)).2.2 C.head then
        some (M.action C.state (C.tape C.head)).1 else none) =
      ((M.arrival .stay (M.snapshot C j)).or (M.arrival .right (M.snapshot C (shift.symm j)))).or
        (M.arrival .left (M.snapshot C (shift j)))
    simp only [M.arrival_snapshot,moveAt_eq_iff]
    by_cases h0 : j=C.head ∧ (M.action C.state (C.tape C.head)).2.2=.stay <;>
      by_cases h1 : shift.symm j=C.head ∧ (M.action C.state (C.tape C.head)).2.2=.right <;>
      by_cases h2 : shift j=C.head ∧ (M.action C.state (C.tape C.head)).2.2=.left <;>
      simp [h0,h1,h2]

theorem run_snapshot (shift : Equiv.Perm J) (C : M.Config J) (t : ℕ) :
    M.snapshot (M.run shift C t) =
      CircuitEncoding.Tableau.run M.localRule shift (M.snapshot C) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext j
    rw [CircuitEncoding.Tableau.run_succ]
    change M.snapshot ((M.step shift)^[t+1] C) j = _
    rw [Function.iterate_succ_apply']
    change M.snapshot (M.step shift (M.run shift C t)) j = _
    rw [M.snapshot_step,ih]

theorem moveAt_line (d : Move) (h : ℤ) : moveAt lineShift d h = h+d.displacement := by
  cases d <;> simp [moveAt,lineShift,Move.displacement ]

theorem embed_step (C : M.Config ℤ) : M.embed (M.step lineShift C) = M.toTM.step (M.embed C) := by
  classical
  by_cases hh : C.state.val=1 ∨ C.state.val=2
  · have hc : M.step lineShift C=C := by
      cases C
      simp_all [step,action,moveAt,Function.update_eq_self]
    rw [hc]
    simp [TM.step,TM.halted,embed,hh]
  · simp only [TM.step,TM.halted,embed,hh,ite_false]
    simp only [step,action,hh,ite_false,toTM,moveAt_line]
    congr
    funext a z
    simp only [Function.update_apply]
    split <;> rename_i hz <;> simp only [hz,ite_true,ite_false]

theorem embed_run (w : List Bool) (t : ℕ) :
    M.embed (M.run lineShift (M.initial w) t)=M.toTM.run w t := by
  induction t with
  | zero => exact M.embed_initial w
  | succ t ih =>
    change M.embed ((M.step lineShift)^[t+1] (M.initial w)) = M.toTM.step^[t+1] (M.toTM.initial w)
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
    rw [M.embed_step]
    exact congrArg M.toTM.step ih

theorem step_halted {J : Type uJ} (shift : Equiv.Perm J) (C : M.Config J)
    (hh : C.state.val=1 ∨ C.state.val=2) : M.step shift C=C := by
  cases C
  simp_all [step,action,moveAt,Function.update_eq_self]

theorem line_head_step (C : M.Config ℤ) :
    C.head-1  ≤  (M.step lineShift C).head ∧ (M.step lineShift C).head  ≤  C.head+1 := by
  change C.head-1  ≤  moveAt lineShift (M.action C.state (C.tape C.head)).2.2 C.head ∧
    moveAt lineShift (M.action C.state (C.tape C.head)).2.2 C.head  ≤  C.head+1
  rw [moveAt_line]
  cases (M.action C.state (C.tape C.head)).2.2 <;> simp [Move.displacement]
  omega

theorem line_head_run (w : List Bool) (t : ℕ) :
    -(t:ℤ)  ≤  (M.run lineShift (M.initial w) t).head ∧
      (M.run lineShift (M.initial w) t).head  ≤  (t:ℤ) := by
  induction t with
  | zero => simp [run,initial]
  | succ t ih =>
    have hs := M.line_head_step (M.run lineShift (M.initial w) t)
    change -(↑(t+1):ℤ)  ≤  ((M.step lineShift)^[t+1] (M.initial w)).head ∧
      ((M.step lineShift)^[t+1] (M.initial w)).head  ≤  (↑(t+1):ℤ)
    rw [Function.iterate_succ_apply']
    change -(↑(t+1):ℤ)  ≤  (M.step lineShift (M.run lineShift (M.initial w) t)).head ∧
      (M.step lineShift (M.run lineShift (M.initial w) t)).head  ≤  (↑(t+1):ℤ)
    push_cast
    omega

theorem agrees_step {J : Type uJ} (shift : Equiv.Perm J) (π : ℤ → J) (I : Set ℤ)
    (hπ : ∀ z,π (z+1)=shift (π z)) (hinj : Set.InjOn π I)
    (C : M.Config ℤ) (D : M.Config J) (ha : M.Agrees π I C D) (hh : C.head∈I) :
    M.Agrees π I (M.step lineShift C) (M.step shift D) := by
  classical
  obtain ⟨hs,hd,ht⟩ := ha
  have scanned : D.tape D.head=C.tape C.head := by rw [hd]; exact ht _ hh
  have moved (d : Move) : moveAt shift d (π C.head)=π (moveAt lineShift d C.head) := by
    rw [moveAt_line]
    cases d with
    | stay => simp [moveAt,Move.displacement]
    | right => exact (hπ C.head).symm
    | left =>
      change shift.symm (π C.head)=π (C.head+(-1))
      apply shift.injective
      rw [shift.apply_symm_apply,← hπ]
      congr 1
      omega
  refine ⟨?_,?_,?_⟩
  · simp only [step,hs,scanned]
  · simp only [step,hs,hd,ht _ hh,moved]
  · intro z hz
    simp only [step]
    rw [hs,scanned,hd]
    have he : π z=π C.head ↔ z=C.head := ⟨hinj hz hh,congrArg π⟩
    simp only [Function.update_apply,he]
    split <;> first | rfl | exact ht z hz

theorem agrees_run {J : Type uJ} (shift : Equiv.Perm J) (π : ℤ → J) (I : Set ℤ)
    (hπ : ∀ z,π (z+1)=shift (π z)) (hinj : Set.InjOn π I)
    (w : List Bool) (D : M.Config J) (ha : M.Agrees π I (M.initial w) D)
    (T : ℕ) (hI : ∀ z : ℤ, -(T:ℤ) ≤ z → z ≤ T → z∈I) :
    ∀ t ≤ T, M.Agrees π I (M.run lineShift (M.initial w) t) (M.run shift D t) := by
  intro t
  induction t with
  | zero => intro _; exact ha
  | succ t ih =>
    intro ht
    have hl := M.line_head_run w t
    have hi : (M.run lineShift (M.initial w) t).head∈I :=
      hI _ (by omega) (by omega)
    have hc := M.agrees_step shift π I hπ hinj _ _ (ih (by omega)) hi
    simpa only [run,Function.iterate_succ_apply'] using hc

theorem protectedInterval_injective (m T L : ℕ) (hL : 2*T+m+2< L) :
    Set.InjOn (fun z : ℤ => (z : ZMod L)) (protectedInterval m T) := by
  intro x hx y hy he
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub x y L).mp he
  have hL' : (2*(T:ℤ)+m+2)< L := by exact_mod_cast hL
  change -(T:ℤ)-1 ≤ x ∧ x ≤ (m:ℤ)+T at hx
  change -(T:ℤ)-1 ≤ y ∧ y ≤ (m:ℤ)+T at hy
  rcases le_total x y with hxy | hyx
  · have hz : y-x=0 := Int.eq_zero_of_dvd_of_nonneg_of_lt (by omega) (by omega) hd
    omega
  · have hd' : (L:ℤ)∣x-y := by simpa only [neg_sub] using (dvd_neg.mpr hd)
    have hz : x-y=0 := Int.eq_zero_of_dvd_of_nonneg_of_lt (by omega) (by omega) hd'
    omega

theorem ring_initial_agrees (w : List Bool) (T L : ℕ) (hL : 2*T+w.length+2< L) :
    M.Agrees (fun z : ℤ => (z : ZMod L)) (protectedInterval w.length T)
      (M.initial w) (M.ringInitial L w) := by
  classical
  have hp : 0< L := by omega
  let : NeZero L := ⟨Nat.ne_of_gt hp⟩
  refine ⟨rfl,by simp [ringInitial,initial],?_⟩
  intro z hz
  have hinj := protectedInterval_injective w.length T L hL
  have input_mem (i : ℕ) (hi : i< w.length) : (i:ℤ)∈protectedInterval w.length T := by
    change -(T:ℤ)-1 ≤ i ∧ (i:ℤ) ≤ (w.length:ℤ)+T
    constructor <;> omega
  have hi : (z : ZMod L).val< w.length ↔ 0 ≤ z ∧ z.toNat< w.length := by
    constructor
    · intro h
      have he : ((z : ZMod L).val : ℤ)=z := hinj (input_mem _ h) hz (by simp)
      rw [← he]
      simp only [Int.natCast_nonneg,Int.toNat_natCast,true_and]
      exact h
    · rintro ⟨hz0,hzlen⟩
      have he : (((z.toNat:ℕ):ℤ):ZMod L)=(z:ZMod L) := by rw [Int.toNat_of_nonneg hz0]
      have hsmall : z.toNat< L := by omega
      rw [← he]
      simpa only [Int.cast_natCast,ZMod.val_natCast,Nat.mod_eq_of_lt hsmall] using hzlen
  have hv (h : (z : ZMod L).val< w.length) : (z : ZMod L).val=z.toNat := by
    have he : ((z : ZMod L).val : ℤ)=z := hinj (input_mem _ h) hz (by simp)
    simpa only [Int.toNat_natCast] using congrArg Int.toNat he
  simp only [ringInitial,initial]
  by_cases hr : (z : ZMod L).val< w.length
  · simp [hi.mp hr,hv hr]
    rfl
  · simp [hr,show ¬(0 ≤ z ∧ z.toNat< w.length) from fun h => hr (hi.mpr h)]

theorem ring_run_agrees (w : List Bool) (T L : ℕ) (hL : 2*T+w.length+2< L) :
    ∀ t ≤ T,M.Agrees (fun z : ℤ => (z : ZMod L)) (protectedInterval w.length T)
      (M.run lineShift (M.initial w) t) (M.run (ringShift L) (M.ringInitial L w) t) := by
  apply M.agrees_run
  · intro z
    change ((z+1:ℤ):ZMod L)=(z:ZMod L)+1
    push_cast
    rfl
  · exact protectedInterval_injective w.length T L hL
  · exact M.ring_initial_agrees w T L hL
  · intro z hz0 hz1
    change -(T:ℤ)-1 ≤ z ∧ z ≤ (w.length:ℤ)+T
    constructor <;> omega

theorem accepting_snapshot {J : Type uJ} (C : M.Config J) :
    (∃ j,M.letterAccepting (M.snapshot C j)) ↔ C.state.val=1 := by
  classical
  constructor
  · rintro ⟨j,q,hq,hv⟩
    by_cases hj : j=C.head
    · simp only [snapshot,hj,ite_true,Option.some.injEq] at hq
      exact hq ▸ hv
    · simp [snapshot,hj] at hq
  · intro hv
    exact ⟨C.head,C.state,by simp [snapshot],hv⟩

end OneTape
end WLTime

namespace WLTime.TM
variable (M : TM)

theorem run_add (w : List Bool) (a b : ℕ) :
    M.run w (a+b)=M.step^[a] (M.run w b) :=
  Function.iterate_add_apply _ _ _ _

theorem step_frozen (C : M.Config) (h : M.halted C) : M.step C=C := by
  rw [step,ite_eq_left h]

theorem run_frozen (w : List Bool) {t u : ℕ} (hh : M.halted (M.run w t))
    (hu : t ≤ u) : M.run w u=M.run w t := by
  obtain ⟨a,rfl⟩ := Nat.exists_eq_add_of_le hu
  rw [Nat.add_comm,M.run_add]
  exact Function.iterate_fixed (M.step_frozen _ hh) a

theorem time_halted (w : List Bool) (h : M.halts w) : M.halted (M.run w (M.time w)) := by
  simp only [time]
  split_ifs
  exact Nat.find_spec h

theorem time_le_of_halted (w : List Bool) {t : ℕ} (h : M.halted (M.run w t)) : M.time w ≤ t := by
  have hh : M.halts w := ⟨t,h⟩
  simp only [time]
  split_ifs
  exact Nat.find_min' hh h

theorem accepts_iff_at_halt (w : List Bool) {t : ℕ} (h : M.halted (M.run w t)) :
    M.accepts w ↔ (M.run w t).state.val=1 := by
  constructor
  · rintro ⟨s,hs⟩
    have hx := M.run_frozen w h (Nat.le_max_right s t)
    have hy := M.run_frozen w (Or.inl hs) (Nat.le_max_left s t)
    rw [hx] at hy
    exact congrArg (fun C : M.Config => C.state.val) hy |>.trans hs
  · intro ht; exact ⟨t,ht⟩

end WLTime.TM

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Stacks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uS uA

namespace WLTime.TypedTape

namespace Machine
variable {S : Type uS} {A : Type uA} (M : Machine S A)

theorem step_live (p : S) (z : ℤ) (tape : ℤ → Symbol A)
    (q : State S) (x : Symbol A) (d : Move)
    (h : M.transition (.inr p) (tape z)=(q,x,d)) :
    M.step ⟨.inr p,z,tape⟩=⟨q,z+d.displacement,Function.update tape z x⟩ := by
  simp only [step,action,halted,reduceCtorEq,or_self,ite_false,h]

theorem step_keep (p : S) (z : ℤ) (tape : ℤ → Symbol A)
    (q : State S) (d : Move)
    (h : M.transition (.inr p) (tape z)=(q,tape z,d)) :
    M.step ⟨.inr p,z,tape⟩=⟨q,z+d.displacement,tape⟩ := by
  rw [M.step_live p z tape q (tape z) d h]
  congr 1
  exact Function.update_eq_self _ _

theorem path_iterate (C : ℕ → Config S A) (n : ℕ)
    (h : ∀ i<n,M.step (C i)=C (i+1)) : M.step^[n] (C 0)=C n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih (fun i hi => h i (by omega))]
    exact h n (by omega)

theorem concat {C D E : Config S A} {a b : ℕ}
    (h : M.step^[a] C=D) (g : M.step^[b] D=E) : M.step^[a+b] C=E := by
  rw [Nat.add_comm,Function.iterate_add_apply,h,g]

variable [Fintype S] [Fintype A]

omit [Fintype A] in
theorem state_halted (p : State S) :
    ((M.stateEquiv p).val=1 ∨ (M.stateEquiv p).val=2) ↔ M.halted p := by
  cases p with
  | inl i => simp [halted,Fin.ext_iff]
  | inr q =>
    have h : 3 ≤ (M.stateEquiv (.inr q)).val := by
      change 3 ≤ 3+(Fintype.equivFin S q).val
      omega
    simp only [halted,reduceCtorEq,or_self,iff_false]
    omega

theorem compile_action (p : State S) (x : Symbol A) :
    M.compile.action (M.stateEquiv p) (M.symbolEquiv x) =
      (M.stateEquiv (M.action p x).1,M.symbolEquiv (M.action p x).2.1,(M.action p x).2.2) := by
  simp only [OneTape.action,M.state_halted,action]
  split_ifs <;> simp

theorem embed_step (C : Config S A) :
    M.embed (M.step C)=M.compile.step OneTape.lineShift (M.embed C) := by
  simp only [embed,step,OneTape.step,M.compile_action,OneTape.moveAt_line]
  congr 1
  funext z
  simp only [Function.update_apply]
  split <;> rfl

theorem embed_initial (w : List Bool) : M.embed (M.initial w)=M.compile.initial w := by
  unfold embed initial OneTape.initial
  congr 1
  funext z
  dsimp only
  by_cases h : 0 ≤ z ∧ z.toNat<w.length
  · simp [h,TM.symbol]
    split_ifs <;> rfl
  · simp [h]
    rfl

theorem embed_run (w : List Bool) (t : ℕ) :
    M.embed (M.run w t)=M.compile.run OneTape.lineShift (M.compile.initial w) t := by
  induction t with
  | zero => exact M.embed_initial w
  | succ t ih =>
    simp only [run,Function.iterate_succ_apply',OneTape.run] at *
    rw [M.embed_step,ih]

end Machine
end WLTime.TypedTape

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Sweep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLTime.StackMachine
namespace Machine
variable (M : Machine)

 theorem stackCell_push (s : List (Fin M.alphabet)) (x : Fin M.alphabet) (i : ℕ) :
    M.stackCell (x::s) i = if i=s.length then some x else M.stackCell s i := by
  simp only [stackCell,List.reverse_cons,List.getElem?_append,List.length_reverse]
  by_cases h : i<s.length
  · rw [ite_eq_left h,ite_eq_right (by omega)]
  · rw [ite_eq_right h]
    by_cases he : i=s.length
    · simp [he]
    · have hi : s.length ≤ i := by omega
      have hx : i-s.length ≠ 0 := by omega
      rw [ite_eq_right he]
      rw [List.getElem?_eq_none (l := [x]) (by simp only [List.length_singleton]; omega)]
      rw [List.getElem?_eq_none (l := s.reverse) (by simpa using hi)]

 theorem stackCell_pop (s : List (Fin M.alphabet)) (i : ℕ) :
    M.stackCell s.tail i = if i+1=s.length then none else M.stackCell s i := by
  simp only [stackCell,← List.dropLast_reverse,List.getElem?_dropLast,List.length_reverse]
  by_cases h : i+1<s.length
  · rw [ite_eq_left (show i<s.length-1 by omega),ite_eq_right (show i+1≠s.length by omega)]
  · rw [ite_eq_right (show ¬i<s.length-1 by omega)]
    by_cases he : i+1=s.length
    · rw [ite_eq_left he]
    · rw [ite_eq_right he,List.getElem?_eq_none (by simp only [List.length_reverse]; omega)]

 theorem stackCell_none (s : List (Fin M.alphabet)) : M.stackCell s s.length=none := by
  exact List.getElem?_eq_none (by simp)

 theorem stackCell_some (s : List (Fin M.alphabet)) (i : ℕ) (hi : i<s.length) :
    (M.stackCell s i).isSome=true := by
  rw [stackCell,List.getElem?_eq_getElem (by simpa using hi)]
  rfl

 theorem storage_change (s s' : Fin M.count → List (Fin M.alphabet))
    (k : Fin M.count) (i : ℕ) (x : Option (Fin M.alphabet))
    (hj : ∀ j ≠ k,s' j=s j)
    (hk : ∀ u,M.stackCell (s' k) u=if u=i then x else M.stackCell (s k) u) :
    M.storage s'=Function.update (M.storage s) (-(i:ℤ)-2)
      (M.trackSymbol false (Function.update (M.storageTracks s (-(i:ℤ)-2)) k x)) := by
  funext z
  by_cases hz : z= -(i:ℤ)-2
  · subst z
    rw [Function.update_self,storage]
    have he : decide (-(i:ℤ)-2= -1)=false := by simp; omega
    rw [he,M.storageTracks_index,M.storageTracks_index]
    congr 1
    funext j
    by_cases h : j=k
    · subst j; simp only [Function.update_self,hk,ite_true]
    · simp only [Function.update_of_ne h,hj j h]
  · rw [Function.update_of_ne hz,storage,storage]
    congr 1
    unfold storageTracks
    split_ifs with h
    · funext j
      by_cases he : j=k
      · subst j
        rw [hk,ite_eq_right (by omega)]
      · rw [hj j he]
    · rfl

 theorem storage_push (s : Fin M.count → List (Fin M.alphabet))
    (k : Fin M.count) (x : Fin M.alphabet) :
    M.storage (Function.update s k (x::s k))=
      Function.update (M.storage s) (-((s k).length:ℤ)-2)
        (M.trackSymbol false (Function.update (M.storageTracks s (-((s k).length:ℤ)-2)) k (some x))) := by
  apply M.storage_change s _ k (s k).length (some x)
  · intro j hj; exact Function.update_of_ne hj _ _
  · intro i; rw [Function.update_self,M.stackCell_push]

 theorem storage_pop (s : Fin M.count → List (Fin M.alphabet))
    (k : Fin M.count) (hk : 0<(s k).length) :
    M.storage (Function.update s k (s k).tail)=
      Function.update (M.storage s) (-((s k).length:ℤ)-1)
        (M.trackSymbol false (Function.update (M.storageTracks s (-((s k).length:ℤ)-1)) k none)) := by
  have he : -(((s k).length-1:ℕ):ℤ)-2= -((s k).length:ℤ)-1 := by omega
  rw [← he]
  apply M.storage_change s _ k ((s k).length-1) none
  · intro j hj; exact Function.update_of_ne hj _ _
  · intro i
    rw [Function.update_self,M.stackCell_pop]
    have he : (i+1=(s k).length) ↔ (i=(s k).length-1) := by omega
    simp only [he]

 theorem seek_run (purpose : M.Purpose') (s : Fin M.count → List (Fin M.alphabet)) :
    M.sweep.step^[(s (M.purposeStack purpose)).length]
      (M.located (.inr (.seek purpose)) (-2) (M.storage s))=
      M.located (.inr (.seek purpose)) (-((s (M.purposeStack purpose)).length:ℤ)-2) (M.storage s) := by
  apply M.sweep.path_iterate (fun i =>
    M.located (.inr (.seek purpose)) (-(i:ℤ)-2) (M.storage s))
  intro i hi
  have ht : M.sweep.transition (.inr (.seek purpose)) (M.storage s (-(i:ℤ)-2))=
      (.inr (.seek purpose),M.storage s (-(i:ℤ)-2),.left) := by
    simp only [sweep,sweepTransition,M.storage_tracks,M.storageTracks_index]
    rw [M.stackCell_some _ i hi]
    rfl
  rw [located,M.sweep.step_keep _ _ _ _ _ ht]
  simp only [Move.displacement,located,Nat.cast_add,Nat.cast_one]
  congr 1
  omega

 theorem return_run (p : M.Control) (s : Fin M.count → List (Fin M.alphabet))
    (n : ℕ) (h : ∀ z< -1,M.sweep.transition (.inr p) (M.storage s z)=
      (.inr p,M.storage s z,.right)) :
    M.sweep.step^[n] (M.located (.inr p) (-(n:ℤ)-1) (M.storage s))=
      M.located (.inr p) (-1) (M.storage s) := by
  have he : M.located (.inr p) (-1) (M.storage s)=
      M.located (.inr p) ((n:ℤ)-(n:ℤ)-1) (M.storage s) := by simp
  rw [he]
  have hz0 : -(n:ℤ)-1=(0:ℤ)-(n:ℤ)-1 := by omega
  rw [hz0]
  apply M.sweep.path_iterate (fun i =>
    M.located (.inr p) ((i:ℤ)-(n:ℤ)-1) (M.storage s))
  intro i hi
  have hz : (i:ℤ)-(n:ℤ)-1< -1 := by omega
  rw [located,M.sweep.step_keep _ _ _ _ _ (h _ hz)]
  simp only [Move.displacement,located,Nat.cast_add,Nat.cast_one]
  congr 1
  omega

 theorem storage_top (s : Fin M.count → List (Fin M.alphabet)) (k : Fin M.count) :
    M.storageTracks s (-((s k).length:ℤ)-1) k=(s k).head? := by
  cases he : s k with
  | nil => simp
  | cons x xs =>
    have hz : -((x::xs).length:ℤ)-1= -(xs.length:ℤ)-2 := by simp; omega
    rw [hz,M.storageTracks_index]
    change M.stackCell (s k) xs.length=_
    rw [he,M.stackCell_push,ite_eq_left rfl]
    rfl

 theorem peek_run (k : Fin M.count) (q : Fin M.states) (v : M.Tops)
    (s : Fin M.count → List (Fin M.alphabet)) :
    M.sweep.step^[2*(s k).length+2]
      (M.located (.inr (.seek (.peek k q v))) (-2) (M.storage s))=
      M.located (.inr (.returnPeek k q (Function.update v k (s k).head?))) (-1) (M.storage s) := by
  have h0 := M.seek_run (.peek k q v) s
  simp only [purposeStack] at h0
  have h1 : M.sweep.step^[1]
      (M.located (.inr (.seek (.peek k q v))) (-((s k).length:ℤ)-2) (M.storage s))=
      M.located (.inr (.read k q v)) (-((s k).length:ℤ)-1) (M.storage s) := by
    change M.sweep.step _=_
    have ht : M.sweep.transition (.inr (.seek (.peek k q v)))
        (M.storage s (-((s k).length:ℤ)-2))=
        (.inr (.read k q v),M.storage s (-((s k).length:ℤ)-2),.right) := by
      simp only [sweep,sweepTransition,purposeStack,M.storage_tracks,M.storageTracks_index,M.stackCell_none]
      rfl
    rw [located,M.sweep.step_keep _ _ _ _ _ ht]
    unfold located
    congr 1
    simp only [Move.displacement]
    omega
  have h2 : M.sweep.step^[1]
      (M.located (.inr (.read k q v)) (-((s k).length:ℤ)-1) (M.storage s))=
      M.located (.inr (.returnPeek k q (Function.update v k (s k).head?)))
        (-((s k).length:ℤ)-1) (M.storage s) := by
    change M.sweep.step _=_
    have ht : M.sweep.transition (.inr (.read k q v))
        (M.storage s (-((s k).length:ℤ)-1))=
        (.inr (.returnPeek k q (Function.update v k (s k).head?)),
          M.storage s (-((s k).length:ℤ)-1),.stay) := by
      simp only [sweep,sweepTransition,M.storage_tracks,M.storage_top]
    rw [located,M.sweep.step_keep _ _ _ _ _ ht]
    simp only [Move.displacement,add_zero,located]
  have h3 := M.return_run (.returnPeek k q (Function.update v k (s k).head?)) s (s k).length
    (by intro z hz; simp [sweep,sweepTransition,M.storage_bottom,show z≠ -1 by omega])
  have h := M.sweep.concat (M.sweep.concat (M.sweep.concat h0 h1) h2) h3
  rw [show (s k).length+1+1+(s k).length=2*(s k).length+2 by omega] at h
  exact h

 theorem partialTops_update (s : Fin M.count → List (Fin M.alphabet)) (k : Fin M.count) :
    Function.update (M.partialTops s k.val) k (s k).head?=M.partialTops s (k.val+1) := by
  funext j
  by_cases h : j=k
  · subst j; simp [partialTops]
  · rw [Function.update_of_ne h]
    unfold partialTops
    have hn : j.val≠k.val := fun he => h (Fin.ext he)
    have he : (j.val<k.val) ↔ (j.val<k.val+1) := by omega
    simp only [he]

 theorem partialTops_all (s : Fin M.count → List (Fin M.alphabet)) :
    M.partialTops s M.count=M.topTuple s := by
  funext k
  exact ite_eq_left k.isLt

 theorem finish_next (k : Fin M.count) (q : Fin M.states) (v : M.Tops)
    (s : Fin M.count → List (Fin M.alphabet)) (hk : k.val+1<M.count) :
    M.sweep.step^[1] (M.located (.inr (.returnPeek k q v)) (-1) (M.storage s))=
      M.located (.inr (.seek (.peek ⟨k.val+1,hk⟩ q v))) (-2) (M.storage s) := by
  change M.sweep.step _=_
  have ht : M.sweep.transition (.inr (.returnPeek k q v)) (M.storage s (-1))=
      (.inr (.seek (.peek ⟨k.val+1,hk⟩ q v)),M.storage s (-1),.left) := by
    simp only [sweep,sweepTransition,M.storage_bottom,decide_true,ite_true,finishPeek,dite_eq_left hk]
  rw [located,M.sweep.step_keep _ _ _ _ _ ht]
  rfl

 theorem finish_last (k : Fin M.count) (q : Fin M.states) (v : M.Tops)
    (s : Fin M.count → List (Fin M.alphabet)) (hk : ¬k.val+1<M.count) :
    M.sweep.step^[1] (M.located (.inr (.returnPeek k q v)) (-1) (M.storage s))=
      M.dispatchLocation (M.transition q v) s := by
  change M.sweep.step _=_
  have ht : M.sweep.transition (.inr (.returnPeek k q v)) (M.storage s (-1))=
      M.dispatch (M.transition q v) (M.storage s (-1)) := by
    simp only [sweep,sweepTransition,M.storage_bottom,decide_true,ite_true,finishPeek,dite_eq_right hk]
  rw [located,M.sweep.step_live _ _ _ _ _ _ ht]
  cases M.transition q v <;> simp only [Function.update_eq_self] <;> rfl

 theorem scan_prefix (s : Fin M.count → List (Fin M.alphabet)) (q : Fin M.states)
    (L : ℕ) (hL : ∀ k,(s k).length ≤ L) (i : ℕ) (hi : i<M.count) :
    ∃ t ≤ i*(2*L+3), M.sweep.step^[t]
      (M.located (.inr (.seek (.peek ⟨0,M.count_pos⟩ q (fun _ => none)))) (-2) (M.storage s))=
      M.located (.inr (.seek (.peek ⟨i,hi⟩ q (M.partialTops s i)))) (-2) (M.storage s) := by
  induction i with
  | zero =>
    refine ⟨0,by omega,?_⟩
    have hh : M.partialTops s 0=(fun _ => none) := by
      funext k; exact ite_eq_right (Nat.not_lt_zero _)
    rw [hh]
    rfl
  | succ i ih =>
    have hii : i<M.count := by omega
    obtain ⟨t,ht,hp⟩ := ih hii
    let k : Fin M.count := ⟨i,hii⟩
    have h1 := M.peek_run k q (M.partialTops s i) s
    rw [show i=k.val from rfl,M.partialTops_update] at h1
    have h2 := M.finish_next k q (M.partialTops s (i+1)) s hi
    refine ⟨t+(2*(s k).length+2)+1,?_,M.sweep.concat (M.sweep.concat hp h1) h2⟩
    have := hL k
    nlinarith

 theorem collect_run (s : Fin M.count → List (Fin M.alphabet)) (q : Fin M.states)
    (L : ℕ) (hL : ∀ k,(s k).length ≤ L) :
    ∃ t ≤ 1+M.count*(2*L+3),M.sweep.step^[t]
      (M.located (.inr (.start q)) (-1) (M.storage s))=
      M.dispatchLocation (M.transition q (M.topTuple s)) s := by
  have hi : M.count-1<M.count := by have := M.count_pos; omega
  let k : Fin M.count := ⟨M.count-1,hi⟩
  have he : k.val+1=M.count := by have := M.count_pos; dsimp [k]; omega
  obtain ⟨t,ht,hp⟩ := M.scan_prefix s q L hL (M.count-1) hi
  have h0 : M.sweep.step^[1] (M.located (.inr (.start q)) (-1) (M.storage s))=
      M.located (.inr (.seek (.peek ⟨0,M.count_pos⟩ q (fun _ => none)))) (-2) (M.storage s) := by
    change M.sweep.step _=_
    rw [located,M.sweep.step_keep _ _ _ _ _ (by rfl)]
    rfl
  have h1 := M.peek_run k q (M.partialTops s k.val) s
  rw [M.partialTops_update,he,M.partialTops_all] at h1
  have h2 := M.finish_last k q (M.topTuple s) s (by omega)
  refine ⟨1+t+(2*(s k).length+2)+1,?_,
    M.sweep.concat (M.sweep.concat (M.sweep.concat h0 hp) h1) h2⟩
  have hlen := hL k
  have hkval : M.count-1+1=M.count := he
  nlinarith

 theorem ret_run (s : Fin M.count → List (Fin M.alphabet)) (q : Fin M.states) (n : ℕ) :
    M.sweep.step^[n+1] (M.located (.inr (.ret q)) (-(n:ℤ)-1) (M.storage s))=
      M.located (.inr (.start q)) (-1) (M.storage s) := by
  have h0 := M.return_run (.ret q) s n
    (by intro z hz; simp [sweep,sweepTransition,M.storage_bottom,show z≠ -1 by omega])
  have h1 : M.sweep.step^[1] (M.located (.inr (.ret q)) (-1) (M.storage s))=
      M.located (.inr (.start q)) (-1) (M.storage s) := by
    change M.sweep.step _=_
    have ht : M.sweep.transition (.inr (.ret q)) (M.storage s (-1))=
        (.inr (.start q),M.storage s (-1),.stay) := by
      simp only [sweep,sweepTransition,M.storage_bottom,decide_true,ite_true]
    rw [located,M.sweep.step_keep _ _ _ _ _ ht]
    rfl
  exact M.sweep.concat h0 h1

 theorem push_run (s : Fin M.count → List (Fin M.alphabet)) (k : Fin M.count)
    (x : Fin M.alphabet) (q : Fin M.states) :
    M.sweep.step^[2*(s k).length+2]
      (M.located (.inr (.seek (.push k x q))) (-2) (M.storage s))=
      M.located (.inr (.start q)) (-1) (M.storage (Function.update s k (x::s k))) := by
  have h0 := M.seek_run (.push k x q) s
  simp only [purposeStack] at h0
  have h1 : M.sweep.step^[1]
      (M.located (.inr (.seek (.push k x q))) (-((s k).length:ℤ)-2) (M.storage s))=
      M.located (.inr (.ret q)) (-((s k).length:ℤ)-1)
        (M.storage (Function.update s k (x::s k))) := by
    change M.sweep.step _=_
    have ht : M.sweep.transition (.inr (.seek (.push k x q)))
        (M.storage s (-((s k).length:ℤ)-2))=
        (.inr (.ret q),M.trackSymbol false
          (Function.update (M.storageTracks s (-((s k).length:ℤ)-2)) k (some x)),.right) := by
      have hz : -((s k).length:ℤ)-2≠ -1 := by omega
      simp only [sweep,sweepTransition,purposeStack,M.storage_tracks,M.storageTracks_index,
        M.stackCell_none,Option.isSome_none,Bool.false_eq_true,ite_false,M.storage_bottom,
        decide_eq_false_iff_not.mpr hz]
    rw [located,M.sweep.step_live _ _ _ _ _ _ ht,← M.storage_push]
    unfold located
    congr 1
    simp only [Move.displacement]
    omega
  have h2 := M.ret_run (Function.update s k (x::s k)) q (s k).length
  have h := M.sweep.concat (M.sweep.concat h0 h1) h2
  rw [show (s k).length+1+((s k).length+1)=2*(s k).length+2 by omega] at h
  exact h

 theorem pop_run (s : Fin M.count → List (Fin M.alphabet)) (k : Fin M.count)
    (q : Fin M.states) :
    M.sweep.step^[2*(s k).length+2]
      (M.located (.inr (.seek (.pop k q))) (-2) (M.storage s))=
      M.located (.inr (.start q)) (-1) (M.storage (Function.update s k (s k).tail)) := by
  have h0 := M.seek_run (.pop k q) s
  simp only [purposeStack] at h0
  have h1 : M.sweep.step^[1]
      (M.located (.inr (.seek (.pop k q))) (-((s k).length:ℤ)-2) (M.storage s))=
      M.located (.inr (.erase k q)) (-((s k).length:ℤ)-1) (M.storage s) := by
    change M.sweep.step _=_
    have ht : M.sweep.transition (.inr (.seek (.pop k q)))
        (M.storage s (-((s k).length:ℤ)-2))=
        (.inr (.erase k q),M.storage s (-((s k).length:ℤ)-2),.right) := by
      simp only [sweep,sweepTransition,purposeStack,M.storage_tracks,M.storageTracks_index,M.stackCell_none]
      rfl
    rw [located,M.sweep.step_keep _ _ _ _ _ ht]
    unfold located
    congr 1
    simp only [Move.displacement]
    omega
  by_cases hk : (s k).length=0
  · have hs : s k=[] := List.eq_nil_of_length_eq_zero hk
    have hu : Function.update s k (s k).tail=s := by rw [hs,List.tail_nil,← hs,Function.update_eq_self]
    have h2 : M.sweep.step^[1] (M.located (.inr (.erase k q)) (-1) (M.storage s))=
        M.located (.inr (.start q)) (-1) (M.storage s) := by
      change M.sweep.step _=_
      have ht : M.sweep.transition (.inr (.erase k q)) (M.storage s (-1))=
          (.inr (.start q),M.storage s (-1),.stay) := by
        simp only [sweep,sweepTransition,M.storage_bottom,decide_true,ite_true]
      rw [located,M.sweep.step_keep _ _ _ _ _ ht]
      rfl
    simp only [hk,Nat.cast_zero,neg_zero,zero_sub] at h1
    rw [hk,hu]
    simpa only [zero_mul,zero_add] using M.sweep.concat h1 h2
  · have hpos : 0<(s k).length := by omega
    have h2 : M.sweep.step^[1]
        (M.located (.inr (.erase k q)) (-((s k).length:ℤ)-1) (M.storage s))=
        M.located (.inr (.ret q)) (-(((s k).length-1:ℕ):ℤ)-1)
          (M.storage (Function.update s k (s k).tail)) := by
      change M.sweep.step _=_
      have ht : M.sweep.transition (.inr (.erase k q))
          (M.storage s (-((s k).length:ℤ)-1))=
          (.inr (.ret q),M.trackSymbol false
            (Function.update (M.storageTracks s (-((s k).length:ℤ)-1)) k none),.right) := by
        have hz : -((s k).length:ℤ)-1≠ -1 := by omega
        simp only [sweep,sweepTransition,M.storage_tracks,M.storage_bottom,
          decide_eq_false_iff_not.mpr hz,Bool.false_eq_true,ite_false]
      rw [located,M.sweep.step_live _ _ _ _ _ _ ht,← M.storage_pop s k hpos]
      unfold located
      congr 1
      simp only [Move.displacement]
      omega
    have h3 := M.ret_run (Function.update s k (s k).tail) q ((s k).length-1)
    have h := M.sweep.concat (M.sweep.concat (M.sweep.concat h0 h1) h2) h3
    rw [show (s k).length+1+1+((s k).length-1+1)=2*(s k).length+2 by omega] at h
    exact h

 theorem dispatch_run (s : Fin M.count → List (Fin M.alphabet)) (q : Fin M.states)
    (a : Command M.count M.alphabet M.states) (L : ℕ) (hL : ∀ k,(s k).length ≤ L) :
    ∃ t ≤ 2*L+3,M.sweep.step^[t] (M.dispatchLocation a s)=
      M.sweepEmbed (M.perform ⟨.inr q,s⟩ a) := by
  cases a with
  | next q' => exact ⟨0,by omega,rfl⟩
  | halt b => exact ⟨0,by omega,rfl⟩
  | push k x q' => exact ⟨2*(s k).length+2,by have := hL k; omega,M.push_run s k x q'⟩
  | pop k q' => exact ⟨2*(s k).length+2,by have := hL k; omega,M.pop_run s k q'⟩

 theorem sweep_simulate_step (C : M.Config) (L : ℕ) (hL : ∀ k,(C.stack k).length ≤ L) :
    ∃ t ≤ 4*(M.count+1)*(L+1),M.sweep.step^[t] (M.sweepEmbed C)=M.sweepEmbed (M.step C) := by
  obtain ⟨p,s⟩ := C
  cases p with
  | inl b => exact ⟨0,by positivity,rfl⟩
  | inr q =>
    obtain ⟨t,ht,hc⟩ := M.collect_run s q L hL
    obtain ⟨u,hu,ha⟩ := M.dispatch_run s q (M.transition q (M.topTuple s)) L hL
    refine ⟨t+u,?_,M.sweep.concat hc ha⟩
    nlinarith

end Machine
end WLTime.StackMachine

end OAI
end

section
-- module Solutions.OAIQW_WLTime.TapeCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLTime.StackMachine
namespace Machine
variable (M : Machine)

 theorem rawTape_nil (z : ℤ) : M.rawTape [] z=.inl 0 := by
  simp [rawTape,TypedTape.Machine.initial]
 theorem rawTape_bit (w : List Bool) (i : ℕ) (hi : i<w.length) :
    M.rawTape w i=.inl (if w[i] then 2 else 1) := by
  simp only [rawTape,TypedTape.Machine.initial,Nat.cast_nonneg,Int.toNat_natCast,hi,and_self,ite_true]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]
 theorem rawTape_beyond (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    M.rawTape w i=.inl 0 := by
  simp only [rawTape,TypedTape.Machine.initial,Nat.cast_nonneg,Int.toNat_natCast,true_and,
    ite_eq_right (by omega : ¬i<w.length)]
 theorem mixed_nonneg (u v : List Bool) (z : ℤ) (hz : 0 ≤ z) :
    M.mixed u v z=M.rawTape u z := ite_eq_left hz
 theorem mixed_neg (u v : List Bool) (z : ℤ) (hz : z<0) :
    M.mixed u v z=M.storage (M.inputStacks v) z := ite_eq_right (by omega)
 theorem mixed_bottom (u v : List Bool) (z : ℤ) :
    M.symbolBottom (M.mixed u v z)=decide (z= -1) := by
  by_cases hz : 0 ≤ z
  · rw [M.mixed_nonneg u v z hz]
    have hh : z≠ -1 := by omega
    simp only [rawTape,TypedTape.Machine.initial,decide_eq_false_iff_not.mpr hh]
    split_ifs <;> rfl
  · rw [M.mixed_neg u v z (by omega),M.storage_bottom]
 theorem inputStacks_zero (v : List Bool) :
    M.inputStacks v ⟨0,M.count_pos⟩=v.map M.inputLetter := by
  simp [inputStacks,initialConfig]
 theorem inputStacks_cons (b : Bool) (v : List Bool) :
    M.inputStacks (b::v)=Function.update (M.inputStacks v) ⟨0,M.count_pos⟩
      (M.inputLetter b::M.inputStacks v ⟨0,M.count_pos⟩) := by
  funext k
  by_cases hk : k=⟨0,M.count_pos⟩
  · subst k; simp only [Function.update_self,M.inputStacks_zero,List.map_cons]
  · have hn : k.val≠0 := fun he => hk (Fin.ext he)
    simp only [Function.update_of_ne hk,inputStacks,initialConfig,hn,ite_false]
 theorem storage_nonneg (s : Fin M.count → List (Fin M.alphabet)) (z : ℤ) (hz : 0 ≤ z) :
    M.storage s z=.inl 0 := by
  have h0 : z≠ -1 := by omega
  have h1 : ¬z< -1 := by omega
  simp only [storage,decide_eq_false_iff_not.mpr h0,storageTracks,ite_eq_right h1,trackSymbol,and_self,ite_true]
 theorem mixed_nil (v : List Bool) : M.mixed [] v=M.storage (M.inputStacks v) := by
  funext z
  by_cases hz : 0 ≤ z
  · rw [M.mixed_nonneg [] v z hz,M.rawTape_nil,M.storage_nonneg _ z hz]
  · exact M.mixed_neg [] v z (by omega)
 theorem rawTape_erase (u : List Bool) (b : Bool) :
    M.rawTape u=Function.update (M.rawTape (u++[b])) (u.length:ℤ) (.inl 0) := by
  funext z
  by_cases he : z=(u.length:ℤ)
  · subst z; rw [Function.update_self,M.rawTape_beyond u u.length (by omega)]
  · rw [Function.update_of_ne he]
    by_cases hz : 0 ≤ z
    · have hzz : z=(z.toNat:ℤ) := by omega
      rw [hzz]
      by_cases hi : z.toNat<u.length
      · rw [M.rawTape_bit u _ hi,M.rawTape_bit (u++[b]) _ (by simp; omega)]
        simp only [List.getElem_append_left hi]
      · rw [M.rawTape_beyond u _ (by omega),M.rawTape_beyond (u++[b]) _ (by simp; omega)]
    · simp only [rawTape,TypedTape.Machine.initial,hz,false_and,ite_false]
 theorem mixed_erase (u v : List Bool) (b : Bool) :
    M.mixed u v=Function.update (M.mixed (u++[b]) v) (u.length:ℤ) (.inl 0) := by
  funext z
  by_cases hz : 0 ≤ z
  · rw [M.mixed_nonneg u v z hz,M.rawTape_erase u b]
    by_cases he : z=(u.length:ℤ)
    · simp only [he,Function.update_self]
    · rw [Function.update_of_ne he,Function.update_of_ne he,M.mixed_nonneg _ _ z hz]
  · have he : z≠(u.length:ℤ) := by omega
    rw [Function.update_of_ne he,M.mixed_neg _ _ z (by omega),M.mixed_neg _ _ z (by omega)]
 theorem mixed_push (u v : List Bool) (b : Bool) :
    M.mixed u (b::v)=Function.update (M.mixed u v) (-(v.length:ℤ)-2)
      (M.trackSymbol false (Function.update (M.symbolTracks (M.mixed u v (-(v.length:ℤ)-2)))
        ⟨0,M.count_pos⟩ (some (M.inputLetter b)))) := by
  have hv : (M.inputStacks v ⟨0,M.count_pos⟩).length=v.length := by
    rw [M.inputStacks_zero,List.length_map]
  rw [M.mixed_neg u v _ (by omega),M.storage_tracks]
  have hh := M.storage_push (M.inputStacks v) ⟨0,M.count_pos⟩ (M.inputLetter b)
  rw [hv,← M.inputStacks_cons] at hh
  funext z
  by_cases hz : 0 ≤ z
  · rw [M.mixed_nonneg u (b::v) z hz,Function.update_of_ne (by omega),M.mixed_nonneg u v z hz]
  · rw [M.mixed_neg u (b::v) z (by omega),hh]
    by_cases he : z= -(v.length:ℤ)-2
    · simp only [he,Function.update_self]
    · rw [Function.update_of_ne he,Function.update_of_ne he,M.mixed_neg u v z (by omega)]

 theorem seekEnd_run (u v : List Bool) :
    M.sweep.step^[u.length] (M.located (.inr .seekEnd) 0 (M.mixed u v))=
      M.located (.inr .seekEnd) (u.length:ℤ) (M.mixed u v) := by
  apply M.sweep.path_iterate (fun i => M.located (.inr .seekEnd) (i:ℤ) (M.mixed u v))
  intro i hi
  have ht : M.sweep.transition (.inr .seekEnd) (M.mixed u v (i:ℤ))=
      (.inr .seekEnd,M.mixed u v (i:ℤ),.right) := by
    rw [M.mixed_nonneg u v _ (by omega),M.rawTape_bit u i hi]
    cases u[i] <;> simp [sweep,sweepTransition]
  rw [located,M.sweep.step_keep _ _ _ _ _ ht]
  simp [located,Move.displacement]

 theorem reverse_path (p : M.Control) (tape : ℤ → M.TapeSymbol) (n : ℕ)
    (h : ∀ i<n,M.sweep.transition (.inr p) (tape (i:ℤ))=(.inr p,tape (i:ℤ),.left)) :
    M.sweep.step^[n] (M.located (.inr p) ((n:ℤ)-1) tape)=M.located (.inr p) (-1) tape := by
  have he : (-1:ℤ)=(n:ℤ)-(n:ℤ)-1 := by omega
  rw [he]
  apply M.sweep.path_iterate (fun i => M.located (.inr p) ((n:ℤ)-(i:ℤ)-1) tape)
  intro i hi
  have hz : (n:ℤ)-(i:ℤ)-1= ((n-i-1:ℕ):ℤ) := by omega
  have ht := h (n-i-1) (by omega)
  rw [← hz] at ht
  rw [located,M.sweep.step_keep _ _ _ _ _ ht]
  unfold located
  congr 1
  simp only [Move.displacement,Nat.cast_add,Nat.cast_one]
  omega

 theorem mixed_return (p : M.Control) (u v : List Bool) (n : ℕ)
    (h : ∀ z< -1,M.sweep.transition (.inr p) (M.mixed u v z)=
      (.inr p,M.mixed u v z,.right)) :
    M.sweep.step^[n] (M.located (.inr p) (-(n:ℤ)-1) (M.mixed u v))=
      M.located (.inr p) (-1) (M.mixed u v) := by
  have he : (-1:ℤ)=(n:ℤ)-(n:ℤ)-1 := by omega
  rw [he]
  rw [show -(n:ℤ)-1=(0:ℤ)-(n:ℤ)-1 by omega]
  apply M.sweep.path_iterate (fun i => M.located (.inr p) ((i:ℤ)-(n:ℤ)-1) (M.mixed u v))
  intro i hi
  rw [located,M.sweep.step_keep _ _ _ _ _ (h _ (by omega))]
  unfold located
  congr 1
  simp only [Move.displacement,Nat.cast_add,Nat.cast_one]
  omega

 theorem append_run (u v : List Bool) (b : Bool) :
    M.sweep.step^[v.length] (M.located (.inr (.append (M.inputLetter b))) (-2) (M.mixed u v))=
      M.located (.inr (.append (M.inputLetter b))) (-(v.length:ℤ)-2) (M.mixed u v) := by
  apply M.sweep.path_iterate (fun i =>
    M.located (.inr (.append (M.inputLetter b))) (-(i:ℤ)-2) (M.mixed u v))
  intro i hi
  have ht : M.sweep.transition (.inr (.append (M.inputLetter b))) (M.mixed u v (-(i:ℤ)-2))=
      (.inr (.append (M.inputLetter b)),M.mixed u v (-(i:ℤ)-2),.left) := by
    rw [M.mixed_neg u v _ (by omega)]
    simp only [sweep,sweepTransition,M.storage_tracks,M.storageTracks_index,M.inputStacks_zero]
    rw [M.stackCell_some _ i (by simpa using hi)]
    rfl
  rw [located,M.sweep.step_keep _ _ _ _ _ ht]
  unfold located
  congr 1
  simp only [Move.displacement,Nat.cast_add,Nat.cast_one]
  omega

 theorem seekEnd_finish (u v : List Bool) :
    M.sweep.step^[u.length+1] (M.located (.inr .seekEnd) 0 (M.mixed u v))=
      M.located (.inr .take) ((u.length:ℤ)-1) (M.mixed u v) := by
  have h1 : M.sweep.step^[1] (M.located (.inr .seekEnd) (u.length:ℤ) (M.mixed u v))=
      M.located (.inr .take) ((u.length:ℤ)-1) (M.mixed u v) := by
    change M.sweep.step _=_
    have ht : M.sweep.transition (.inr .seekEnd) (M.mixed u v (u.length:ℤ))=
        (.inr .take,M.mixed u v (u.length:ℤ),.left) := by
      rw [M.mixed_nonneg u v _ (by omega),M.rawTape_beyond u u.length (by omega)]
      simp [sweep,sweepTransition]
    rw [located,M.sweep.step_keep _ _ _ _ _ ht]
    rfl
  exact M.sweep.concat (M.seekEnd_run u v) h1

 theorem take_run (u v : List Bool) (b : Bool) :
    M.sweep.step^[1] (M.located (.inr .take) (u.length:ℤ) (M.mixed (u++[b]) v))=
      M.located (.inr (.bring (M.inputLetter b))) ((u.length:ℤ)-1) (M.mixed u v) := by
  change M.sweep.step _=_
  have ht : M.sweep.transition (.inr .take) (M.mixed (u++[b]) v (u.length:ℤ))=
      (.inr (.bring (M.inputLetter b)),.inl 0,.left) := by
    have hb : M.mixed (u++[b]) v (u.length:ℤ)=.inl (if b then 2 else 1) := by
      rw [M.mixed_nonneg _ _ _ (by omega),M.rawTape_bit _ _ (by simp)]
      simp only [List.getElem_append_right (by omega : u.length ≤ u.length),Nat.sub_self,List.getElem_cons_zero]
    rw [hb]
    cases b <;> simp [sweep,sweepTransition,symbolBottom,inputLetter]
  rw [located,M.sweep.step_live _ _ _ _ _ _ ht,← M.mixed_erase]
  rfl

 theorem bring_run (u v : List Bool) (b : Bool) :
    M.sweep.step^[u.length+1]
      (M.located (.inr (.bring (M.inputLetter b))) ((u.length:ℤ)-1) (M.mixed u v))=
      M.located (.inr (.append (M.inputLetter b))) (-2) (M.mixed u v) := by
  have h0 := M.reverse_path (.bring (M.inputLetter b)) (M.mixed u v) u.length (by
    intro i hi
    have hz : (i:ℤ)≠ -1 := by omega
    simp only [sweep,sweepTransition,M.mixed_bottom,decide_eq_false_iff_not.mpr hz,
      Bool.false_eq_true,ite_false])
  have h1 : M.sweep.step^[1]
      (M.located (.inr (.bring (M.inputLetter b))) (-1) (M.mixed u v))=
      M.located (.inr (.append (M.inputLetter b))) (-2) (M.mixed u v) := by
    change M.sweep.step _=_
    have ht : M.sweep.transition (.inr (.bring (M.inputLetter b))) (M.mixed u v (-1))=
        (.inr (.append (M.inputLetter b)),M.mixed u v (-1),.left) := by
      simp only [sweep,sweepTransition,M.mixed_bottom,decide_true,ite_true]
    rw [located,M.sweep.step_keep _ _ _ _ _ ht]
    rfl
  exact M.sweep.concat h0 h1

 theorem append_finish (u v : List Bool) (b : Bool) :
    M.sweep.step^[v.length+1]
      (M.located (.inr (.append (M.inputLetter b))) (-2) (M.mixed u v))=
      M.located (.inr .back) (-(v.length:ℤ)-1) (M.mixed u (b::v)) := by
  have h1 : M.sweep.step^[1]
      (M.located (.inr (.append (M.inputLetter b))) (-(v.length:ℤ)-2) (M.mixed u v))=
      M.located (.inr .back) (-(v.length:ℤ)-1) (M.mixed u (b::v)) := by
    change M.sweep.step _=_
    have hz : -(v.length:ℤ)-2≠ -1 := by omega
    have ht : M.sweep.transition (.inr (.append (M.inputLetter b))) (M.mixed u v (-(v.length:ℤ)-2))=
        (.inr .back,M.trackSymbol false
          (Function.update (M.symbolTracks (M.mixed u v (-(v.length:ℤ)-2)))
            ⟨0,M.count_pos⟩ (some (M.inputLetter b))),.right) := by
      have hv : M.symbolTracks (M.mixed u v (-(v.length:ℤ)-2)) ⟨0,M.count_pos⟩=none := by
        rw [M.mixed_neg u v _ (by omega),M.storage_tracks,M.storageTracks_index]
        change M.stackCell (M.inputStacks v ⟨0,M.count_pos⟩) v.length=none
        rw [M.inputStacks_zero,← List.length_map (f:=M.inputLetter) (as:=v),M.stackCell_none]
      simp only [sweep,sweepTransition,hv,Option.isSome_none,Bool.false_eq_true,ite_false,
        M.mixed_bottom,decide_eq_false_iff_not.mpr hz]
    rw [located,M.sweep.step_live _ _ _ _ _ _ ht,← M.mixed_push]
    unfold located
    congr 1
    simp only [Move.displacement]
    omega
  exact M.sweep.concat (M.append_run u v b) h1

 theorem back_run (u v : List Bool) (n : ℕ) :
    M.sweep.step^[n+1] (M.located (.inr .back) (-(n:ℤ)-1) (M.mixed u v))=
      M.located (.inr .seekEnd) 0 (M.mixed u v) := by
  have h0 := M.mixed_return .back u v n (by
    intro z hz
    simp only [sweep,sweepTransition,M.mixed_bottom,
      decide_eq_false_iff_not.mpr (by omega : z≠ -1),Bool.false_eq_true,ite_false])
  have h1 : M.sweep.step^[1] (M.located (.inr .back) (-1) (M.mixed u v))=
      M.located (.inr .seekEnd) 0 (M.mixed u v) := by
    change M.sweep.step _=_
    have ht : M.sweep.transition (.inr .back) (M.mixed u v (-1))=
        (.inr .seekEnd,M.mixed u v (-1),.right) := by
      simp only [sweep,sweepTransition,M.mixed_bottom,decide_true,ite_true]
    rw [located,M.sweep.step_keep _ _ _ _ _ ht]
    rfl
  exact M.sweep.concat h0 h1

 theorem init_cycle (u v : List Bool) (b : Bool) :
    M.sweep.step^[2*(u.length+v.length)+6]
      (M.located (.inr .seekEnd) 0 (M.mixed (u++[b]) v))=
      M.located (.inr .seekEnd) 0 (M.mixed u (b::v)) := by
  have h0 := M.seekEnd_finish (u++[b]) v
  have he : (((u++[b]).length:ℤ)-1)=(u.length:ℤ) := by simp
  rw [he] at h0
  have h := M.sweep.concat (M.sweep.concat (M.sweep.concat (M.sweep.concat h0
    (M.take_run u v b)) (M.bring_run u v b)) (M.append_finish u v b)) (M.back_run u (b::v) v.length)
  have hn : (u++[b]).length+1+1+(u.length+1)+(v.length+1)+(v.length+1)=
      2*(u.length+v.length)+6 := by simp only [List.length_append,List.length_singleton]; omega
  rw [hn] at h
  exact h

 theorem init_empty (v : List Bool) :
    M.sweep.step^[2] (M.located (.inr .seekEnd) 0 (M.mixed [] v))=
      M.sweepEmbed (M.initialConfig v) := by
  have h0 := M.seekEnd_finish [] v
  have h1 : M.sweep.step^[1] (M.located (.inr .take) (-1) (M.mixed [] v))=
      M.sweepEmbed (M.initialConfig v) := by
    change M.sweep.step _=_
    have ht : M.sweep.transition (.inr .take) (M.mixed [] v (-1))=
        (.inr (.start M.initial),M.mixed [] v (-1),.stay) := by
      simp only [sweep,sweepTransition,M.mixed_bottom,decide_true,ite_true]
    rw [located,M.sweep.step_keep _ _ _ _ _ ht,M.mixed_nil]
    rfl
  exact M.sweep.concat h0 h1

 theorem init_process (u v : List Bool) :
    M.sweep.step^[u.length*(2*(u.length+v.length)+4)+2]
      (M.located (.inr .seekEnd) 0 (M.mixed u v))=M.sweepEmbed (M.initialConfig (u++v)) := by
  induction u using List.reverseRecOn generalizing v with
  | nil => simpa only [List.length_nil,zero_mul,zero_add,List.nil_append] using M.init_empty v
  | append_singleton u b ih =>
    have h0 := M.init_cycle u v b
    have h1 := ih (b::v)
    have h := M.sweep.concat h0 h1
    have he : 2*(u.length+v.length)+6+(u.length*(2*(u.length+(b::v).length)+4)+2)=
        (u++[b]).length*(2*((u++[b]).length+v.length)+4)+2 := by
      simp only [List.length_cons,List.length_append,List.length_nil]
      ring
    rw [he] at h
    simpa only [List.append_assoc,List.singleton_append] using h

end Machine
end WLTime.StackMachine

namespace WLTime.StackMachine
namespace Machine
variable (M : Machine)

 theorem storage_empty (z : ℤ) : M.storage (M.inputStacks []) z =
    if z= -1 then M.trackSymbol true (fun _ => none) else .inl 0 := by
  have hs : M.storageTracks (M.inputStacks []) z=(fun _ => none) := by
    unfold storageTracks
    split_ifs
    · funext k
      simp [stackCell,inputStacks,initialConfig]
    · rfl
  simp only [storage,hs]
  by_cases hz : z= -1
  · simp only [hz,decide_true,ite_true]
  · simp only [decide_eq_false_iff_not.mpr hz,ite_eq_right hz,trackSymbol,and_self,ite_true]

 theorem mixed_initial (w : List Bool) :
    M.mixed w []=Function.update (M.rawTape w) (-1) (M.trackSymbol true (fun _ => none)) := by
  funext z
  by_cases he : z= -1
  · subst z
    rw [Function.update_self,M.mixed_neg _ _ _ (by omega),M.storage_origin]
  · rw [Function.update_of_ne he]
    by_cases hz : 0 ≤ z
    · exact M.mixed_nonneg w [] z hz
    · rw [M.mixed_neg _ _ z (by omega),M.storage_empty,ite_eq_right he]
      simp only [rawTape,TypedTape.Machine.initial,hz,false_and,ite_false]

 theorem init_mark (w : List Bool) :
    M.sweep.run w 2=M.located (.inr .seekEnd) 0 (M.mixed w []) := by
  have h0 : M.sweep.step (M.sweep.initial w)=M.located (.inr .mark) (-1) (M.rawTape w) := by
    have hh : ¬M.sweep.halted (.inl 0) := by simp [TypedTape.Machine.halted]
    have ha : M.sweep.action (.inl 0) (M.rawTape w 0)=
        (.inr .mark,M.rawTape w 0,.left) := by
      rw [TypedTape.Machine.action,ite_eq_right hh]
      rfl
    change M.sweep.step ⟨.inl 0,0,M.rawTape w⟩=_
    simp only [TypedTape.Machine.step,ha,Function.update_eq_self]
    rfl
  change M.sweep.step (M.sweep.step (M.sweep.initial w))=_
  rw [h0,located,M.sweep.step_live _ _ _ _ _ _ (by rfl),← M.mixed_initial]
  rfl

 theorem sweep_initial (w : List Bool) :
    ∃ t ≤ 4*(w.length+1)^2,M.sweep.run w t=M.sweepEmbed (M.initialConfig w) := by
  have h := M.sweep.concat (M.init_mark w) (M.init_process w [])
  simp only [List.length_nil,Nat.add_zero,List.append_nil] at h
  refine ⟨2+(w.length*(2*w.length+4)+2),by nlinarith,h⟩

 theorem step_length (C : M.Config) (L : ℕ) (hL : ∀ k,(C.stack k).length ≤ L) :
    ∀ k,((M.step C).stack k).length ≤ L+1 := by
  intro k
  obtain ⟨p,s⟩ := C
  dsimp only at hL
  cases p with
  | inl b => exact (hL k).trans (by omega)
  | inr q =>
    simp only [step]
    cases M.transition q (fun k => (s k).head?) with
    | next q' => exact (hL k).trans (by omega)
    | halt b => exact (hL k).trans (by omega)
    | push j x q' =>
      simp only [perform,Function.update_apply]
      split_ifs with hj
      · subst k; simp only [List.length_cons]; exact Nat.add_le_add_right (hL j) 1
      · exact (hL k).trans (by omega)
    | pop j q' =>
      simp only [perform,Function.update_apply]
      split_ifs with hj
      · subst k; simp only [List.length_tail]; have := hL j; omega
      · exact (hL k).trans (by omega)

 theorem iterate_length (C : M.Config) (L : ℕ) (hL : ∀ k,(C.stack k).length ≤ L) (t : ℕ) :
    ∀ k,((M.step^[t] C).stack k).length ≤ L+t := by
  induction t with
  | zero => simpa only [Function.iterate_zero_apply,Nat.add_zero] using hL
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    simpa only [Nat.add_assoc] using M.step_length (M.step^[t] C) (L+t) ih

 theorem sweep_iterate (C : M.Config) (L : ℕ) (hL : ∀ k,(C.stack k).length ≤ L) (t : ℕ) :
    ∃ u ≤ 4*(M.count+1)*t*(L+t+1),
      M.sweep.step^[u] (M.sweepEmbed C)=M.sweepEmbed (M.step^[t] C) := by
  induction t with
  | zero => exact ⟨0,by omega,rfl⟩
  | succ t ih =>
    obtain ⟨u,hu,he⟩ := ih
    obtain ⟨v,hv,hf⟩ := M.sweep_simulate_step (M.step^[t] C) (L+t) (M.iterate_length C L hL t)
    refine ⟨u+v,?_,?_⟩
    · nlinarith
    · rw [Nat.add_comm,Function.iterate_add_apply,he,hf,Function.iterate_succ_apply']

 theorem sweep_run (w : List Bool) (t : ℕ) :
    ∃ u ≤ 8*(M.count+1)*(w.length+t+1)^2,
      M.sweep.run w u=M.sweepEmbed (M.run w t) := by
  obtain ⟨a,ha,he⟩ := M.sweep_initial w
  have hL : ∀ k,((M.initialConfig w).stack k).length ≤ w.length := by
    intro k; simp only [initialConfig]; split_ifs <;> simp
  obtain ⟨b,hb,hf⟩ := M.sweep_iterate (M.initialConfig w) w.length hL t
  refine ⟨a+b,?_,M.sweep.concat he hf⟩
  have hh : (w.length+1)^2 ≤ (w.length+t+1)^2 := by nlinarith
  have htt : t ≤ w.length+t+1 := by omega
  have hmul := Nat.mul_le_mul_right (w.length+t+1) htt
  have hprod := Nat.mul_le_mul_left (4*(M.count+1)) hmul
  nlinarith

 theorem oneTape_simulate (w : List Bool) (t : ℕ) :
    ∃ u ≤ 8*(M.count+1)*(w.length+t+1)^2,M.oneTape.run OneTape.lineShift (M.oneTape.initial w) u=
      M.sweep.embed (M.sweepEmbed (M.run w t)) := by
  obtain ⟨u,hu,he⟩ := M.sweep_run w t
  refine ⟨u,hu,?_⟩
  rw [← M.sweep.embed_run,he]

 theorem oneTape_correct (w : List Bool) (t : ℕ) (b : Bool)
    (hh : (M.run w t).state=.inl b) :
    M.oneTape.toTM.halts w ∧ M.oneTape.toTM.time w ≤ 8*(M.count+1)*(w.length+t+1)^2 ∧
      (M.oneTape.toTM.accepts w ↔ b=true) := by
  obtain ⟨u,hu,he⟩ := M.oneTape_simulate w t
  have hs : (M.oneTape.toTM.run w u).state.val=if b then 1 else 2 := by
    rw [← M.oneTape.embed_run,he]
    simp only [OneTape.embed,TypedTape.Machine.embed,sweepEmbed,located,hh]
    cases b <;> rfl
  have hx : M.oneTape.toTM.halted (M.oneTape.toTM.run w u) := by
    change (M.oneTape.toTM.run w u).state.val=1 ∨ (M.oneTape.toTM.run w u).state.val=2
    rw [hs]
    cases b <;> simp
  refine ⟨⟨u,hx⟩,(M.oneTape.toTM.time_le_of_halted w hx).trans hu,?_⟩
  rw [M.oneTape.toTM.accepts_iff_at_halt w hx]
  rw [hs]
  cases b <;> simp

end Machine
end WLTime.StackMachine

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Programs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uK uA uS uT

namespace WLTime.TypedStack

namespace Machine
variable {K : Type uK} {A : Type uA} {S : Type uS} [DecidableEq K] (M : Machine K A S)

variable [Fintype K] [Fintype A] [Fintype S]

 theorem project_perform (C : M.compile.Config) (a : Command K A S) :
    M.project (M.compile.perform C (M.encodeCommand a))=M.perform (M.project C) a := by
  cases a with
  | next q => simp only [encodeCommand,StackMachine.Machine.perform,project,Sum.map_inr,
      Equiv.symm_apply_apply,perform]
  | halt b => rfl
  | push k x q =>
    simp only [encodeCommand,StackMachine.Machine.perform,project,Sum.map_inr,
      Equiv.symm_apply_apply,perform]
    congr 1
    funext j
    by_cases hj : j=k
    · subst j
      simp only [Function.update_self,List.map_cons,M.decode_encode]
    · have hn : M.registerEquiv j≠M.registerEquiv k := fun hh => hj (M.registerEquiv.injective hh)
      simp only [Function.update_of_ne hj,Function.update_of_ne hn]
  | pop k q =>
    simp only [encodeCommand,StackMachine.Machine.perform,project,Sum.map_inr,
      Equiv.symm_apply_apply,perform]
    congr 1
    funext j
    by_cases hj : j=k
    · subst j
      simp only [Function.update_self,List.map_tail]
    · have hn : M.registerEquiv j≠M.registerEquiv k := fun hh => hj (M.registerEquiv.injective hh)
      simp only [Function.update_of_ne hj,Function.update_of_ne hn]

 theorem project_step (C : M.compile.Config) : M.project (M.compile.step C)=M.step (M.project C) := by
  obtain ⟨p,s⟩ := C
  cases p with
  | inl b => rfl
  | inr q =>
    change M.project (M.compile.perform _ (M.encodeCommand _))=_
    rw [M.project_perform]
    simp only [step,project,Sum.map_inr,List.head?_map]

 theorem project_initial (w : List Bool) : M.project (M.compile.initialConfig w)=M.initialConfig w := by
  have hi (b : Bool) : M.decodeSymbol (M.compile.inputLetter b)=M.inputLetter b := by
    cases b <;> rfl
  simp only [project,StackMachine.Machine.initialConfig,Sum.map_inr,Equiv.symm_apply_apply,initialConfig]
  congr 1
  funext k
  have hk : (M.registerEquiv k).val=0 ↔ k=M.inputStack := by
    rw [← M.register_input]
    exact Fin.ext_iff.symm.trans (M.registerEquiv.injective.eq_iff)
  simp only [hk]
  split_ifs
  · simp only [List.map_map]
    exact List.map_congr_left (fun b _ => hi b)
  · rfl

 theorem project_run (w : List Bool) (t : ℕ) : M.project (M.compile.run w t)=M.run w t := by
  induction t with
  | zero => exact M.project_initial w
  | succ t ih =>
    simp only [run,StackMachine.Machine.run,Function.iterate_succ_apply'] at *
    rw [M.project_step,ih]

 theorem compile_halt (w : List Bool) (t : ℕ) (b : Bool)
    (h : (M.run w t).state=.inl b) : (M.compile.run w t).state=.inl b := by
  rw [← M.project_run] at h
  cases he : (M.compile.run w t).state with
  | inl b' => simpa only [project,he,Sum.map_inl,id_eq,Sum.inl.injEq] using h
  | inr q => simp only [project,he,Sum.map_inr,reduceCtorEq] at h

 theorem oneTape_correct (w : List Bool) (t : ℕ) (b : Bool)
    (h : (M.run w t).state=.inl b) :
    M.compile.oneTape.toTM.halts w ∧
      M.compile.oneTape.toTM.time w ≤ 8*(Fintype.card K+1)*(w.length+t+1)^2 ∧
      (M.compile.oneTape.toTM.accepts w ↔ b=true) :=
  M.compile.oneTape_correct w t b (M.compile_halt w t b h)

end Machine
end WLTime.TypedStack

namespace WLTime.TypedStack

variable {K : Type uK} {A : Type uA} {S : Type uS} {T : Type uT} [DecidableEq K]

namespace Execution
 theorem iterate (M : Machine K A S) {q s t b out} (h : Execution M.transition q s t b out) :
    M.step^[t] ⟨.inr q,s⟩=⟨.inl b,out⟩ := by
  induction h with
  | @halt q s b h =>
    change M.perform ⟨.inr q,s⟩ (M.transition q (tops s))=⟨.inl b,s⟩
    rw [h]
    rfl
  | @next q s q' t b out h tail ih =>
    rw [Function.iterate_succ_apply]
    change M.step^[t] (M.perform ⟨.inr q,s⟩ (M.transition q (tops s)))=⟨.inl b,out⟩
    rw [h]
    exact ih
  | @push q s k x q' t b out h tail ih =>
    rw [Function.iterate_succ_apply]
    change M.step^[t] (M.perform ⟨.inr q,s⟩ (M.transition q (tops s)))=⟨.inl b,out⟩
    rw [h]
    exact ih
  | @pop q s k q' t b out h tail ih =>
    rw [Function.iterate_succ_apply]
    change M.step^[t] (M.perform ⟨.inr q,s⟩ (M.transition q (tops s)))=⟨.inl b,out⟩
    rw [h]
    exact ih

 theorem rename {tr : S → Tops K A → Command K A S} {tr' : T → Tops K A → Command K A T}
    (f : S → T) (hf : ∀ q v,tr' (f q) v=Command.rename f (tr q v))
    {q s t b out} (h : Execution tr q s t b out) : Execution tr' (f q) s t b out := by
  induction h with
  | halt h => exact .halt (by rw [hf,h]; rfl)
  | next h tail ih => exact .next (by rw [hf,h]; rfl) ih
  | push h tail ih => exact .push (by rw [hf,h]; rfl) ih
  | pop h tail ih => exact .pop (by rw [hf,h]; rfl) ih

 theorem plug {tr : S → Tops K A → Command K A S} {tr' : T → Tops K A → Command K A T}
    (f : S → T) (r : T) (hf : ∀ q v,tr' (f q) v=Command.redirect f r (tr q v))
    {q s t b mid} (h : Execution tr q s t b mid)
    {u c out} (cont : Execution tr' r mid u c out) : Execution tr' (f q) s (t+u) c out := by
  induction h with
  | halt h =>
    simpa only [Nat.add_comm] using Execution.next (by rw [hf,h]; rfl) cont
  | next h tail ih =>
    simpa only [Nat.add_right_comm] using Execution.next (by rw [hf,h]; rfl) (ih cont)
  | push h tail ih =>
    simpa only [Nat.add_right_comm] using Execution.push (by rw [hf,h]; rfl) (ih cont)
  | pop h tail ih =>
    simpa only [Nat.add_right_comm] using Execution.pop (by rw [hf,h]; rfl) (ih cont)
end Execution

namespace Code

 theorem exec_finite {c : Code K A} {s t out} (h : c.Exec s t out) :
    Execution c.transition c.entry s t false out := by
  induction h with
  | skip s => exact .halt rfl
  | push s k x =>
    exact .push (q' := (1 : Fin 2)) (by simp [entry,transition]) (.halt (by simp [transition]))
  | pushDyn s k f =>
    exact .push (q' := (1 : Fin 2)) (by simp [entry,transition]) (.halt (by simp [transition]))
  | pop s k =>
    exact .pop (q' := (1 : Fin 2)) (by simp [entry,transition]) (.halt (by simp [transition]))
  | @seq a b s mid out t u first second ih1 ih2 =>
    exact ih1.plug Sum.inl (.inr b.entry) (fun _ _ => rfl) (ih2.rename Sum.inr (fun _ _ => rfl))
  | branch_true hp body ih =>
    exact .next (by simp [entry,transition,hp]) (ih.rename (Sum.inr ∘ Sum.inl) (fun _ _ => rfl))
  | branch_false hp body ih =>
    exact .next (by simp [entry,transition,hp]) (ih.rename (Sum.inr ∘ Sum.inr) (fun _ _ => rfl))
  | loop_false hp => exact .halt (by simp [entry,transition,hp])
  | loop_true hp body rest ih1 ih2 =>
    exact .next (by simp [entry,transition,hp])
      (ih1.plug Sum.inr (.inl ()) (fun _ _ => rfl) ih2)

end Code
end WLTime.TypedStack

namespace WLTime.TypedStack.Code
variable {K : Type uK} {A : Type uA} [DecidableEq K]

 theorem clear_exec (k : K) (s : Stacks K A) :
    (clear k).Exec s (3*(s k).length+1) (Function.update s k []) := by
  generalize hx : s k=xs
  induction xs generalizing s with
  | nil =>
    have hs : Function.update s k []=s := by rw [← hx]; exact Function.update_eq_self k s
    rw [hs]
    exact .loop_false (by simp [nonempty,tops,hx])
  | cons x xs ih =>
    have hstep := ih (Function.update s k xs) (by simp)
    have he : (Function.update (Function.update s k xs) k [])=Function.update s k [] := by simp
    rw [he] at hstep
    have first : Exec (.pop k) s 2 (Function.update s k xs) := by
      simpa only [hx,List.tail_cons] using Exec.pop s k
    have hh := Exec.loop_true (p:=nonempty k) (by simp [nonempty,tops,hx]) first hstep
    convert hh using 1 <;> simp [clear]
    omega

 theorem transfer_exec (a b : K) (hab : a≠b) (zero : A) (s : Stacks K A) :
    (transfer a b zero).Exec s (5*(s a).length+1)
      (Function.update (Function.update s a []) b ((s a).reverse++s b)) := by
  generalize hx : s a=xs
  induction xs generalizing s with
  | nil =>
    have hout : Function.update (Function.update s a []) b (([] : List A).reverse++s b)=s := by
      simp only [List.reverse_nil,List.nil_append]
      rw [← hx,Function.update_eq_self]
      exact Function.update_eq_self b s
    rw [hout]
    exact .loop_false (by simp [nonempty,tops,hx])
  | cons x xs ih =>
    let s₁ := Function.update s b (x::s b)
    let s₂ := Function.update s₁ a xs
    have hs₁a : s₁ a=x::xs := by simp [s₁,Function.update_of_ne hab,hx]
    have hs₂a : s₂ a=xs := by simp [s₂]
    have body : Exec (.seq (.pushDyn b (fun v => (v a).getD zero)) (.pop a)) s 4 s₂ := by
      have hp : Exec (.pushDyn b (fun v => (v a).getD zero)) s 2 s₁ := by
        simpa [tops,hx,s₁] using Exec.pushDyn s b (fun v => (v a).getD zero)
      have hq : Exec (.pop a) s₁ 2 s₂ := by
        simpa [hs₁a,s₂] using Exec.pop s₁ a
      exact .seq hp hq
    have hrest := ih s₂ hs₂a
    have hout : Function.update (Function.update s₂ a []) b (xs.reverse++s₂ b)=
        Function.update (Function.update s a []) b ((x::xs).reverse++s b) := by
      funext k
      by_cases hb : k=b
      · subst k
        simp [s₂,s₁,hab.symm,List.reverse_cons,List.append_assoc]
      · by_cases ha : k=a
        · subst k
          simp [hb]
        · simp [s₂,s₁,hb,ha]
    rw [hout] at hrest
    have hh := Exec.loop_true (p:=nonempty a) (by simp [nonempty,tops,hx]) body hrest
    convert hh using 1 <;> simp [transfer]
    omega

 theorem distribute_exec (a b c : K) (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (zero : A) (s : Stacks K A) :
    (distribute a b c zero).Exec s (7*(s a).length+1)
      (Function.update (Function.update (Function.update s a []) b ((s a).reverse++s b))
        c ((s a).reverse++s c)) := by
  generalize hx : s a=xs
  induction xs generalizing s with
  | nil =>
    have hout : Function.update (Function.update (Function.update s a []) b ([]++s b)) c ([]++s c)=s := by
      simp only [List.nil_append]
      rw [← hx,Function.update_eq_self,Function.update_eq_self,Function.update_eq_self]
    change Exec _ s 1 (Function.update (Function.update (Function.update s a []) b ([]++s b)) c ([]++s c))
    rw [hout]
    exact .loop_false (by simp [nonempty,tops,hx])
  | cons x xs ih =>
    let s₁ := Function.update s b (x::s b)
    let s₂ := Function.update s₁ c (x::s c)
    let s₃ := Function.update s₂ a xs
    have hs₁a : s₁ a=x::xs := by simp [s₁,hab,hx]
    have hs₁c : s₁ c=s c := by simp [s₁,hbc.symm]
    have hs₂a : s₂ a=x::xs := by simp [s₂,hac,hs₁a]
    have hs₃a : s₃ a=xs := by simp [s₃]
    have first : Exec (.pushDyn b (fun v => (v a).getD zero)) s 2 s₁ := by
      simpa [tops,hx,s₁] using Exec.pushDyn s b (fun v => (v a).getD zero)
    have second : Exec (.pushDyn c (fun v => (v a).getD zero)) s₁ 2 s₂ := by
      simpa [tops,hs₁a,hs₁c,s₂] using Exec.pushDyn s₁ c (fun v => (v a).getD zero)
    have third : Exec (.pop a) s₂ 2 s₃ := by
      simpa [hs₂a,s₃] using Exec.pop s₂ a
    have body := Exec.seq first (Exec.seq second third)
    have hrest := ih s₃ hs₃a
    have hout : Function.update (Function.update (Function.update s₃ a []) b (xs.reverse++s₃ b))
        c (xs.reverse++s₃ c)=Function.update (Function.update (Function.update s a [])
          b ((x::xs).reverse++s b)) c ((x::xs).reverse++s c) := by
      funext k
      by_cases hc : k=c
      · subst k
        simp [s₃,s₂,s₁,hac.symm,List.reverse_cons,List.append_assoc]
      · by_cases hb : k=b
        · subst k
          simp [s₃,s₂,s₁,hab.symm,hbc,List.reverse_cons,List.append_assoc]
        · by_cases ha : k=a
          · subst k
            simp [hc,hb]
          · simp [s₃,s₂,s₁,hc,hb,ha]
    rw [hout] at hrest
    have hh := Exec.loop_true (p:=nonempty a) (by simp [nonempty,tops,hx]) body hrest
    convert hh using 1 <;> simp [distribute]
    omega

end WLTime.TypedStack.Code

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Arithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uK uA uL

namespace WLTime.TypedStack.Code
variable {K : Type uK} {A : Type uA} [DecidableEq K]

theorem copy_exec (a b tmp : K) (hab : a≠b) (hat : a≠tmp) (hbt : b≠tmp)
    (zero : A) (s : Stacks K A) (ht : s tmp=[]) :
    (copy a b tmp zero).Exec s (12*(s a).length+2) (Function.update s b (s a++s b)) := by
  let mid := Function.update (Function.update s a []) tmp (s a).reverse
  have hf : (transfer a tmp zero).Exec s (5*(s a).length+1) mid := by
    simpa only [ht,List.append_nil] using transfer_exec a tmp hat zero s
  have he := Exec.seq hf (distribute_exec tmp a b hat.symm hbt.symm hab zero mid)
  convert he using 1 <;> try rfl
  · simp [mid,List.length_reverse]
    omega
  · funext k
    by_cases hb : k=b
    · subst k
      simp [mid,hbt,hab.symm]
    · by_cases ha : k=a
      · subst k
        simp [mid,hat,hb]
      · by_cases hk : k=tmp
        · subst k
          simp [mid,hb,ha,ht]
        · simp [mid,hb,ha,hk]

end WLTime.TypedStack.Code

namespace WLTime.UnaryPrograms
open TypedStack
variable {K : Type uK} [DecidableEq K]

theorem readLoop_exec (a b : K) (hab : a≠b) (s : Stacks K Bool) :
    (readLoop a b).Exec s (5*(scan (s a)).1+1)
      (Function.update (Function.update s a (prefixTail (s a))) b
        (numeral (scan (s a)).1++s b)) := by
  generalize hx : s a=xs
  induction xs generalizing s with
  | nil =>
    have he : Function.update (Function.update s a (prefixTail [])) b (numeral (scan []).1++s b)=s := by
      simp only [prefixTail,scan,numeral,List.replicate_zero,List.nil_append]
      rw [← hx,Function.update_eq_self,Function.update_eq_self]
    rw [he]
    exact .loop_false (by simp [isTrue,tops,hx])
  | cons x xs ih =>
    cases x with
    | false =>
      have he : Function.update (Function.update s a (prefixTail (false::xs))) b
          (numeral (scan (false::xs)).1++s b)=s := by
        simp only [prefixTail,scan,numeral,List.replicate_zero,List.nil_append]
        rw [← hx,Function.update_eq_self,Function.update_eq_self]
      rw [he]
      exact .loop_false (by simp [isTrue,tops,hx])
    | true =>
      let mid := Function.update (Function.update s b (true::s b)) a xs
      have hma : mid a=xs := by simp [mid]
      have hf : Code.Exec (.seq (.push b true) (.pop a)) s 4 mid := by
        have hp := Code.Exec.seq (Code.Exec.push s b true) (Code.Exec.pop _ a)
        simpa only [Function.update_of_ne hab,hx,List.tail_cons] using hp
      have hr := ih mid hma
      have he : Function.update (Function.update mid a (prefixTail xs)) b (numeral (scan xs).1++mid b)=
          Function.update (Function.update s a (prefixTail (true::xs))) b
            (numeral (scan (true::xs)).1++s b) := by
        funext k
        by_cases hb : k=b
        · subst k
          simp [mid,hab.symm,scan,numeral,List.replicate_add,List.append_assoc]
        · by_cases ha : k=a
          · subst k; simp [mid,hb,prefixTail]
          · simp [mid,hb,ha]
      rw [he] at hr
      have hh := Code.Exec.loop_true (p:=isTrue a) (by simp [isTrue,tops,hx]) hf hr
      convert hh using 1 <;> try rfl
      simp only [scan]
      omega

theorem read_exec (a b : K) (hab : a≠b) (s : Stacks K Bool) :
    (read a b).Exec s (5*(scan (s a)).1+3)
      (Function.update (Function.update s a (scan (s a)).2) b (numeral (scan (s a)).1++s b)) := by
  have he := Code.Exec.seq (readLoop_exec a b hab s) (Code.Exec.pop _ a)
  convert he using 1 <;> try rfl
  funext k
  by_cases ha : k=a
  · subst k; simp [hab]
  · by_cases hb : k=b
    · subst k; simp [ha]
    · simp [ha,hb]

theorem scan_le (xs : List Bool) : (scan xs).1 ≤ xs.length := by
  induction xs with
  | nil => simp [scan]
  | cons x xs ih =>
    cases x
    · simp [scan]
    · simp only [scan,List.length_cons]; omega

end WLTime.UnaryPrograms

namespace WLTime.TypedStack.Code
variable {K : Type uK} {L : Type uL} {A : Type uA} [DecidableEq K] [DecidableEq L]

theorem update_sum_inr (e : L → List A) (s : K → List A) (k : K) (xs : List A) :
    Function.update (Sum.elim e s) (.inr k) xs=Sum.elim e (Function.update s k xs) := by
  funext a
  cases a <;> simp

theorem relabel_inr_exec {c : Code K A} {s t out} (h : c.Exec s t out) (e : L → List A) :
    (c.relabel (Sum.inr : K → L ⊕ K)).Exec (Sum.elim e s) t (Sum.elim e out) := by
  induction h with
  | skip s => exact .skip _
  | push s k x => simpa only [relabel,update_sum_inr,Sum.elim_inr] using Exec.push (Sum.elim e s) (.inr k) x
  | pushDyn s k f =>
    have ht : tops (Sum.elim e s) ∘ Sum.inr=tops s := rfl
    simpa only [relabel,update_sum_inr,Sum.elim_inr,ht] using Exec.pushDyn (Sum.elim e s) (.inr k) (fun v => f (v ∘ Sum.inr))
  | pop s k => simpa only [relabel,update_sum_inr,Sum.elim_inr] using Exec.pop (Sum.elim e s) (.inr k)
  | seq first second ih1 ih2 => exact .seq ih1 ih2
  | branch_true hp body ih => exact .branch_true hp ih
  | branch_false hp body ih => exact .branch_false hp ih
  | loop_false hp => exact .loop_false hp
  | loop_true hp body rest ih1 ih2 => exact .loop_true hp ih1 ih2

end WLTime.TypedStack.Code

namespace WLTime.UnaryPrograms
open TypedStack
variable {K : Type uK} [DecidableEq K]

theorem extra_succ_update (n : ℕ) (s : Stacks K Bool) :
    Function.update (Sum.elim (extra (n+1)) s) (.inl 0)
      (Sum.elim (extra (n+1)) s (.inl 0)).tail=Sum.elim (extra n) s := by
  funext i
  cases i with
  | inl j => fin_cases j <;> simp [extra,numeral]
  | inr j => simp

theorem countdown_exec (c : Code K Bool) (f : Stacks K Bool → Stacks K Bool)
    (P : Stacks K Bool → Prop) (B : ℕ)
    (hp : ∀ s, P s → P (f s))
    (hc : ∀ s, P s → ∃ t≤B,c.Exec s t (f s))
    (n : ℕ) (s : Stacks K Bool) (hs : P s) :
    ∃ t≤n*(B+3)+1,
      (Code.loop (Code.nonempty (.inl 0))
        (.seq (c.relabel Sum.inr) (.pop (.inl 0))) : Code (Fin 2 ⊕ K) Bool).Exec
        (Sum.elim (extra n) s) t (Sum.elim (extra 0) (f^[n] s)) := by
  induction n generalizing s with
  | zero =>
    refine ⟨1,by omega,?_⟩
    exact .loop_false (by simp [Code.nonempty,tops,extra,numeral])
  | succ n ih =>
    obtain ⟨u,hu,he⟩ := hc s hs
    have he' := Code.relabel_inr_exec he (extra (n+1))
    have hb := Code.Exec.seq he' (Code.Exec.pop _ (.inl 0))
    rw [extra_succ_update] at hb
    obtain ⟨v,hv,hr⟩ := ih (f s) (hp s hs)
    have hh := Code.Exec.loop_true (p:=Code.nonempty (.inl 0))
      (by simp [Code.nonempty,tops,extra,numeral]) hb hr
    refine ⟨u+2+v+1,?_,?_⟩
    · nlinarith
    · simpa only [Function.iterate_succ_apply] using hh

theorem repeat_exec (base : K) (c : Code K Bool) (f : Stacks K Bool → Stacks K Bool)
    (P : Stacks K Bool → Prop) (B n : ℕ)
    (hp : ∀ s,P s → P (f s))
    (hc : ∀ s,P s → ∃ t≤B,c.Exec s t (f s))
    (s : Stacks K Bool) (hs : P s) (hb : s base=numeral n) :
    ∃ t≤n*(B+15)+3,
      (repeatN base c).Exec (Sum.elim (extra 0) s) t
        (Sum.elim (extra 0) (f^[n] s)) := by
  have hf := Code.copy_exec (.inr base : Fin 2 ⊕ K) (.inl 0) (.inl 1)
    (by simp) (by simp) (by simp) false (Sum.elim (extra 0) s) (by simp [extra])
  have he : Function.update (Sum.elim (extra 0) s) (.inl 0)
      (Sum.elim (extra 0) s (.inr base)++Sum.elim (extra 0) s (.inl 0))=
      Sum.elim (extra n) s := by
    funext i
    cases i with
    | inl j => fin_cases j <;> simp [extra,numeral,hb]
    | inr j => simp
  rw [he] at hf
  obtain ⟨u,hu,hr⟩ := countdown_exec c f P B hp hc n s hs
  refine ⟨_,?_,Code.Exec.seq hf hr⟩
  simp only [Sum.elim_inr,hb,numeral,List.length_replicate]
  nlinarith

end WLTime.UnaryPrograms

namespace WLTime.TypedStack.Code
variable {K : Type uK} {L : Type uL} {A : Type uA} [DecidableEq K] [DecidableEq L]

omit [DecidableEq K] [DecidableEq L] in
theorem liftStacks_apply (f : K → L) (hf : Function.Injective f)
    (frame : Stacks L A) (s : Stacks K A) (k : K) : liftStacks f frame s (f k)=s k := by
  classical
  have h : ∃ a,f a=f k := ⟨k,rfl⟩
  rw [liftStacks,dite_eq_left h]
  exact congrArg s (hf h.choose_spec)

theorem liftStacks_update (f : K → L) (hf : Function.Injective f)
    (frame : Stacks L A) (s : Stacks K A) (k : K) (xs : List A) :
    liftStacks f frame (Function.update s k xs)=Function.update (liftStacks f frame s) (f k) xs := by
  classical
  funext l
  by_cases hl : l=f k
  · subst l
    simp only [liftStacks_apply f hf,Function.update_self]
  · rw [Function.update_of_ne hl]
    unfold liftStacks
    split_ifs with h
    · have hne : h.choose≠k := by
        intro hk
        exact hl (h.choose_spec.symm.trans (congrArg f hk))
      exact Function.update_of_ne hne _ _
    · rfl

omit [DecidableEq K] [DecidableEq L] in
theorem liftStacks_tops (f : K → L) (hf : Function.Injective f)
    (frame : Stacks L A) (s : Stacks K A) : tops (liftStacks f frame s) ∘ f=tops s := by
  funext k
  simp only [Function.comp_apply,tops,liftStacks_apply f hf]

theorem relabel_exec (f : K → L) (hf : Function.Injective f)
    {c : Code K A} {s t out} (h : c.Exec s t out) (frame : Stacks L A) :
    (c.relabel f).Exec (liftStacks f frame s) t (liftStacks f frame out) := by
  induction h with
  | skip s => exact .skip _
  | push s k x =>
    simpa only [relabel,liftStacks_update f hf,liftStacks_apply f hf] using
      Exec.push (liftStacks f frame s) (f k) x
  | pushDyn s k g =>
    simpa only [relabel,liftStacks_update f hf,liftStacks_apply f hf,liftStacks_tops f hf] using
      Exec.pushDyn (liftStacks f frame s) (f k) (fun v => g (v ∘ f))
  | pop s k =>
    simpa only [relabel,liftStacks_update f hf,liftStacks_apply f hf] using
      Exec.pop (liftStacks f frame s) (f k)
  | seq first second ih1 ih2 => exact .seq ih1 ih2
  | branch_true hp body ih =>
    exact .branch_true (by simpa only [liftStacks_tops f hf] using hp) ih
  | branch_false hp body ih =>
    exact .branch_false (by simpa only [liftStacks_tops f hf] using hp) ih
  | loop_false hp => exact .loop_false (by simpa only [liftStacks_tops f hf] using hp)
  | loop_true hp body rest ih1 ih2 =>
    exact .loop_true (by simpa only [liftStacks_tops f hf] using hp) ih1 ih2

theorem relabel_exec_of_maps (f : K → L) (hf : Function.Injective f)
    {c : Code K A} {s t out} (h : c.Exec s t out) (s' out' : Stacks L A)
    (hs : ∀ k,s' (f k)=s k) (ho : ∀ k,out' (f k)=out k)
    (hframe : ∀ l,(∀ k,f k≠l) → out' l=s' l) :
    (c.relabel f).Exec s' t out' := by
  classical
  have hi : liftStacks f s' s=s' := by
    funext l
    unfold liftStacks
    split_ifs with hh
    · exact (hs hh.choose).symm.trans (congrArg s' hh.choose_spec)
    · rfl
  have he : liftStacks f s' out=out' := by
    funext l
    unfold liftStacks
    split_ifs with hh
    · exact (ho hh.choose).symm.trans (congrArg out' hh.choose_spec)
    · exact (hframe l (by simpa only [not_exists] using hh)).symm
  simpa only [hi,he] using relabel_exec f hf h s'
end WLTime.TypedStack.Code

namespace WLTime.TypedStack

namespace Program
variable {K : Type uK} [DecidableEq K]

omit [DecidableEq K] in
theorem embed_injective {a b : ℕ} (j : Fin a → Fin b) (hj : Function.Injective j) :
    Function.Injective (embed (K:=K) j) := Sum.map_injective.mpr ⟨hj,Function.injective_id⟩

theorem raise_exec (p : Program K) {s t out} (h : p.Exec s t out)
    {N : ℕ} (j : Fin p.scratch → Fin N) (hj : Function.Injective j) :
    (p.code.relabel (embed (K:=K) j)).Exec
      (Sum.elim (fun _ : Fin N => []) s) t (Sum.elim (fun _ : Fin N => []) out) := by
  apply Code.relabel_exec_of_maps _ (embed_injective j hj) h
  · intro k; cases k <;> rfl
  · intro k; cases k <;> rfl
  · intro l hl
    cases l with
    | inl x => rfl
    | inr x => exact False.elim (hl (.inr x) rfl)

theorem ofCode_exec {c : Code K Bool} {s t out} (h : c.Exec s t out) :
    (ofCode c).Exec s t out := Code.relabel_inr_exec h (fun _ => [])

theorem seq_exec {p q : Program K} {s t u mid out}
    (hp : p.Exec s t mid) (hq : q.Exec mid u out) :
    (seq p q).Exec s (t+u) out := by
  exact .seq (raise_exec p hp _ (Fin.castAdd_injective _ _))
    (raise_exec q hq _ (Fin.natAdd_injective _ _))

theorem branch_true {test : Tops K Bool → Bool} {p q : Program K} {s t out}
    (ht : test (tops s)=true) (h : p.Exec s t out) :
    (branch test p q).Exec s (t+1) out := by
  exact .branch_true ht (raise_exec p h _ (Fin.castAdd_injective _ _))

theorem branch_false {test : Tops K Bool → Bool} {p q : Program K} {s t out}
    (ht : test (tops s)=false) (h : q.Exec s t out) :
    (branch test p q).Exec s (t+1) out := by
  exact .branch_false ht (raise_exec q h _ (Fin.natAdd_injective _ _))

theorem loop_false {test : Tops K Bool → Bool} {p : Program K} {s}
    (h : test (tops s)=false) : (loop test p).Exec s 1 s := .loop_false h

theorem loop_true {test : Tops K Bool → Bool} {p : Program K} {s t u mid out}
    (ht : test (tops s)=true) (hb : p.Exec s t mid)
    (hr : (loop test p).Exec mid u out) : (loop test p).Exec s (t+u+1) out :=
  .loop_true ht hb hr

theorem skip_exec (s : Stacks K Bool) : (skip : Program K).Exec s 1 s := ofCode_exec (.skip s)
theorem push_exec (a : K) (b : Bool) (s : Stacks K Bool) :
    (push a b).Exec s 2 (Function.update s a (b::s a)) := ofCode_exec (.push s a b)
theorem pop_exec (a : K) (s : Stacks K Bool) :
    (pop a).Exec s 2 (Function.update s a (s a).tail) := ofCode_exec (.pop s a)
theorem clear_exec (a : K) (s : Stacks K Bool) :
    (clear a).Exec s (3*(s a).length+1) (Function.update s a []) :=
  ofCode_exec (Code.clear_exec a s)
theorem read_exec (a b : K) (hab : a≠b) (s : Stacks K Bool) :
    (read a b).Exec s (5*(UnaryPrograms.scan (s a)).1+3)
      (Function.update (Function.update s a (UnaryPrograms.scan (s a)).2) b
        (UnaryPrograms.numeral (UnaryPrograms.scan (s a)).1++s b)) :=
  ofCode_exec (UnaryPrograms.read_exec a b hab s)

theorem copy_exec (a b : K) (hab : a≠b) (s : Stacks K Bool) :
    (copy a b).Exec s (12*(s a).length+2) (Function.update s b (s a++s b)) := by
  simp only [Exec,copy,ambient]
  have h := Code.copy_exec (.inr a : Fin 1 ⊕ K) (.inr b) (.inl 0)
    (by simpa using hab) (by simp) (by simp) false (Sum.elim (fun _ : Fin 1 => []) s) rfl
  convert h using 1; simp only [Sum.elim_inr,Code.update_sum_inr]; rfl

theorem repeat_exec (base : K) (p : Program K) (f : Stacks K Bool → Stacks K Bool)
    (P : Stacks K Bool → Prop) (B n : ℕ)
    (hp : ∀ s,P s → P (f s))
    (hc : ∀ s,P s → ∃ t≤B,p.Exec s t (f s))
    (s : Stacks K Bool) (hs : P s) (hb : s base=UnaryPrograms.numeral n) :
    ∃ t≤n*(B+15)+3,(repeatN base p).Exec s t (f^[n] s) := by
  let g : Stacks (Fin p.scratch ⊕ K) Bool → Stacks (Fin p.scratch ⊕ K) Bool :=
    fun z => p.ambient (f (z ∘ Sum.inr))
  let Q : Stacks (Fin p.scratch ⊕ K) Bool → Prop :=
    fun z => ∃ s,z=p.ambient s ∧ P s
  have hg (s) : g (p.ambient s)=p.ambient (f s) := rfl
  have hi (n) (s) : g^[n] (p.ambient s)=p.ambient (f^[n] s) := by
    induction n generalizing s with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply,hg,ih,Function.iterate_succ_apply]
  have hp' : ∀ z,Q z → Q (g z) := by
    rintro _ ⟨s,rfl,hs⟩
    exact ⟨f s,hg s,hp s hs⟩
  have hc' : ∀ z,Q z → ∃ t≤B,p.code.Exec z t (g z) := by
    rintro _ ⟨s,rfl,hs⟩
    exact hc s hs
  obtain ⟨t,ht,he⟩ := UnaryPrograms.repeat_exec (.inr base : Fin p.scratch ⊕ K) p.code g Q B n hp' hc'
    (p.ambient s) ⟨s,rfl,hs⟩ (show p.ambient s (.inr base)=UnaryPrograms.numeral n from hb)
  rw [hi] at he
  refine ⟨t,ht,?_⟩
  apply Code.relabel_exec_of_maps _ (Equiv.injective _) he
  · intro k; cases k with
    | inl i => fin_cases i <;> rfl
    | inr i => cases i <;> rfl
  · intro k; cases k with
    | inl i => fin_cases i <;> rfl
    | inr i => cases i <;> rfl
  · intro l hl
    exact False.elim (hl ((merge 2 p.scratch).symm l) (Equiv.apply_symm_apply _ l))

end Program
end WLTime.TypedStack

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Expressions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uK uL

namespace WLTime.UnaryPrograms
open TypedStack
variable {K : Type uK} [DecidableEq K]

theorem skipFieldLoop_exec (a : K) (s : Stacks K Bool) :
    (skipFieldLoop a).Exec s (3*(scan (s a)).1+1)
      (Function.update s a (prefixTail (s a))) := by
  generalize hx : s a=xs
  induction xs generalizing s with
  | nil =>
    have he : Function.update s a (prefixTail [])=s := by
      simpa only [prefixTail,←hx] using Function.update_eq_self a s
    rw [he]
    exact .loop_false (by simp [isTrue,tops,hx])
  | cons x xs ih =>
    cases x with
    | false =>
      have he : Function.update s a (prefixTail (false::xs))=s := by
        simpa only [prefixTail,←hx] using Function.update_eq_self a s
      rw [he]
      exact .loop_false (by simp [isTrue,tops,hx])
    | true =>
      have hr := ih (Function.update s a xs) (by simp)
      simp only [Function.update_idem] at hr
      have hp : Code.Exec (.pop a) s 2 (Function.update s a xs) := by
        simpa only [hx,List.tail_cons] using Code.Exec.pop s a
      have he := Code.Exec.loop_true (p:=isTrue a) (by simp [isTrue,tops,hx]) hp hr
      convert he using 1 <;> try rfl
      simp only [scan]
      omega

theorem skipField_exec (a : K) (s : Stacks K Bool) :
    (skipField a).Exec s (3*(scan (s a)).1+3) (Function.update s a (scan (s a)).2) := by
  apply Program.ofCode_exec
  have he := Code.Exec.seq (skipFieldLoop_exec a s) (Code.Exec.pop _ a)
  simpa only [Function.update_self,prefixTail_tail,Function.update_idem,Nat.add_assoc] using he

theorem scan_tail_le (xs : List Bool) : (scan xs).2.length≤xs.length := by
  induction xs with
  | nil => simp [scan]
  | cons b xs ih => cases b <;> simp only [scan,List.length_cons] <;> omega

theorem skipEntry_exec (a : K) (s : Stacks K Bool) :
    ∃ t≤9*(s a).length+9,(skipEntry a).Exec s t (Function.update s a (tailField^[3] (s a))) := by
  have h1 := skipField_exec a s
  have h2 := skipField_exec a (Function.update s a (tailField (s a)))
  have h3 := skipField_exec a (Function.update s a (tailField (tailField (s a))))
  simp only [Function.update_self,Function.update_idem] at h2 h3
  have he := Program.seq_exec h1 (Program.seq_exec h2 h3)
  refine ⟨_,?_,he⟩
  have ha := scan_le (s a)
  have hb := scan_le (tailField (s a))
  have hc := scan_le (tailField (tailField (s a)))
  have hd := scan_tail_le (s a)
  have hf := scan_tail_le (tailField (s a))
  dsimp only [tailField] at *
  omega

theorem tailField_iterate_le (n : ℕ) (xs : List Bool) :
    (tailField^[n] xs).length≤xs.length := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    exact (ih _).trans (scan_tail_le xs)

theorem seek_exec (a index : K) (n : ℕ) (s : Stacks K Bool)
    (hi : s index=numeral n) :
    ∃ t≤n*(9*(s a).length+24)+3,
      (seek a index).Exec s t (Function.update s a (tailField^[3*n] (s a))) := by
  let f := fun s : Stacks K Bool => Function.update s a (tailField^[3] (s a))
  let P := fun z : Stacks K Bool => (z a).length≤(s a).length
  have hp : ∀z,P z → P (f z) := by
    intro z hz
    simpa only [P,f,Function.update_self] using (tailField_iterate_le 3 (z a)).trans hz
  have hc : ∀z,P z → ∃t≤9*(s a).length+9,(skipEntry a).Exec z t (f z) := by
    intro z hz
    obtain ⟨t,ht,he⟩ := skipEntry_exec a z
    exact ⟨t,by dsimp only [P] at hz; omega,he⟩
  have he (n) : f^[n] s=Function.update s a (tailField^[3*n] (s a)) := by
    induction n with
    | zero => simpa only [Function.iterate_zero,Function.id_def,Nat.mul_zero] using
        (Function.update_eq_self a s).symm
    | succ n ih =>
      rw [Function.iterate_succ_apply',ih]
      simp only [f,Function.update_self,Function.update_idem]
      congr 1
      rw [Nat.mul_succ,Nat.add_comm,Function.iterate_add_apply]
  obtain ⟨t,ht,hh⟩ := Program.repeat_exec index (skipEntry a) f P (9*(s a).length+9) n hp hc s le_rfl hi
  rw [he] at hh
  exact ⟨t,by omega,hh⟩

theorem prependRecord_exec (a b : K) (hab : a≠b) (n : ℕ) (s : Stacks K Bool)
    (ha : s a=numeral n) :
    (prependRecord a b).Exec s (12*n+4) (Function.update s b (numeral n++false::s b)) := by
  have he := Program.seq_exec (Program.push_exec b false s)
    (Program.copy_exec a b hab (Function.update s b (false::s b)))
  simpa only [prependRecord,Function.update_of_ne hab,Function.update_self,Function.update_idem,ha,
    numeral,List.length_replicate,Nat.add_comm 2,Nat.add_assoc,Nat.reduceAdd] using he

theorem numeral_add (n m : ℕ) : numeral (n+m)=numeral n++numeral m :=
  List.replicate_add n m true

theorem mulAdd_exec (a b c : K) (hbc : b≠c)
    (s : Stacks K Bool) (na nb : ℕ) (ha : s a=numeral na) (hb : s b=numeral nb) :
    ∃t≤na*(12*nb+17)+3,
      (mulAdd a b c).Exec s t (Function.update s c (numeral (na*nb)++s c)) := by
  let f := fun z : Stacks K Bool => Function.update z c (z b++z c)
  let P := fun z : Stacks K Bool => z b=numeral nb
  have hp : ∀z,P z → P (f z) := by
    intro z hz
    simpa only [P,f,Function.update_of_ne hbc] using hz
  have hc : ∀z,P z → ∃t≤12*nb+2,(Program.copy b c).Exec z t (f z) := by
    intro z hz
    change z b=numeral nb at hz
    refine ⟨12*nb+2,le_rfl,?_⟩
    simpa only [f,hz,numeral_length] using Program.copy_exec b c hbc z
  have hi (n) : f^[n] s=Function.update s c (numeral (n*nb)++s c) := by
    induction n with
    | zero => simpa only [Function.iterate_zero,Function.id_def,Nat.zero_mul,numeral,
        List.replicate_zero,List.nil_append] using (Function.update_eq_self c s).symm
    | succ n ih =>
      rw [Function.iterate_succ_apply',ih]
      simp only [f,Function.update_of_ne hbc,Function.update_self,Function.update_idem,hb]
      congr 1
      rw [Nat.succ_mul,Nat.add_comm,numeral_add,List.append_assoc]
  obtain ⟨t,ht,he⟩ := Program.repeat_exec a (Program.copy b c) f P (12*nb+2) na hp hc s hb ha
  rw [hi] at he
  exact ⟨t,by omega,he⟩

end WLTime.UnaryPrograms

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Digits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uJ

namespace WLTime.Digits

theorem value_eq_zero_iff {d m : ℕ} (hm : 0< m) (a : Word d m) :
    value a=0 ↔ ∀ i,(a i).val=0 := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [value_succ,Fin.forall_fin_succ]
    constructor
    · intro h
      have hz : value (fun i : Fin d => a i.succ)=0 := by nlinarith
      exact ⟨by omega,(ih _).mp hz⟩
    · rintro ⟨h0,ht⟩
      rw [h0,(ih _).mpr ht]
      omega

end WLTime.Digits

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Tableau
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uP uE uS uT uG uH uF uAlphabet

namespace WLTime.CircuitEncoding

namespace Schematic
variable {r m : ℕ} {P : Type uP} {E : Type uE} {S : Type uS} {T : Type uT} (C : Schematic r m P E S T)

open Compression.ConsistencyData

theorem setsOfWitness_nonempty (W : C.expand.Witness) (p : Node P E) (a : Address r m) :
    (C.setsOfWitness W p a).Nonempty := by
  classical
  cases p with
  | gate p => exact W.gate_nonempty (p,a)
  | buffer e =>
    change (if h : ProductAllowed (C.domain e) a then W.buffer ⟨e,⟨a,h⟩⟩ else Set.univ).Nonempty
    by_cases h : ProductAllowed (C.domain e) a
    · rw [dite_eq_left h]
      exact W.buffer_nonempty ⟨e,⟨a,h⟩⟩
    · rw [dite_eq_right h]
      exact Set.univ_nonempty
  | dummy => exact Set.univ_nonempty

theorem setsOfWitness_buffer (W : C.expand.Witness) (e : E) (a : Address r m)
    (ha : ProductAllowed (C.domain e) a) :
    C.setsOfWitness W (.buffer e) a = W.buffer ⟨e,⟨a,ha⟩⟩ := by
  exact dite_eq_left ha

theorem consistent_of_witness (W : C.expand.Witness) : C.consistency.ArcConsistent := by
  classical
  refine ⟨C.setsOfWitness W,C.setsOfWitness_nonempty W,?_⟩
  intro f a ha
  cases f with
  | first e =>
    rw [C.affineSrc_first e a,C.affineDst_first e,C.same_transmit_first]
    change C.expand.output (C.src e,a) '' W.gate (C.src e,a) =
      (fun z : Fin 2 → Bit => z 0) '' C.setsOfWitness W (.buffer e) a
    rw [C.setsOfWitness_buffer W e a ha]
    exact W.first ⟨e,⟨a,ha⟩⟩
  | second e =>
    rw [C.affineSrc_second e a,C.affineDst_second e,C.same_transmit_second]
    change C.expand.output (C.src e,a) '' W.gate (C.src e,a) =
      (fun z : Fin 2 → Bit => z 1) '' C.setsOfWitness W (.buffer e) a
    rw [C.setsOfWitness_buffer W e a ha]
    exact W.second ⟨e,⟨a,ha⟩⟩
  | third e =>
    rw [C.affineSrc_third e,C.affineDst_third e,C.same_transmit_third]
    change (fun z : Fin 2 → Bit => z 0 + z 1) '' C.setsOfWitness W (.buffer e) a =
      (fun z => z (C.port e)) '' W.gate (C.dst e,C.transmit e a ha)
    rw [C.setsOfWitness_buffer W e a ha]
    exact W.third ⟨e,⟨a,ha⟩⟩
  | seed s =>
    have hs : C.expand.seed (C.seedGate s,a) = true := by
      simp only [expand,decide_eq_true_eq]
      exact ⟨s,rfl,ha⟩
    rw [C.affineSrc_seed s a,C.affineDst_seed s,C.same_transmit_seed]
    change C.expand.output (C.seedGate s,a) '' W.gate (C.seedGate s,a) =
      (fun _ : Fin 1 → Bit => (0 : Bit)) '' Set.univ
    rw [const_image Set.univ_nonempty]
    exact W.seeds _ hs
  | test t =>
    have ht : C.expand.test (C.testGate t,a) = true := by
      simp only [expand,decide_eq_true_eq]
      exact ⟨t,rfl,ha⟩
    rw [C.affineSrc_test t a,C.affineDst_test t,C.same_transmit_test]
    change C.expand.output (C.testGate t,a) '' W.gate (C.testGate t,a) =
      (fun _ : Fin 1 → Bit => (1 : Bit)) '' Set.univ
    rw [const_image Set.univ_nonempty]
    exact W.tests _ ht

theorem consistency_iff_tests_false : C.consistency.ArcConsistent ↔
    ∀ g, C.expand.test g = true → ¬C.expand.TrueAt g := by
  rw [← C.expand.witness_iff_tests_false]
  constructor
  · rintro ⟨Q,hQ,hE⟩
    exact ⟨C.witnessOfConsistent Q hQ hE⟩
  · rintro ⟨W⟩
    exact C.consistent_of_witness W

end Schematic
end WLTime.CircuitEncoding

namespace WLTime.CircuitEncoding.Circuit
variable {G : Type uG} {E : Type uE} {H : Type uH} {F : Type uF} (C : Circuit G E) (D : Circuit H F) (f : G ≃ H)

theorem incoming_of_cover (hE : C.EdgeCover D f) (g : G) (R : H → ℕ → Prop) :
    (∃ e,C.dst e=g ∧ R (f (C.src e)) (C.port e).val) ↔
      ∃ e,D.dst e=f g ∧ R (D.src e) (D.port e).val := by
  constructor
  · rintro ⟨e,he,hR⟩
    obtain ⟨e',hd,hs,hp⟩ := (hE g (C.src e) (C.port e).val).mp ⟨e,he,rfl,rfl⟩
    exact ⟨e',hd,by simpa only [hs,hp] using hR⟩
  · rintro ⟨e,he,hR⟩
    obtain ⟨e',hd,hs,hp⟩ := (hE g (f.symm (D.src e)) (D.port e).val).mpr
      ⟨e,he,by simp,rfl⟩
    exact ⟨e',hd,by simpa only [hs,hp,f.apply_symm_apply] using hR⟩

theorem truth_of_cover (hE : C.EdgeCover D f)
    (hkind : ∀ g,C.kind g=D.kind (f g)) (hseed : ∀ g,C.seed g=D.seed (f g))
    (g : G) : C.TrueAt g ↔ D.TrueAt (f g) := by
  apply C.truth_iff_of_equations (fun g => D.TrueAt (f g)) _ g
  intro g
  rw [TrueAt,← hkind g,← hseed g]
  split_ifs
  · apply or_congr Iff.rfl
    simpa only [exists_prop] using (C.incoming_of_cover D f hE g (fun s _ => D.TrueAt s)).symm
  · apply forall_congr'
    intro p
    simpa only [exists_prop] using (C.incoming_of_cover D f hE g (fun s v => v=p.val ∧ D.TrueAt s)).symm

end WLTime.CircuitEncoding.Circuit

namespace WLTime.CircuitEncoding.BoxTableau
open ProductBox
open Tableau

variable {Alphabet : Type uAlphabet} {d q m : ℕ}
variable (F : Alphabet → Alphabet → Alphabet → Alphabet)

theorem left_covered (x y z : Alphabet) (a b : ProductBox.Address (d+q) m)
    (ht : Digits.value (ProductBox.time b)=Digits.value (ProductBox.time a)+1)
    (hj : Digits.encode (ProductBox.space b)=Digits.inc (m^q) (Digits.encode (ProductBox.space a))) :
    ∃ p s,(box (.left x y z p s)).Rel a b := by
  obtain ⟨p,hp⟩ := (Digits.nonwrap_relation _ _).mpr ht
  obtain ⟨s,hs⟩ := (ProductBox.Box.carry_rel _ _).mpr hj
  exact ⟨p,s,(ProductBox.Box.product_relation _ _ _ _).mpr ⟨hp,hs⟩⟩

theorem center_covered (x y z : Alphabet) (a b : ProductBox.Address (d+q) m)
    (ht : Digits.value (ProductBox.time b)=Digits.value (ProductBox.time a)+1)
    (hj : Digits.encode (ProductBox.space b)=Digits.encode (ProductBox.space a)) :
    ∃ p,(box (.center x y z p)).Rel a b := by
  obtain ⟨p,hp⟩ := (Digits.nonwrap_relation _ _).mpr ht
  exact ⟨p,(ProductBox.Box.product_relation _ _ _ _).mpr
    ⟨hp,(ProductBox.Box.identity_rel _ _).mpr (Digits.encode.injective hj.symm)⟩⟩

theorem right_covered (x y z : Alphabet) (a b : ProductBox.Address (d+q) m)
    (ht : Digits.value (ProductBox.time b)=Digits.value (ProductBox.time a)+1)
    (hj : Digits.encode (ProductBox.space b)=(Digits.inc (m^q)).symm (Digits.encode (ProductBox.space a))) :
    ∃ p s,(box (.right x y z p s)).Rel a b := by
  obtain ⟨p,hp⟩ := (Digits.nonwrap_relation _ _).mpr ht
  obtain ⟨s,hs⟩ := (ProductBox.Box.borrow_rel _ _).mpr hj
  exact ⟨p,s,(ProductBox.Box.product_relation _ _ _ _).mpr ⟨hp,hs⟩⟩

theorem realizes (e : Label Alphabet d q) (a b : ProductBox.Address (d+q) m)
    (hab : (box e).Rel a b) :
    ∃ u : Tableau.Connection Alphabet (Fin (m^q)) (m^d),
      Tableau.source (Digits.inc (m^q)) u=nodeMap (src e,a) ∧
      Tableau.target F u=nodeMap (dst F e,b) ∧
      (Tableau.port F u).val=(port F e).val := by
  have hn := box_numerical e hab
  have prev_eq (h : Digits.value (ProductBox.time b)=Digits.value (ProductBox.time a)+1) :
      ∃ hb : 0<(Digits.encode (ProductBox.time b)).val,
        Tableau.prevTime (Digits.encode (ProductBox.time b)) hb=Digits.encode (ProductBox.time a) := by
    have hb : 0<(Digits.encode (ProductBox.time b)).val := by change 0<Digits.value _; omega
    exact ⟨hb,Fin.ext (by change Digits.value (ProductBox.time b)-1=Digits.value (ProductBox.time a); omega)⟩
  cases e with
  | left x y z p j =>
    obtain ⟨ht,hj⟩ := hn
    obtain ⟨hb,hprev⟩ := prev_eq ht
    refine ⟨.left x y z (Digits.encode (ProductBox.time b)) hb (Digits.encode (ProductBox.space b)),?_,rfl,rfl⟩
    simp only [Tableau.source,src,nodeMap,hprev,hj,Equiv.symm_apply_apply]
  | center x y z p =>
    obtain ⟨ht,hj⟩ := hn
    obtain ⟨hb,hprev⟩ := prev_eq ht
    refine ⟨.center x y z (Digits.encode (ProductBox.time b)) hb (Digits.encode (ProductBox.space b)),?_,rfl,rfl⟩
    simp only [Tableau.source,src,nodeMap,hprev,hj]
  | bridge x y z =>
    change a=b at hn
    subst b
    exact ⟨.bridge x y z (Digits.encode (ProductBox.time a)) (Digits.encode (ProductBox.space a)),rfl,rfl,rfl⟩
  | right x y z p j =>
    obtain ⟨ht,hj⟩ := hn
    obtain ⟨hb,hprev⟩ := prev_eq ht
    refine ⟨.right x y z (Digits.encode (ProductBox.time b)) hb (Digits.encode (ProductBox.space b)),?_,rfl,rfl⟩
    simp only [Tableau.source,src,nodeMap,hprev,hj,Equiv.apply_symm_apply]
  | out x y z =>
    change a=b at hn
    subst b
    exact ⟨.out x y z (Digits.encode (ProductBox.time a)) (Digits.encode (ProductBox.space a)),rfl,rfl,rfl⟩

theorem covers (u : Tableau.Connection Alphabet (Fin (m^q)) (m^d)) :
    ∃ e : Label Alphabet d q,
      src e=(Tableau.source (Digits.inc (m^q)) u).1 ∧
      dst F e=(Tableau.target F u).1 ∧
      (box e).Rel (ProductBox.addressEquiv.symm (Tableau.source (Digits.inc (m^q)) u).2)
        (ProductBox.addressEquiv.symm (Tableau.target F u).2) ∧
      (port F e).val=(Tableau.port F u).val := by
  cases u with
  | left x y z t ht j =>
    obtain ⟨p,s,hp⟩ := left_covered x y z
      (ProductBox.addressEquiv.symm (Tableau.prevTime t ht,(Digits.inc (m^q)).symm j))
      (ProductBox.addressEquiv.symm (t,j)) (by
        simp only [ProductBox.addressEquiv,Equiv.coe_fn_symm_mk,ProductBox.time_append,
          Digits.value,Equiv.apply_symm_apply,Tableau.prevTime]
        omega) (by
        simp only [ProductBox.addressEquiv,Equiv.coe_fn_symm_mk,ProductBox.space_append,
          Equiv.apply_symm_apply])
    exact ⟨.left x y z p s,rfl,rfl,hp,rfl⟩
  | center x y z t ht j =>
    obtain ⟨p,hp⟩ := center_covered x y z
      (ProductBox.addressEquiv.symm (Tableau.prevTime t ht,j))
      (ProductBox.addressEquiv.symm (t,j)) (by
        simp only [ProductBox.addressEquiv,Equiv.coe_fn_symm_mk,ProductBox.time_append,
          Digits.value,Equiv.apply_symm_apply,Tableau.prevTime]
        omega) (by
        simp only [ProductBox.addressEquiv,Equiv.coe_fn_symm_mk,ProductBox.space_append,
          Equiv.apply_symm_apply])
    exact ⟨.center x y z p,rfl,rfl,hp,rfl⟩
  | bridge x y z t j =>
    exact ⟨.bridge x y z,rfl,rfl,(ProductBox.Box.identity_rel _ _).mpr rfl,rfl⟩
  | right x y z t ht j =>
    obtain ⟨p,s,hp⟩ := right_covered x y z
      (ProductBox.addressEquiv.symm (Tableau.prevTime t ht,Digits.inc (m^q) j))
      (ProductBox.addressEquiv.symm (t,j)) (by
        simp only [ProductBox.addressEquiv,Equiv.coe_fn_symm_mk,ProductBox.time_append,
          Digits.value,Equiv.apply_symm_apply,Tableau.prevTime]
        omega) (by
        simp only [ProductBox.addressEquiv,Equiv.coe_fn_symm_mk,ProductBox.space_append,
          Equiv.apply_symm_apply,Equiv.symm_apply_apply])
    exact ⟨.right x y z p s,rfl,rfl,hp,rfl⟩
  | out x y z t j =>
    exact ⟨.out x y z,rfl,rfl,(ProductBox.Box.identity_rel _ _).mpr rfl,rfl⟩

section Initialization
open scoped Classical
variable (input : Fin m → Alphabet) (blank : Alphabet)

theorem seed_allowed (s : Alphabet ⊕ Fin q) (a : ProductBox.Address (d+(q+1)) m) :
    ProductAllowed (seedDomain input s) a ↔
      (∀ i,(ProductBox.time a i).val=0) ∧
      ProductAllowed (positionDomain input s) (ProductBox.space a) := by
  simp only [ProductAllowed,seedDomain,Fin.forall_fin_add,Fin.addCases_left,
    Fin.addCases_right,Finset.mem_filter,Finset.mem_univ,true_and]

theorem input_allowed (f : Alphabet) (a : ProductBox.Address (q+1) m) :
    ProductAllowed (positionDomain input (.inl f)) a ↔
      input (a 0)=f ∧ ∀ i : Fin q,(a i.succ).val=0 := by
  simp only [ProductAllowed,positionDomain,Fin.forall_fin_succ,Fin.cases_zero,
    Fin.cases_succ,Finset.mem_filter,Finset.mem_univ,true_and]

theorem blank_allowed (i : Fin q) (a : ProductBox.Address (q+1) m) :
    ProductAllowed (positionDomain input (.inr i)) a ↔ (a i.succ).val≠0 := by
  simp only [ProductAllowed,positionDomain,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro h; exact h i.succ rfl
  · intro h j hj; simpa only [hj] using h

theorem seed_spec (hm : 0< m) (f : Alphabet) (a : ProductBox.Address (d+(q+1)) m) :
    (∃ s,seedGate blank s=.scalar f ∧ ProductAllowed (seedDomain input s) a) ↔
      Digits.value (ProductBox.time a)=0 ∧ f=initialDigit input blank (ProductBox.space a) := by
  constructor
  · rintro ⟨s,hs,ha⟩
    obtain ⟨ht,hp⟩ := (seed_allowed input s a).mp ha
    refine ⟨(Digits.value_eq_zero_iff hm _).mpr ht,?_⟩
    cases s with
    | inl x =>
      have hx : x=f := Gate.scalar.inj hs
      obtain ⟨hi,hh⟩ := (input_allowed input x _).mp hp
      simp only [initialDigit,ite_eq_left hh,← hx,hi]
    | inr i =>
      have hf : blank=f := Gate.scalar.inj hs
      have hi := (blank_allowed input i _).mp hp
      have hh : ¬∀ j : Fin q,(ProductBox.space a j.succ).val=0 := fun h => hi (h i)
      simp only [initialDigit,ite_eq_right hh,← hf]
  · rintro ⟨ht,hf⟩
    have ht' := (Digits.value_eq_zero_iff hm _).mp ht
    by_cases hh : ∀ j : Fin q,(ProductBox.space a j.succ).val=0
    · refine ⟨.inl f,rfl,(seed_allowed input _ _).mpr ⟨ht',?_⟩⟩
      apply (input_allowed input _ _).mpr
      exact ⟨by simpa only [initialDigit,ite_eq_left hh] using hf.symm,hh⟩
    · obtain ⟨i,hi⟩ := not_forall.mp hh
      refine ⟨.inr i,?_,(seed_allowed input _ _).mpr ⟨ht',?_⟩⟩
      · change Gate.scalar blank=.scalar f
        simpa only [initialDigit,ite_eq_right hh] using congrArg Gate.scalar hf.symm
      · exact (blank_allowed input i _).mpr hi

variable (accepting : Alphabet → Prop)

theorem test_spec (f : Alphabet) (a : ProductBox.Address (d+(q+1)) m) :
    (∃ s,testGate accepting s=.scalar f ∧ ProductAllowed (testDomain accepting s) a) ↔
      Digits.value (ProductBox.time a)+1=m^d ∧ accepting f := by
  simp only [testGate,Gate.scalar.injEq,test_allowed accepting]
  constructor
  · rintro ⟨s,hs,ht⟩; exact ⟨ht,hs ▸ s.property⟩
  · rintro ⟨ht,hf⟩; exact ⟨⟨f,hf⟩,rfl,ht⟩

theorem edge_cover :
    (schematic F input blank accepting : Schematic (d+(q+1)) m _ _ _ _).expand.EdgeCover
      (Tableau.circuit F (Digits.inc (m^(q+1))) (initialRing input blank) accepting) nodeEquiv := by
  intro g s p
  constructor
  · rintro ⟨⟨e,a,ha⟩,hg,hs,hp⟩
    obtain ⟨u,hu,hv,hw⟩ := realizes F e a ((box e).apply a) ⟨ha,rfl⟩
    refine ⟨u,?_,?_,hw.trans hp⟩
    · exact hv.trans (congrArg nodeEquiv hg)
    · exact hu.trans (congrArg nodeEquiv hs)
  · rintro ⟨u,hg,hs,hp⟩
    change Tableau.target F u=nodeEquiv g at hg
    change Tableau.source (Digits.inc (m^(q+1))) u=nodeEquiv s at hs
    obtain ⟨e,he,hf,hab,hp'⟩ := covers F u
    let a := ProductBox.addressEquiv.symm (Tableau.source (Digits.inc (m^(q+1))) u).2
    let b := ProductBox.addressEquiv.symm (Tableau.target F u).2
    have hsrc : (src e,a)=nodeEquiv.symm (Tableau.source (Digits.inc (m^(q+1))) u) := by
      exact Prod.ext he rfl
    have hdst : (dst F e,(box e).apply a)=nodeEquiv.symm (Tableau.target F u) := by
      exact Prod.ext hf hab.2
    refine ⟨⟨e,a,hab.1⟩,?_,?_,hp'.trans hp⟩
    · change (dst F e,(box e).apply a)=g
      rw [hdst,hg,Equiv.symm_apply_apply]
    · change (src e,a)=s
      rw [hsrc,hs,Equiv.symm_apply_apply]

 theorem seed_eq (hm : 0< m) (g : Gate Alphabet × ProductBox.Address (d+(q+1)) m) :
    (schematic F input blank accepting).expand.seed g =
      (Tableau.circuit F (Digits.inc (m^(q+1))) (initialRing input blank) accepting).seed (nodeEquiv g) := by
  classical
  rcases g with ⟨g,a⟩
  cases g with
  | scalar f =>
    change decide (∃ s,seedGate blank s=.scalar f ∧ ProductAllowed (seedDomain input s) a) =
      decide (Digits.value (ProductBox.time a)=0 ∧ f=initialRing input blank (Digits.encode (ProductBox.space a)))
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq,seed_spec input blank hm,initialRing,Equiv.symm_apply_apply]
  | first x y z =>
    change decide (∃ s,seedGate blank s=.first x y z ∧ ProductAllowed (seedDomain input s) a)=false
    apply decide_eq_false
    rintro ⟨s,hs,_⟩
    cases s <;> cases hs
  | second x y z =>
    change decide (∃ s,seedGate blank s=.second x y z ∧ ProductAllowed (seedDomain input s) a)=false
    apply decide_eq_false
    rintro ⟨s,hs,_⟩
    cases s <;> cases hs

theorem test_eq (g : Gate Alphabet × ProductBox.Address (d+(q+1)) m) :
    (schematic F input blank accepting).expand.test g =
      (Tableau.circuit F (Digits.inc (m^(q+1))) (initialRing input blank) accepting).test (nodeEquiv g) := by
  classical
  rcases g with ⟨g,a⟩
  cases g with
  | scalar f =>
    change decide (∃ s,testGate accepting s=.scalar f ∧ ProductAllowed (testDomain accepting s) a) =
      decide (Digits.value (ProductBox.time a)+1=m^d ∧ accepting f)
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq,test_spec accepting]
  | first x y z =>
    change decide (∃ s,Gate.scalar s.val=.first x y z ∧ ProductAllowed (testDomain accepting s) a)=false
    simp
  | second x y z =>
    change decide (∃ s,Gate.scalar s.val=.second x y z ∧ ProductAllowed (testDomain accepting s) a)=false
    simp

theorem truth_eq (hm : 0< m) (g : Gate Alphabet × ProductBox.Address (d+(q+1)) m) :
    (schematic F input blank accepting).expand.TrueAt g ↔
      (Tableau.circuit F (Digits.inc (m^(q+1))) (initialRing input blank) accepting).TrueAt (nodeEquiv g) :=
  Circuit.truth_of_cover _ _ nodeEquiv (edge_cover F input blank accepting)
    (fun _ => rfl) (seed_eq F input blank accepting hm) g

theorem local_equivalence (hm : 0< m) :
    (∀ g, (schematic F input blank accepting : Schematic (d+(q+1)) m _ _ _ _).expand.test g=true →
      ¬(schematic F input blank accepting).expand.TrueAt g) ↔
      ∀ j, ¬accepting (Tableau.run F (Digits.inc (m^(q+1))) (initialRing input blank) (m^d-1) j) := by
  rw [← Tableau.tests_false_iff F (Digits.inc (m^(q+1))) (initialRing input blank) (Nat.pow_pos hm) accepting]
  constructor
  · intro h g
    have hi := h (nodeEquiv.symm g)
    simpa only [test_eq F input blank accepting,truth_eq F input blank accepting hm,
      Equiv.apply_symm_apply] using hi
  · intro h g
    simpa only [test_eq F input blank accepting,truth_eq F input blank accepting hm] using h (nodeEquiv g)

end Initialization

end WLTime.CircuitEncoding.BoxTableau

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Simulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA uJ uK uAlphabet

namespace WLTime.CircuitEncoding.Tableau
variable {A : Type uA} {J : Type uJ} {K : Type uK} (F : A → A → A → A) (s : Equiv.Perm J) (t : Equiv.Perm K)
  (e : J ≃ K) (u : J → A) (v : K → A)

theorem run_reindex (hstep : ∀ j,e (s j)=t (e j)) (hinit : ∀ j,u j=v (e j))
    (n : ℕ) (j : J) : run F s u n j=run F t v n (e j) := by
  have hinv (j : J) : e (s.symm j)=t.symm (e j) := by
    apply t.injective
    rw [t.apply_symm_apply,← hstep,s.apply_symm_apply]
  induction n generalizing j with
  | zero => exact hinit j
  | succ n ih => simp only [run_succ,ih,hinv,hstep]
end WLTime.CircuitEncoding.Tableau

namespace WLTime.Digits

theorem value_lt_base_iff {q m : ℕ} (hm : 0< m) (a : Word (q+1) m) :
    value a< m ↔ ∀ i : Fin q,(a i.succ).val=0 := by
  rw [← value_eq_zero_iff hm (fun i => a i.succ),value_succ]
  have hhead := (a 0).isLt
  constructor
  · intro h
    by_contra hh
    have hx : 1 ≤ value (fun i => a i.succ) := Nat.one_le_iff_ne_zero.mpr hh
    have hh' := Nat.mul_le_mul_left m hx
    omega
  · intro h
    simp only [h,Nat.mul_zero,Nat.add_zero]
    exact hhead

 theorem finEquiv_val {n : ℕ} [NeZero n] (j : Fin n) :
    (ZMod.finEquiv n j).val=j.val := by
  cases n with
  | zero => exact Fin.elim0 j
  | succ n => rfl

 theorem finEquiv_shift {n : ℕ} [NeZero n] (j : Fin n) :
    ZMod.finEquiv n (inc n j)=OneTape.ringShift n (ZMod.finEquiv n j) := by
  apply ZMod.val_injective
  rw [finEquiv_val,inc_value]
  change (if j.val+1=n then 0 else j.val+1)=((ZMod.finEquiv n j)+1).val
  have h1 : (1 : ZMod n).val=1%n := by simpa only [Nat.cast_one] using ZMod.val_natCast n 1
  rw [ZMod.val_add,finEquiv_val,h1]
  by_cases hn : n=1
  · subst n
    simp
  · have hn' : 1<n := by have := NeZero.ne n; omega
    rw [Nat.mod_eq_of_lt hn']
    by_cases hj : j.val+1=n
    · simp [hj]
    · rw [ite_eq_right hj,Nat.mod_eq_of_lt (by have := j.isLt; omega)]

end WLTime.Digits

namespace WLTime.OneTape
variable (M : OneTape)
open CircuitEncoding

 theorem ring_initial_digits (w : List Bool) (hm : 0< w.length) (q : ℕ)
    [NeZero (w.length^(q+1))] (j : Fin (w.length^(q+1))) :
    BoxTableau.initialRing (M.inputCell w) M.blankCell j=
      M.snapshot (M.ringInitial (w.length^(q+1)) w) (ZMod.finEquiv (w.length^(q+1)) j) := by
  have hval : Digits.value (Digits.encode.symm j)=j.val := by
    simp only [Digits.value,Equiv.apply_symm_apply]
  have hzero : ZMod.finEquiv (w.length^(q+1)) j=0 ↔ j.val=0 := by
    rw [← ZMod.val_eq_zero,Digits.finEquiv_val]
  unfold BoxTableau.initialRing BoxTableau.initialDigit
  by_cases hj : j.val< w.length
  · have ht := (Digits.value_lt_base_iff hm (Digits.encode.symm j)).mp (hval ▸ hj)
    rw [ite_eq_left ht]
    have ha : ((Digits.encode.symm j) 0).val=j.val := by
      have hz := (Digits.value_eq_zero_iff hm (fun i => Digits.encode.symm j i.succ)).mpr ht
      rw [Digits.value_succ,hz,Nat.mul_zero,Nat.add_zero] at hval
      exact hval
    simp [inputCell,snapshot,ringInitial,Digits.finEquiv_val,ha,hj,hzero]
  · have ht : ¬∀ i : Fin q,(Digits.encode.symm j i.succ).val=0 := by
      rw [← Digits.value_lt_base_iff hm,hval]
      exact hj
    rw [ite_eq_right ht]
    have hz : j.val≠0 := by omega
    simp [blankCell,snapshot,ringInitial,Digits.finEquiv_val,hj,hzero,hz]

end WLTime.OneTape

end OAI
end

section
-- module Solutions.OAIQW_WLTime.GraphFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uJ uT uP uE uA uB uA' uB' uV uW uU

namespace WLTime.Compression.ConsistencyData
variable {r m : ℕ} {P : Type uP} {E : Type uE} (I : ConsistencyData (r+1) m P E)

variable [Fintype P] [Fintype E]
open scoped Classical

 theorem mixedCode_pos (K : ℕ) (t : BlockTag (r:=r) (P:=P) (E:=E) K) (a b : Fin m) :
    0 < mixedCode (m:=m) K t a b := by unfold mixedCode; omega

 theorem mixedCode_le (K : ℕ) (t : BlockTag (r:=r) (P:=P) (E:=E) K) (a b : Fin m) :
    mixedCode (m:=m) K t a b≤Fintype.card (BlockTag (r:=r) (P:=P) (E:=E) K)*m^2 := by
  have ht := (finProdFinEquiv (finProdFinEquiv (Fintype.equivFin _ t,a),b)).isLt
  change b.val+m*(a.val+m*(Fintype.equivFin _ t).val) < _ at ht
  unfold mixedCode
  nlinarith

 theorem mixedCode_injective (K : ℕ) :
    Function.Injective (fun x : BlockTag (r:=r) (P:=P) (E:=E) K × Fin m × Fin m =>
      mixedCode (m:=m) K x.1 x.2.1 x.2.2) := by
  rintro ⟨t,a,b⟩ ⟨u,c,d⟩ h
  have he : finProdFinEquiv (finProdFinEquiv (Fintype.equivFin _ t,a),b) =
      finProdFinEquiv (finProdFinEquiv (Fintype.equivFin _ u,c),d) := by
    apply Fin.ext
    change b.val+m*(a.val+m*(Fintype.equivFin _ t).val) = d.val+m*(c.val+m*(Fintype.equivFin _ u).val)
    simpa only [mixedCode,Nat.add_left_inj] using h
  have h1 := finProdFinEquiv.injective he
  have h2 := finProdFinEquiv.injective (congrArg Prod.fst h1)
  have ht := (Fintype.equivFin _).injective (congrArg Prod.fst h2)
  have ha : a=c := congrArg Prod.snd h2
  have hb : b=d := congrArg Prod.snd h1
  subst u; subst c; subst d; rfl

 theorem rawCode_injective (K : ℕ) : Function.Injective (rawCode (r:=r) (m:=m) (P:=P) (E:=E) K) := by
  intro x y h
  cases x <;> cases y
  all_goals simp only [rawCode] at h
  all_goals have he := mixedCode_injective K (a₁:=(_,_,_)) (a₂:=(_,_,_)) h
  all_goals simp only [Prod.mk.injEq,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq] at he
  all_goals first | rcases he with ⟨⟨rfl,rfl⟩,rfl,rfl⟩; rfl | tauto

 theorem rawCode_pos (K : ℕ) (v : RawBlock (r:=r) (m:=m) (P:=P) (E:=E) K) : 0<rawCode K v := by
  cases v <;> exact mixedCode_pos (P:=P) (E:=E) K _ _ _

 theorem rawCode_le (K : ℕ) (v : RawBlock (r:=r) (m:=m) (P:=P) (E:=E) K) :
    rawCode K v≤Fintype.card (BlockTag (r:=r) (P:=P) (E:=E) K)*m^2 := by
  cases v <;> exact mixedCode_le (P:=P) (E:=E) K _ _ _

 theorem rect_card (K : ℕ) : Fintype.card (I.Rect K)=I.rectCoefficient K*m^2 := by
  simp only [Rect,Fintype.card_prod,Fintype.card_fin,rectCoefficient,pow_two]
  ring

 theorem tagValues_card_pos (K : ℕ) : 0<Fintype.card (I.TagValues K) := by
  apply Fintype.card_pos_iff.mpr
  exact ⟨fun _ => 0⟩

 theorem rectangle_code_le (K : ℕ) (v : RawBlock (r:=r) (m:=m) (P:=P) (E:=E) K) :
    rawCode K v≤I.rectCoefficient K*m^2 := by
  apply (rawCode_le K v).trans
  have h := I.tagValues_card_pos K
  unfold rectCoefficient
  gcongr
  exact Nat.le_mul_of_pos_right _ h

 theorem card_bases_le_rectangle (K : ℕ) (hK : 0<K) (hr : 1≤r) (ε : F₂) :
    Fintype.card (I.Vertex K ε)≤I.rectCoefficient K*m^2 := by
  rw [← Fintype.card_congr (I.rectVertexEquiv K hK hr ε),← I.rect_card K]
  exact Fintype.card_subtype_le _

 theorem spacedCount_lt_limit (K : ℕ) (ε : F₂) (v : I.Vertex K ε) :
    I.spacedCount K v.1+1≤I.slotLimit K := by
  have h := I.rectangle_code_le K v.1.val
  unfold spacedCount slotLimit
  nlinarith

 theorem slots_complete (K : ℕ) (hK : 0<K) (hr : 1≤r) (ε : F₂) (q : ℕ)
    (v : Marking.Slot (I.Vertex K ε) (fun v => I.spacedCount K v.1)) :
    ∃!u,I.slots K hK hr ε q u=some v :=
  Marking.decodeSlots_complete (I.rectVertexEquiv K hK hr ε) (I.slotLimit K) q
    (I.spacedCount_lt_limit K ε) v

end WLTime.Compression.ConsistencyData

namespace WLTime.Pebble
 theorem wins_transport_iff {K : ℕ} {A : Type uA} {B : Type uB} {A' : Type uA'} {B' : Type uB'}
    (G : SimpleGraph A) (H : SimpleGraph B) (G' : SimpleGraph A') (H' : SimpleGraph B')
    (f : A ≃ A') (g : B ≃ B')
    (hf : ∀x y,G.Adj x y ↔ G'.Adj (f x) (f y))
    (hg : ∀x y,H.Adj x y ↔ H'.Adj (g x) (g y)) :
    Wins G H (fun _ _ => True) (fun _ : Fin K => none) ↔
      Wins G' H' (fun _ _ => True) (fun _ : Fin K => none) := by
  constructor
  · intro h; simpa only [Position.map_none] using h.transport f g hf hg
  · intro h
    have h' := h.transport f.symm g.symm
      (fun x y => by simpa only [Equiv.apply_symm_apply] using (hf (f.symm x) (f.symm y)).symm)
      (fun x y => by simpa only [Equiv.apply_symm_apply] using (hg (g.symm x) (g.symm y)).symm)
    simpa only [Position.map_none] using h'
end WLTime.Pebble

namespace WLTime.Marking
variable {V : Type uV} {W : Type uW} {U : Type uU} [Fintype V] [Fintype W] [Fintype U]
variable (G : SimpleGraph V) (H : SimpleGraph W) (count : V → ℕ) (count' : W → ℕ)
 omit [Fintype V] [Fintype W] in
 theorem raw_wins_iff (a : U → Option (Slot V count)) (b : U → Option (Slot W count'))
    (ha : ∀ v,∃!u,a u=some v) (hb : ∀ v,∃!u,b u=some v)
    (hholes : Fintype.card {u // a u=none}=Fintype.card {u // b u=none}) (K : ℕ) :
    Pebble.Wins (rawGraph G a) (rawGraph H b) (fun _ _ => True) (fun _ : Fin K => none) ↔
      Pebble.Wins (graph G count (Fintype.card {u // a u=none}))
        (graph H count' (Fintype.card {u // a u=none})) (fun _ _ => True) (fun _ : Fin K => none) := by
  classical
  have h := Pebble.wins_transport_iff (K:=K) (rawGraph G a) (rawGraph H b)
    (graph G count _) (graph H count' _) (rawEquiv a ha) (rawEquiv b hb)
    (fun x y => (rawEquiv_adj G a ha x y).symm) (fun x y => (rawEquiv_adj H b hb x y).symm)
  have he := congrArg (fun q => Pebble.Wins (graph G count (Fintype.card {u // a u=none}))
    (graph H count' q) (fun _ _ => True) (fun _ : Fin K => none)) hholes.symm
  exact h.trans (iff_of_eq he)
end WLTime.Marking

namespace WLTime.Compression.ConsistencyData
variable {r m : ℕ} {P : Type uP} {E : Type uE} (I : ConsistencyData (r+1) m P E)
variable [Fintype P] [Fintype E] [Nonempty P]
open scoped Classical

 theorem spaced_wins_iff_ac (hr : 2≤r) (hm : 2 ≤ m) (q : ℕ) :
    Pebble.Wins (Marking.graph (I.valuationGraph (r+2) 0) (fun v => I.spacedCount (r+2) v.1) q)
      (Marking.graph (I.valuationGraph (r+2) 1) (fun v => I.spacedCount (r+2) v.1) q)
      (fun _ _ => True) (fun _ : Fin (r+2) => none) ↔ I.ArcConsistent := by
  classical
  constructor
  · intro h
    apply (I.colored_wins_iff_ac hr).mp
    exact Marking.wins_bases_spaced (I.valuationGraph (r+2) 0) (I.valuationGraph (r+2) 1)
      Sigma.fst Sigma.fst (fun v : I.Block (r+2) => rawCode (r+2) v.val)
      ((rawCode_injective (r+2)).comp Subtype.val_injective)
      (fun v => rawCode_pos (r+2) v.val) (I.baseEquiv (r+2) (by omega)) (fun _ => rfl)
      q (r+2) (I.rectCoefficient (r+2)*m^2) (I.card_bases_le_rectangle (r+2) (by omega) (by omega) 0)
      (I.two_le_card_base (r+2) hm) (by omega) h
  · intro h
    obtain ⟨Q⟩ := I.arcConsistent_iff.mp h
    exact (Marking.liftSystem Sigma.fst Sigma.fst (I.spacedCount (r+2)) q (r+2)
      (I.valuationSystem Q (r+2) (by omega) hr le_rfl)).wins_empty

 theorem rectangular_wins_iff_ac (hr : 2≤r) (hm : 2 ≤ m) (q : ℕ) :
    Pebble.Wins (I.rectangularGraph (r+2) (by omega) (by omega) 0 q)
      (I.rectangularGraph (r+2) (by omega) (by omega) 1 q)
      (fun _ _ => True) (fun _ : Fin (r+2) => none) ↔ I.ArcConsistent := by
  classical
  have hh := Marking.raw_holes_eq (I.baseEquiv (r+2) (by omega)) (fun _ => rfl)
    (I.slots (r+2) (by omega) (by omega) 0 q) (I.slots (r+2) (by omega) (by omega) 1 q)
    (I.slots_complete (r+2) (by omega) (by omega) 0 q) (I.slots_complete (r+2) (by omega) (by omega) 1 q)
  exact (Marking.raw_wins_iff _ _ _ _ _ _
    (I.slots_complete (r+2) (by omega) (by omega) 0 q)
    (I.slots_complete (r+2) (by omega) (by omega) 1 q) hh (r+2)).trans (I.spaced_wins_iff_ac hr hm _)

end WLTime.Compression.ConsistencyData

end OAI
end

section
-- module Solutions.OAIQW_WLTime.MatrixWriter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uV uW uT uS uJ uR uJ'

namespace WLTime.Enumeration
variable {V : Type uV} {W : Type uW}

 theorem Listing.length_eq_card [Fintype V] (l : Listing V) : l.items.length=Fintype.card V := by
  rw [← Fintype.card_fin l.items.length]
  exact Fintype.card_congr l.equiv
end WLTime.Enumeration

end OAI
end

section
-- module Solutions.OAIQW_WLTime.MatrixBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uJ uK uL uA

namespace WLTime.OneTape
variable (M : OneTape)
open CircuitEncoding

theorem bounded_acceptance (w : List Bool) (T : ℕ) :
    (M.run lineShift (M.initial w) T).state.val=1 ↔
      ∃ t ≤ T,(M.toTM.run w t).state.val=1 := by
  have he := congrArg (fun C : M.toTM.Config => C.state.val) (M.embed_run w T)
  change (M.run lineShift (M.initial w) T).state.val=(M.toTM.run w T).state.val at he
  rw [he]
  constructor
  · intro h; exact ⟨T,le_rfl,h⟩
  · rintro ⟨t,ht,h⟩
    rw [M.toTM.run_frozen w (Or.inl h) ht]
    exact h

theorem product_bounded (w : List Bool) (hm : 0<w.length) (d q : ℕ)
    (hL : 2*(w.length^d-1)+w.length+2<w.length^(q+1)) :
    (∀ g, (BoxTableau.schematic M.localRule (M.inputCell w) M.blankCell M.letterAccepting :
      Schematic (d+(q+1)) w.length _ _ _ _).expand.test g=true →
      ¬(BoxTableau.schematic M.localRule (M.inputCell w) M.blankCell M.letterAccepting).expand.TrueAt g) ↔
      ¬∃ t ≤ w.length^d-1,(M.toTM.run w t).state.val=1 := by
  let : NeZero (w.length^(q+1)) := ⟨Nat.ne_of_gt (Nat.pow_pos hm)⟩
  rw [BoxTableau.local_equivalence M.localRule (M.inputCell w) M.blankCell M.letterAccepting hm]
  rw [← M.bounded_acceptance w (w.length^d-1)]
  have hr := M.ring_run_agrees w (w.length^d-1) (w.length^(q+1)) hL (w.length^d-1) le_rfl
  rw [← hr.1,← M.accepting_snapshot, M.run_snapshot]
  simp only [not_exists]
  constructor
  · intro h j
    let f : Fin (w.length^(q+1)) ≃ ZMod (w.length^(q+1)) := (ZMod.finEquiv _).toEquiv
    have he := Tableau.run_reindex M.localRule (Digits.inc _) (ringShift _) f
      (BoxTableau.initialRing (M.inputCell w) M.blankCell) (M.snapshot (M.ringInitial _ w))
      Digits.finEquiv_shift (M.ring_initial_digits w hm q) (w.length^d-1) (f.symm j)
    exact (by simpa only [f.apply_symm_apply] using he) ▸ h (f.symm j)
  · intro h j
    have he := Tableau.run_reindex M.localRule (Digits.inc _) (ringShift _) (ZMod.finEquiv _).toEquiv
      (BoxTableau.initialRing (M.inputCell w) M.blankCell) (M.snapshot (M.ringInitial _ w))
      Digits.finEquiv_shift (M.ring_initial_digits w hm q) (w.length^d-1) j
    rw [he]
    exact h _

end WLTime.OneTape

namespace WLTime.OneTape.Symbolic
open CircuitEncoding NatCode Compression Enumeration
variable (M : OneTape) (d q : ℕ)
open scoped Classical

 theorem listing_length (w : List Bool) (pad : ℕ) :
    (listing M d q (d+q+2) w pad).items.length=baseOrder M d q w.length+pad := by
  rw [Enumeration.Listing.length_eq_card]
  simp only [RawVertex,Enumeration.Vertex,Fintype.card_option,Fintype.card_sum,
    Fintype.card_prod,Fintype.card_fin]
  have hL : (instanceData M d q w).slotLimit (d+q+2)=
      (coefficient M d q (d+q+2)*w.length^2+1)^2+1 := rfl
  rw [hL]
  unfold baseOrder coefficient ConsistencyData.rectCoefficient
  simp only [ConsistencyData.BlockTag,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  ring_nf

 theorem pairGraph_diameter (hr : 2≤d+q) (w : List Bool) (pad : ℕ) (ε : F₂) :
    (pairGraph M d q hr w pad ε).diameterTwo := by
  apply Graph.ofSimple_diameter
  · rw [listing_length]; dsimp [baseOrder]; omega
  · exact Marking.raw_diameter _ _

 theorem pairGraph_correct (hr : 2≤d+q) (w : List Bool) (hm : 2≤w.length) (pad : ℕ)
    (hL : 2*(w.length^d-1)+w.length+2<w.length^(q+1)) :
    (Equivalent .joint (d+q+1) (pairGraph M d q hr w pad 0) (pairGraph M d q hr w pad 1) ↔
      ¬∃t≤w.length^d-1,(M.toTM.run w t).state.val=1) ∧
    (Equivalent .separate (d+q+2) (pairGraph M d q hr w pad 0) (pairGraph M d q hr w pad 1) ↔
      ¬∃t≤w.length^d-1,(M.toTM.run w t).state.val=1) := by
  have hn : 0<(listing M d q (d+q+2) w pad).items.length := by
    rw [listing_length]; dsimp [baseOrder]; omega
  let : Nonempty (Node M d q) := ⟨.dummy⟩
  have he : Wins (pairGraph M d q hr w pad 0) (pairGraph M d q hr w pad 1)
      (fun _ : Fin (d+q+2) => none) ↔ (instanceData M d q w).ArcConsistent :=
    (wins_ofSimple_iff _ _ _ _).trans ((instanceData M d q w).rectangular_wins_iff_ac hr hm pad)
  have ha : (instanceData M d q w).ArcConsistent ↔
      ¬∃t≤w.length^d-1,(M.toTM.run w t).state.val=1 :=
    (schema M d q w).consistency_iff_tests_false.trans (M.product_bounded w (by omega) d q hL)
  exact ⟨(joint_equivalent_iff_wins hn (by omega)).trans (he.trans ha),
    (separate_equivalent_iff_wins hn).trans (he.trans ha)⟩

end WLTime.OneTape.Symbolic

namespace WLTime.TypedStack.Code
variable {K : Type uK} {L : Type uL} {A : Type uA}
 theorem card_state (p : Code K A) : Fintype.card p.State=p.controlSize := by
  induction p with
  | skip => exact Fintype.card_unique
  | push | pushDyn | pop => exact Fintype.card_fin 2
  | seq p q hp hq => simpa only [State,Fintype.card_sum,controlSize] using congrArg₂ (·+·) hp hq
  | branch t p q hp hq => simpa only [State,Fintype.card_sum,Fintype.card_unique,controlSize,Nat.add_assoc] using congrArg (1+·) (congrArg₂ (·+·) hp hq)
  | loop t p hp => simpa only [State,Fintype.card_sum,Fintype.card_unique,controlSize] using congrArg (1+·) hp
end WLTime.TypedStack.Code

namespace WLTime.TypedStack.Program
variable {K : Type uK} [DecidableEq K]

 omit [DecidableEq K] in
 theorem loadDigits_scratch (a : K) (ds : List ℕ) : (loadDigits a ds).scratch≤2 := by
  induction ds with
  | nil => exact Nat.zero_le _
  | cons b bs ih => simpa only [loadDigits,seqShared,doubleUnary_scratch,pushes_scratch,max_zero] using max_le ih le_rfl
 omit [DecidableEq K] in
 theorem loadDigits_size (a : K) (ds : List ℕ) (hd : ∀b∈ds,b<2) :
    (loadDigits a ds).code.controlSize≤((doubleUnary a).code.controlSize+3)*ds.length+1 := by
  induction ds with
  | nil => rfl
  | cons b bs ih =>
    have hb := hd b (by simp)
    have hi := ih (fun c hc => hd c (by simp [hc]))
    simp only [loadDigits,seqShared_size,pushes_size,UnaryPrograms.numeral_length,List.length_cons]
    rw [Nat.mul_succ]
    omega
 omit [DecidableEq K] in
 theorem loadNat_size (a : K) (n : ℕ) :
    (loadNat a n).code.controlSize≤((doubleUnary a).code.controlSize+3)*(Nat.digits 2 n).length+1 := by
  exact loadDigits_size a _ (fun b hb => Nat.digits_lt_base (by decide) hb)
end WLTime.TypedStack.Program

end OAI
end

section
-- module Solutions.OAIQW_WLTime.TapePair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uK uA uB uL uS uT

namespace WLTime.TapePair
variable {A : Type uA}

 theorem getD_tail (s : List A) (n : ℕ) (blank : A) :
    s.tail.getD n blank=s.getD (n+1) blank := by cases s <;> rfl

theorem contents_moveWrite (blank x : A) (d : Move) (s : Tape A) (z : ℤ) :
    contents blank (moveWrite blank x d s) z =
      if z+d.displacement=0 then x else contents blank s (z+d.displacement) := by
  cases d with
  | stay =>
    simp only [Move.displacement,add_zero,moveWrite,contents]
    by_cases hz : z<0
    · have h0 : z≠0 := by omega
      simp only [hz,ite_true,h0,ite_false]
    · by_cases h0 : z=0
      · subst z; simp
      · have he : z.toNat=(z-1).toNat+1 := by omega
        simp only [hz,ite_false,h0,he,List.getD_cons_succ,getD_tail]
  | right =>
    simp only [Move.displacement,moveWrite,contents]
    by_cases hz : z<0
    · by_cases he : z+1=0
      · have hz' : (-z-1).toNat=0 := by omega
        simp only [hz,ite_true,he,hz',List.getD_cons_zero]
      · have hz' : z+1<0 := by omega
        have ht : (-z-1).toNat=(-(z+1)-1).toNat+1 := by omega
        simp only [hz,ite_true,he,ite_false,hz',ht,List.getD_cons_succ]
    · have hz' : ¬z+1<0 := by omega
      have he : z+1≠0 := by omega
      have ht : (z+1).toNat=z.toNat+1 := by omega
      simp only [hz,ite_false,he,hz',getD_tail,ht]
  | left =>
    simp only [Move.displacement,moveWrite,contents]
    by_cases hz : z<0
    · have hz' : z+ -1<0 := by omega
      have he : z+ -1≠0 := by omega
      have ht : (-(z+ -1)-1).toNat=(-z-1).toNat+1 := by omega
      simp only [hz,ite_true,he,ite_false,hz',getD_tail,ht]
    · by_cases h0 : z=0
      · subst z
        cases s.left <;> rfl
      · by_cases h1 : z=1
        · subst z
          simp
        · have hz' : ¬z+ -1<0 := by omega
          have he : z+ -1≠0 := by omega
          have ht : z.toNat=((z+ -1).toNat-1)+1+1 := by omega
          have hs : (z+ -1).toNat-1+1=(z+ -1).toNat := by omega
          simp only [hz,ite_false,he,hz']
          calc
            (s.left.headD blank::x::s.right.tail).getD z.toNat blank =
                s.right.tail.getD ((z+ -1).toNat-1) blank := by
              rw [ht,List.getD_cons_succ,List.getD_cons_succ]
            _ = s.right.getD (z+ -1).toNat blank := by rw [getD_tail,hs]

end WLTime.TapePair

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Consumer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uK uA uB

namespace WLTime.StackMachine.Machine
variable (K a q : ℕ)
 theorem decode_control (c : SweepControl K a q) : decodeControl K a q (controlCode K a q c)=some c := by
  cases c with
  | seek p => cases p <;> rfl
  | _ => rfl
 theorem control_bound : Fintype.card (SweepControl K a q)≤14*(K+1)*(a+1)*(q+1)*(a+1)^K := by
  have hi : Function.Injective (controlCode K a q) := by
    intro x y h
    apply Option.some.inj
    rw [←decode_control K a q x,←decode_control K a q y,h]
  have h := Fintype.card_le_of_injective _ hi
  simp only [ControlCode,Fintype.card_prod,Fintype.card_fin,Fintype.card_option,Fintype.card_fun] at h
  convert h using 1
  ring_nf

 theorem compile_states_bound (M : StackMachine.Machine) :
    M.oneTape.states≤3+14*(M.count+1)*(M.alphabet+1)*(M.states+1)*(M.alphabet+1)^M.count :=
  Nat.add_le_add_left (control_bound _ _ _) 3
 theorem compile_symbols (M : StackMachine.Machine) :
    M.oneTape.symbols=3+2*(M.alphabet+1)^M.count := by
  change 3+Fintype.card (Bool × (Fin M.count → Option (Fin M.alphabet)))=_
  simp only [Fintype.card_prod,Fintype.card_bool,Fintype.card_fun,Fintype.card_option,Fintype.card_fin]
end WLTime.StackMachine.Machine

namespace WLTime.TypedStack.Code
variable {K : Type uK} {A : Type uA} {B : Type uB}
 theorem mapLetters_controlSize (f : A → B) (g : B → A) (p : Code K A) :
    (p.mapLetters f g).controlSize=p.controlSize := by
  induction p <;> simp_all [mapLetters,controlSize]
end WLTime.TypedStack.Code

namespace WLTime.OneTape.Symbolic.FullWriter
open NatCode TypedStack UnaryPrograms
open scoped Classical
variable (U : OneTape) (d q : ℕ)
 theorem scratch_le (n : ℕ) : (program U d q n).scratch ≤ scratchBound U d q := by
  have h := Program.loadDigits_scratch Reg.order (Nat.digits 2 n)
  simp only [program,Program.seqShared,Program.pushes_scratch,scratchBound,Program.loadNat]
  omega
 theorem syntax_le (n : ℕ) : (program U d q n).code.controlSize ≤ syntaxBound U d q*((Nat.digits 2 n).length+1) := by
  have h := Program.loadNat_size Reg.order n
  simp only [program,Program.seqShared_size,Program.pushes_size,List.length_reverse,encodeNat_length]
  have he := Nat.le_mul_of_pos_right
    ((Program.countLength Reg.word Reg.len).code.controlSize+
      ((body U d q).compile rho Reg.word Reg.output).code.controlSize+4)
    (show 0 < (Nat.digits 2 n).length+1 by omega)
  dsimp only [syntaxBound]
  nlinarith

 theorem input_length (n : ℕ) (w : List Bool) (hr : 2 ≤ d+q) (hn : baseOrder U d q w.length ≤ n) :
    (encodePair (pairGraph U d q hr w (n-baseOrder U d q w.length) 0)
      (pairGraph U d q hr w (n-baseOrder U d q w.length) 1)).length=
      2*(Nat.digits 2 n).length+1+2*n^2 := by
  have hl : (listing U d q (d+q+2) w (n-baseOrder U d q w.length)).items.length=n := by
    rw [listing_length,Nat.add_sub_of_le hn]
  have hbits {v : ℕ} (G : Graph v) : (matrixBits G).length=v^2 := by
    simp [matrixBits,List.length_flatten,Function.comp_def,pow_two]
  simp only [encodePair,List.length_append,encodeNat_length,hbits,hl]
  omega

end WLTime.OneTape.Symbolic.FullWriter

namespace WLTime.TMConsumer
open TypedStack
variable {K : Type uK} [DecidableEq K] [Fintype K] (M : TM)
 omit [DecidableEq K] [Fintype K] in
 theorem prelude_size (c : Code K Bool) (output : K) :
    (preludeCode M c output).controlSize=c.controlSize+5 := by
  simp only [preludeCode,Code.controlSize,Code.relabel_controlSize,Code.mapLetters_controlSize,
    Code.transfer]
 omit [DecidableEq K] [Fintype K] in
 theorem state_card (c : Code K Bool) (output : K) :
    Fintype.card (State M c output)=c.controlSize+5+Fintype.card (TMStack.State M) := by
  rw [Fintype.card_sum,Code.card_state,prelude_size]
end WLTime.TMConsumer

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Universal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLTime.OneTape.Symbolic.FullWriter
open TypedStack
open scoped Classical
variable (U : OneTape) (d q : ℕ) (A : TM)

 theorem consumer_alphabet (n : ℕ) : (consumer U d q A n).symbols ≤ alphabetBound U d q A := by
  unfold consumer TMConsumer.oneTape
  rw [StackMachine.Machine.compile_symbols]
  change 3+2*((2+Fintype.card (Fin A.symbols))+1)^
    Fintype.card (TMConsumer.Reg A (Fin (program U d q n).scratch ⊕ Reg)) ≤ _
  simp only [Fintype.card_fin,Fintype.card_sum,card_reg,TMConsumer.Reg,Fintype.card_prod,Fintype.card_bool]
  dsimp only [alphabetBound,tapesBound]
  have hs := scratch_le U d q n
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  rw [show 2+A.symbols+1=A.symbols+3 by omega]
  apply Nat.pow_le_pow_right (by omega)
  omega

 theorem consumer_states (n : ℕ) :
    (consumer U d q A n).states ≤ statesBound U d q A*((Nat.digits 2 n).length+1) := by
  have h := StackMachine.Machine.compile_states_bound
    (TMConsumer.machine A (program U d q n).code (.inr Reg.word) (.inr Reg.output) not).compile
  change (consumer U d q A n).states ≤ 3+14*(Fintype.card (TMConsumer.Reg A (Fin (program U d q n).scratch ⊕ Reg))+1)*
    (2+Fintype.card (Fin A.symbols)+1)*
      (Fintype.card (TMConsumer.State A (program U d q n).code (.inr Reg.output))+1)*
      (2+Fintype.card (Fin A.symbols)+1)^Fintype.card (TMConsumer.Reg A (Fin (program U d q n).scratch ⊕ Reg)) at h
  rw [TMConsumer.state_card] at h
  simp only [TMConsumer.Reg,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,card_reg,Fintype.card_bool] at h
  have hK : (program U d q n).scratch+4+A.tapes*2 ≤ tapesBound U d q A := by
    dsimp [tapesBound]; have hs := scratch_le U d q n; omega
  have hq : (program U d q n).code.controlSize+5+Fintype.card (TMStack.State A)+1 ≤
      (syntaxBound U d q+6+Fintype.card (TMStack.State A))*((Nat.digits 2 n).length+1) := by
    have hs := syntax_le U d q n
    nlinarith
  simp only [TMStack.State,Fintype.card_sum,Fintype.card_fin] at hq
  have hp : (2+A.symbols+1)^((program U d q n).scratch+4+A.tapes*2) ≤ (A.symbols+3)^tapesBound U d q A := by
    rw [show 2+A.symbols+1=A.symbols+3 by omega]
    exact Nat.pow_le_pow_right (by omega) hK
  calc
    _  ≤  _ := h
    _  ≤  3+14*(tapesBound U d q A+1)*(A.symbols+3)*
      ((syntaxBound U d q+6+Fintype.card (TMStack.State A))*((Nat.digits 2 n).length+1))*(A.symbols+3)^tapesBound U d q A := by
      have ht := Nat.mul_le_mul_right (A.symbols+3) (Nat.mul_le_mul_left 14 (Nat.add_le_add_right hK 1))
      rw [show 2+A.symbols+1=A.symbols+3 by omega] at hp ⊢
      simpa only [TMStack.State,Fintype.card_sum,Fintype.card_fin] using
        Nat.add_le_add_left (Nat.mul_le_mul (Nat.mul_le_mul ht hq) hp) 3
    _  ≤  statesBound U d q A*((Nat.digits 2 n).length+1) := by
      dsimp only [statesBound]
      nlinarith
end WLTime.OneTape.Symbolic.FullWriter

namespace WLTime.Diagonal

 theorem moveCode_lt (d : Move) : moveCode d<3 := by cases d <;> decide

 theorem raw_valid (M : OneTape) : (raw M).Valid := by
  refine ⟨M.states_ge,M.symbols_ge,?_,?_⟩
  · simp [raw]
  · intro e he
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
    exact ⟨(M.transition _ _).1.isLt,(M.transition _ _).2.1.isLt,moveCode_lt _⟩

 theorem bounded_accepts_iff (D : OneTape) (w : List Bool) (B : ℕ)
    (hh : D.toTM.halts w) (ht : D.toTM.time w ≤ B) :
    (∃ t ≤ B,(D.toTM.run w t).state.val=1) ↔ D.toTM.accepts w := by
  constructor
  · rintro ⟨t,_,h⟩; exact ⟨t,h⟩
  · intro ha
    exact ⟨D.toTM.time w,ht,(D.toTM.accepts_iff_at_halt w (D.toTM.time_halted w hh)).mp ha⟩

end WLTime.Diagonal

namespace WLTime.Universal
open UnaryPrograms

theorem unary_tile (n : ℕ) : Diagonal.unary n=numeral n++[false] := rfl

@[simp] theorem tailField_entry (e : Diagonal.Entry) (xs : List Bool) :
    tailField^[3] (Diagonal.entryBits e++xs)=xs := by
  simp only [Function.iterate_succ_apply,Function.iterate_zero,Function.id_def,
    Diagonal.entryBits,unary_tile,List.append_assoc,List.cons_append,List.nil_append,
    tailField,scan_numeral]

theorem tailField_table_drop (es : List Diagonal.Entry) (n : ℕ) (hn : n≤es.length)
    (xs : List Bool) :
    tailField^[3*n] (Diagonal.tableBits es++xs)=Diagonal.tableBits (es.drop n)++xs := by
  induction n generalizing es with
  | zero => simp
  | succ n ih =>
    cases es with
    | nil => simp at hn
    | cons e es =>
      have hn' : n≤es.length := by simpa using hn
      rw [Nat.mul_succ,Function.iterate_add_apply]
      change tailField^[3*n] (tailField^[3] ((Diagonal.entryBits e++Diagonal.tableBits es)++xs))=_
      rw [List.append_assoc,tailField_entry,ih es hn']
      rfl

end WLTime.Universal

namespace WLTime.Universal
open TypedStack UnaryPrograms

open Reg

@[simp] theorem scan_entry (e : Diagonal.Entry) (xs : List Bool) :
    scan (Diagonal.entryBits e++xs)=(e.1,Diagonal.unary e.2.1++Diagonal.unary e.2.2++xs) := by
  simp only [Diagonal.entryBits,List.append_assoc,unary_tile,List.cons_append,List.nil_append,
    scan_numeral]

@[simp] theorem scan_unary (n : ℕ) (xs : List Bool) : scan (Diagonal.unary n++xs)=(n,xs) := by
  simp only [unary_tile,List.append_assoc,List.cons_append,List.nil_append,scan_numeral]

theorem table_at (es : List Diagonal.Entry) (i : ℕ) (hi : i<es.length) :
    tailField^[3*i] (Diagonal.tableBits es)=
      Diagonal.entryBits es[i]++Diagonal.tableBits (es.drop (i+1)) := by
  have he := tailField_table_drop es i (by omega) []
  simp only [List.append_nil] at he
  rw [he,List.drop_eq_getElem_cons hi]
  rfl

theorem lookup_exec (es : List Diagonal.Entry) (q g x : ℕ)
    (hi : q*g+x<es.length) (s : Stacks Reg Bool)
    (ht : s tab=Diagonal.tableBits es) (hg : s alpha=numeral g)
    (hq : s state=numeral q) (hx : s cur=numeral x)
    (hs : s search=[]) (hn : s index=[]) (hw : s write=[]) (hd : s dir=[]) :
    ∃ t≤(q*g+x+1)*(30*(Diagonal.tableBits es).length+30*q+30*g+30*x+100),
      lookup.Exec s t
        (Function.update (Function.update (Function.update s state (numeral es[q*g+x].1))
          write (numeral es[q*g+x].2.1)) dir (numeral es[q*g+x].2.2)) := by
  let e := es[q*g+x]
  let tail := Diagonal.tableBits (es.drop (q*g+x+1))
  let a := Function.update s search (Diagonal.tableBits es)
  let b := Function.update a index (numeral (q*g))
  let c := Function.update a index (numeral (q*g+x))
  let d := Function.update c search (Diagonal.entryBits e++tail)
  let f := Function.update d state []
  let j := Function.update (Function.update f search (Diagonal.unary e.2.1++Diagonal.unary e.2.2++tail))
    state (numeral e.1)
  let k := Function.update (Function.update j search (Diagonal.unary e.2.2++tail)) write (numeral e.2.1)
  let l := Function.update (Function.update k search tail) dir (numeral e.2.2)
  have h1 : (Program.copy tab search).Exec s (12*(Diagonal.tableBits es).length+2) a := by
    simpa [a,ht,hs] using Program.copy_exec tab search (by decide) s
  obtain ⟨t2,ht2,h2⟩ := mulAdd_exec state alpha index (by decide) a q g
    (by simp [a,hq]) (by simp [a,hg])
  replace h2 : (mulAdd state alpha index).Exec a t2 b := by simpa [b,a,hn] using h2
  have h3 : (Program.copy cur index).Exec b (12*x+2) c := by
    have hh := Program.copy_exec cur index (by decide) b
    simpa [b,c,a,hx,hn,←numeral_add,Nat.add_comm x] using hh
  obtain ⟨t4,ht4,h4⟩ := seek_exec search index (q*g+x) c (by simp [c])
  have hc : c search=Diagonal.tableBits es := by simp [c,a]
  rw [hc,table_at es _ hi] at h4
  change (seek search index).Exec c t4 d at h4
  have h5 : (Program.clear state).Exec d (3*q+1) f := by
    simpa [d,c,a,hq] using Program.clear_exec state d
  have h6 : (Program.read search state).Exec f (5*e.1+3) j := by
    simpa [f,d,j] using Program.read_exec search state (by decide) f
  have h7 : (Program.read search write).Exec j (5*e.2.1+3) k := by
    simpa [k,j,f,d,c,a,hw] using Program.read_exec search write (by decide) j
  have h8 : (Program.read search dir).Exec k (5*e.2.2+3) l := by
    simpa [l,k,j,f,d,c,a,hd] using Program.read_exec search dir (by decide) k
  have h9 := Program.clear_exec search l
  have h10 := Program.clear_exec index (Function.update l search [])
  have he := Program.seq_exec h1 (Program.seq_exec h2 (Program.seq_exec h3
    (Program.seq_exec h4 (Program.seq_exec h5 (Program.seq_exec h6 (Program.seq_exec h7
      (Program.seq_exec h8 (Program.seq_exec h9 h10))))))))
  have hout : Function.update (Function.update l search []) index []=
        Function.update (Function.update (Function.update s state (numeral e.1))
          write (numeral e.2.1)) dir (numeral e.2.2) := by
    funext r; cases r <;> simp [l,k,j,f,d,c,a,hs,hn]
  rw [hout] at he
  refine ⟨_,?_,he⟩
  have hlen := tailField_iterate_le (3*(q*g+x)) (Diagonal.tableBits es)
  rw [table_at es _ hi] at hlen
  have he_len : (Diagonal.entryBits e).length=e.1+e.2.1+e.2.2+3 := by
    simp [Diagonal.entryBits,unary_tile]; omega
  change (Diagonal.entryBits e++tail).length≤(Diagonal.tableBits es).length at hlen
  rw [List.length_append,he_len] at hlen
  rw [hc] at ht4
  simp only [l,k,j,f,d,c,a]
  simp only [Function.update_of_ne (by decide : search≠dir),Function.update_self,
    Function.update_of_ne (by decide : index≠search),
    Function.update_of_ne (by decide : index≠dir),
    Function.update_of_ne (by decide : index≠write),
    Function.update_of_ne (by decide : index≠state),numeral_length]
  nlinarith

end WLTime.Universal

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Interpreter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uK uC

namespace WLTime.Universal
open TypedStack UnaryPrograms Reg

theorem motionLeft_exec (s : Stacks Reg Bool) (L R : List ℕ) (x : ℕ)
    (hl : s left=fields L) (hr : s right=fields R)
    (hx : s write=numeral x) (hc : s cur=[]) :
    motionLeft.Exec s (12*x+20*L.headD 0+12)
      (Function.update (Function.update s left (fields L.tail)) right (fields (L.headD 0::x::R))) := by
  let a := Function.update s right (fields (x::R))
  let b := Function.update (Function.update a left (fields L.tail)) cur (numeral (L.headD 0))
  let c := Function.update b right (fields (L.headD 0::x::R))
  have h1 : (prependRecord write right).Exec s (12*x+4) a := by
    simpa [a,hr] using prependRecord_exec write right (by decide) x s hx
  have h2 : (Program.read left cur).Exec a (5*L.headD 0+3) b := by
    simpa [b,a,hl,hc] using Program.read_exec left cur (by decide) a
  have h3 : (prependRecord cur right).Exec b (12*L.headD 0+4) c := by
    simpa [c,b,a] using prependRecord_exec cur right (by decide) (L.headD 0) b (by simp [b])
  have h4 := Program.clear_exec cur c
  have he := Program.seq_exec h1 (Program.seq_exec h2 (Program.seq_exec h3 h4))
  have hout : Function.update c cur []=
      Function.update (Function.update s left (fields L.tail)) right (fields (L.headD 0::x::R)) := by
    funext r; cases r <;> simp [c,b,a,hc]
  rw [hout] at he
  convert he using 1 <;> try rfl
  simp [c,b]
  omega

theorem motion_exec (s : Stacks Reg Bool) (L R : List ℕ) (x : ℕ) (d : Move)
    (hl : s left=fields L) (hr : s right=fields R)
    (hx : s write=numeral x) (hc : s cur=[])
    (hd : s dir=numeral (Diagonal.moveCode d)) :
    ∃t≤12*x+20*L.headD 0+17,motion.Exec s t
      (Function.update (Function.update (Function.update s dir (numeral (movedDir d)))
        left (fields (shiftTape x d L R).1)) right (fields (shiftTape x d L R).2)) := by
  cases d with
  | left =>
    have he := Program.branch_false (p:=Program.seq (Program.pop dir) (Program.branch (UnaryPrograms.isTrue dir)
      (prependRecord write left) (prependRecord write right)))
      (test:=UnaryPrograms.isTrue dir) (by simp [UnaryPrograms.isTrue,tops,hd,Diagonal.moveCode,numeral])
      (motionLeft_exec s L R x hl hr hx hc)
    refine ⟨12*x+20*L.headD 0+13,by omega,?_⟩
    convert he using 1
    all_goals try rfl
    funext r; cases r <;> simp [shiftTape,movedDir,hd,Diagonal.moveCode,numeral]
  | stay =>
    let a := Function.update s dir []
    have h1 : (Program.pop dir).Exec s 2 a := by
      simpa [a,hd,Diagonal.moveCode,numeral] using Program.pop_exec dir s
    have h2 := prependRecord_exec write right (by decide) x a (by simp [a,hx])
    have h3 := Program.branch_false (p:=prependRecord write left) (test:=UnaryPrograms.isTrue dir)
      (by simp [UnaryPrograms.isTrue,tops,a]) h2
    have he := Program.branch_true (q:=motionLeft) (test:=UnaryPrograms.isTrue dir)
      (by simp [UnaryPrograms.isTrue,tops,hd,Diagonal.moveCode,numeral]) (Program.seq_exec h1 h3)
    refine ⟨12*x+8,by omega,?_⟩
    convert he using 1
    all_goals try rfl
    all_goals try omega
    funext r; cases r <;> simp [a,shiftTape,movedDir,hl,hr,numeral]
  | right =>
    let a := Function.update s dir (numeral 1)
    have h1 : (Program.pop dir).Exec s 2 a := by
      simpa [a,hd,Diagonal.moveCode,numeral] using Program.pop_exec dir s
    have h2 := prependRecord_exec write left (by decide) x a (by simp [a,hx])
    have h3 := Program.branch_true (q:=prependRecord write right) (test:=UnaryPrograms.isTrue dir)
      (by simp [UnaryPrograms.isTrue,tops,a,numeral]) h2
    have he := Program.branch_true (q:=motionLeft) (test:=UnaryPrograms.isTrue dir)
      (by simp [UnaryPrograms.isTrue,tops,hd,Diagonal.moveCode,numeral]) (Program.seq_exec h1 h3)
    refine ⟨12*x+8,by omega,?_⟩
    convert he using 1
    all_goals try rfl
    all_goals try omega
    funext r; cases r <;> simp [a,shiftTape,movedDir,hl,hr,numeral]

end WLTime.Universal

namespace WLTime.Universal
open TypedStack UnaryPrograms Reg

theorem flagTest_exec (s : Stacks Reg Bool) (q : ℕ) (ht : s temp=numeral q) (hh : s halt=[]) :
    ∃t≤10,flagTest.Exec s t
      (Function.update (Function.update s temp (numeral (q-2))) halt (haltFlag q)) := by
  cases q with
  | zero =>
    have he := Program.branch_false (p:=Program.seq (Program.pop temp) (Program.branch (UnaryPrograms.isTrue temp)
      (Program.seq (Program.pop temp) (Program.branch (UnaryPrograms.isTrue temp) Program.skip (Program.push halt true)))
      (Program.push halt false))) (test:=UnaryPrograms.isTrue temp)
      (by simp [UnaryPrograms.isTrue,tops,ht,numeral]) (Program.skip_exec s)
    refine ⟨2,by omega,?_⟩
    convert he using 1 <;> try rfl
    funext r; cases r <;> simp [haltFlag,←ht,hh]
  | succ q =>
    let a := Function.update s temp (numeral q)
    have hp : (Program.pop temp).Exec s 2 a := by
      simpa [a,ht,numeral,List.replicate_succ] using Program.pop_exec temp s
    have htop : UnaryPrograms.isTrue temp (tops s)=true := by simp [UnaryPrograms.isTrue,tops,ht,numeral,List.replicate_succ]
    cases q with
    | zero =>
      have he := Program.branch_true (q:=Program.skip) htop (Program.seq_exec hp
        (Program.branch_false (p:=Program.seq (Program.pop temp)
          (Program.branch (UnaryPrograms.isTrue temp) Program.skip (Program.push halt true))) (test:=UnaryPrograms.isTrue temp)
          (by simp [UnaryPrograms.isTrue,tops,a,numeral]) (Program.push_exec halt false a)))
      refine ⟨6,by omega,?_⟩
      convert he using 1 <;> try rfl
      funext r; cases r <;> simp [a,haltFlag,hh]
    | succ q =>
      let b := Function.update s temp (numeral q)
      have hp' : (Program.pop temp).Exec a 2 b := by
        simpa [a,b,numeral,List.replicate_succ] using Program.pop_exec temp a
      have ht' : UnaryPrograms.isTrue temp (tops a)=true := by simp [UnaryPrograms.isTrue,tops,a,numeral,List.replicate_succ]
      cases q with
      | zero =>
        have he := Program.branch_true (q:=Program.skip) htop (Program.seq_exec hp
          (Program.branch_true (q:=Program.push halt false) ht' (Program.seq_exec hp'
            (Program.branch_false (p:=Program.skip) (test:=UnaryPrograms.isTrue temp)
              (by simp [UnaryPrograms.isTrue,tops,b,numeral]) (Program.push_exec halt true b)))))
        refine ⟨9,by omega,?_⟩
        convert he using 1 <;> try rfl
        funext r; cases r <;> simp [b,haltFlag,hh]
      | succ q =>
        have he := Program.branch_true (q:=Program.skip) htop (Program.seq_exec hp
          (Program.branch_true (q:=Program.push halt false) ht' (Program.seq_exec hp'
            (Program.branch_true (q:=Program.push halt true) (test:=UnaryPrograms.isTrue temp)
              (by simp [UnaryPrograms.isTrue,tops,b,numeral,List.replicate_succ]) (Program.skip_exec b)))))
        refine ⟨8,by omega,?_⟩
        convert he using 1 <;> try rfl
        funext r; cases r <;> simp [b,haltFlag,hh]

theorem flagState_exec (s : Stacks Reg Bool) (q : ℕ)
    (hq : s state=numeral q) (ht : s temp=[]) (hh : s halt=[]) :
    ∃t≤15*q+13,flagState.Exec s t (Function.update s halt (haltFlag q)) := by
  let a := Function.update s temp (numeral q)
  have h1 : (Program.copy state temp).Exec s (12*q+2) a := by
    simpa [a,hq,ht] using Program.copy_exec state temp (by decide) s
  obtain ⟨t,htime,h2⟩ := flagTest_exec a q (by simp [a]) (by simp [a,hh])
  have h3 := Program.clear_exec temp (Function.update (Function.update a temp (numeral (q-2))) halt (haltFlag q))
  have he := Program.seq_exec h1 (Program.seq_exec h2 h3)
  have hout : Function.update (Function.update (Function.update a temp (numeral (q-2))) halt (haltFlag q)) temp []=
      Function.update s halt (haltFlag q) := by
    funext r; cases r <;> simp [a,ht]
  rw [hout] at he
  refine ⟨_,?_,he⟩
  simp only [Function.update_of_ne (by decide : temp≠halt),Function.update_self,numeral_length]
  omega

end WLTime.Universal

namespace WLTime.Universal
open TypedStack UnaryPrograms Reg

theorem activeStep_exec (M : OneTape) (q : Fin M.states) (T : TapePair.Tape (Fin M.symbols)) (m : ℕ)
    (hq1 : q.val≠1) (hq2 : q.val≠2) :
    ∃t<stepBound M,activeStep.Exec (store M q T m) t
      (store M (nextState M q T) (nextTape M q T) m) := by
  let s := store M q T m
  let x := T.right.headD (zeroSymbol M)
  let p := M.transition q x
  let L := T.left.map Fin.val
  let R := T.right.tail.map Fin.val
  let a := Function.update (Function.update s right (fields R)) cur (numeral x.val)
  let b := Function.update (Function.update (Function.update a state (numeral p.1.val))
      write (numeral p.2.1.val)) dir (numeral (Diagonal.moveCode p.2.2))
  let c := Function.update b cur []
  let d := Function.update (Function.update (Function.update c dir (numeral (movedDir p.2.2)))
    left (fields (shiftTape p.2.1.val p.2.2 L R).1)) right (fields (shiftTape p.2.1.val p.2.2 L R).2)
  let e := Function.update d write []
  let f := Function.update e dir []
  have h1 : (Program.read right cur).Exec s (5*x.val+3) a := by
    simpa only [s,store,fields_head,fields_tail,map_head_zero,a,R,x,Function.update_self,
      List.map_tail,List.append_nil] using Program.read_exec right cur (by decide) s
  have hi : q.val*M.symbols+x.val<(Diagonal.raw M).table.length := by
    simp only [Diagonal.raw,List.length_ofFn]
    have hq := q.isLt
    have hx := x.isLt
    nlinarith
  obtain ⟨t2,ht2,h2⟩ := lookup_exec (Diagonal.raw M).table q.val M.symbols x.val hi a
    (by simp [a,s,store]) (by simp [a,s,store]) (by simp [a,s,store]) (by simp [a])
    (by simp [a,s,store]) (by simp [a,s,store]) (by simp [a,s,store]) (by simp [a,s,store])
  rw [table_lookup M q x hi] at h2
  change lookup.Exec a t2 b at h2
  have h3 : (Program.clear cur).Exec b (3*x.val+1) c := by
    simpa [c,b,a] using Program.clear_exec cur b
  obtain ⟨t4,ht4,h4⟩ := motion_exec c L R p.2.1.val p.2.2
    (by simp [c,b,a,s,store,L]) (by simp [c,b,a]) (by simp [c,b]) (by simp [c]) (by simp [c,b])
  change motion.Exec c t4 d at h4
  have h5 : (Program.clear write).Exec d (3*p.2.1.val+1) e := by
    simpa [e,d,c,b] using Program.clear_exec write d
  have h6 : (Program.clear dir).Exec e (3*movedDir p.2.2+1) f := by
    simpa [f,e,d] using Program.clear_exec dir e
  obtain ⟨t7,ht7,h7⟩ := flagState_exec f p.1.val
    (by simp [f,e,d,c,b]) (by simp [f,e,d,c,b,a,s,store])
    (by simp [f,e,d,c,b,a,s,store,haltFlag,hq1,hq2])
  have he := Program.seq_exec h1 (Program.seq_exec h2 (Program.seq_exec h3
    (Program.seq_exec h4 (Program.seq_exec h5 (Program.seq_exec h6 h7)))))
  have htape : ((nextTape M q T).left.map Fin.val,(nextTape M q T).right.map Fin.val)=
      shiftTape p.2.1.val p.2.2 L R := by
    simp only [nextTape,hq1,hq2,false_or,ite_false]
    change ((TapePair.moveWrite (zeroSymbol M) p.2.1 p.2.2 T).left.map Fin.val,
      (TapePair.moveWrite (zeroSymbol M) p.2.1 p.2.2 T).right.map Fin.val)=_
    cases hmv : p.2.2 <;> simp only [TapePair.moveWrite,shiftTape,L,R,List.map_cons,
      List.map_tail,map_head_zero]
  have htL := congrArg Prod.fst htape
  have htR := congrArg Prod.snd htape
  have hout : Function.update f halt (haltFlag p.1.val)=
      store M (nextState M q T) (nextTape M q T) m := by
    funext r
    cases r <;> simp [f,e,d,c,b,a,s,store,nextState,hq1,hq2]
    all_goals first | exact congrArg fields htL.symm | exact congrArg fields htR.symm | simp [p,x]
  rw [hout] at he
  refine ⟨_,?_,he⟩
  have ht2' : t2≤(M.states*M.symbols+1)*(30*(Diagonal.tableBits (Diagonal.raw M).table).length+
      60*M.states+60*M.symbols+100) := by
    apply ht2.trans
    apply Nat.mul_le_mul
    · simp only [Diagonal.raw,List.length_ofFn] at hi
      omega
    · have hq := q.isLt
      have hx := x.isLt
      omega
  have hx := x.isLt
  have hy := p.2.1.isLt
  have hq := p.1.isLt
  have hl : L.headD 0<M.symbols := by
    simpa only [L,map_head_zero] using (T.left.headD (zeroSymbol M)).isLt
  have hd : movedDir p.2.2≤1 := by cases p.2.2 <;> decide
  dsimp only [stepBound]
  omega

theorem step_exec (M : OneTape) (q : Fin M.states) (T : TapePair.Tape (Fin M.symbols)) (m : ℕ) :
    ∃t ≤ stepBound M,step.Exec (store M q T m) t
      (store M (nextState M q T) (nextTape M q T) m) := by
  by_cases hh : q.val=1 ∨ q.val=2
  · have hf : (tops (store M q T m) halt).isNone=false := by
      rcases hh with h | h <;> simp [tops,store,haltFlag,h]
    have he := Program.branch_false (p:=activeStep) (test:=fun v => (v halt).isNone) hf (Program.skip_exec (store M q T m))
    refine ⟨2,by simp [stepBound],?_⟩
    simpa only [step,nextState,nextTape,hh,ite_true] using he
  · have hq1 : q.val≠1 := fun h => hh (Or.inl h)
    have hq2 : q.val≠2 := fun h => hh (Or.inr h)
    obtain ⟨t,ht,he⟩ := activeStep_exec M q T m hq1 hq2
    refine ⟨t+1,by omega,?_⟩
    exact Program.branch_true (by simp [tops,store,haltFlag,hq1,hq2]) he

end WLTime.Universal

namespace WLTime.UnaryPrograms
open TypedStack
variable {K : Type uK} {C : Type uC} [DecidableEq K]

theorem countdown_lift (c : Code K Bool) (f : C → C) (enc : C → Stacks K Bool) (B : ℕ)
    (hc : ∀ x,∃ t≤B,c.Exec (enc x) t (enc (f x))) (n : ℕ) (x : C) :
    ∃ t≤n*(B+3)+1,
      (Code.loop (Code.nonempty (.inl 0))
        (.seq (c.relabel Sum.inr) (.pop (.inl 0))) : Code (Fin 2 ⊕ K) Bool).Exec
        (Sum.elim (extra n) (enc x)) t (Sum.elim (extra 0) (enc (f^[n] x))) := by
  induction n generalizing x with
  | zero =>
    refine ⟨1,by omega,?_⟩
    exact .loop_false (by simp [Code.nonempty,tops,extra,numeral])
  | succ n ih =>
    obtain ⟨u,hu,he⟩ := hc x
    have he' := Code.relabel_inr_exec he (extra (n+1))
    have hb := Code.Exec.seq he' (Code.Exec.pop _ (.inl 0))
    rw [extra_succ_update] at hb
    obtain ⟨v,hv,hr⟩ := ih (f x)
    have hh := Code.Exec.loop_true (p:=Code.nonempty (.inl 0))
      (by simp [Code.nonempty,tops,extra,numeral]) hb hr
    refine ⟨u+2+v+1,?_,?_⟩
    · nlinarith
    · simpa only [Function.iterate_succ_apply] using hh

theorem repeat_lift (base : K) (c : Code K Bool) (f : C → C) (enc : C → Stacks K Bool)
    (B n : ℕ) (hc : ∀ x,∃ t≤B,c.Exec (enc x) t (enc (f x)))
    (x : C) (hb : enc x base=numeral n) :
    ∃ t≤n*(B+15)+3,
      (repeatN base c).Exec (Sum.elim (extra 0) (enc x)) t
        (Sum.elim (extra 0) (enc (f^[n] x))) := by
  have hf := Code.copy_exec (.inr base : Fin 2 ⊕ K) (.inl 0) (.inl 1)
    (by simp) (by simp) (by simp) false (Sum.elim (extra 0) (enc x)) (by simp [extra])
  have he : Function.update (Sum.elim (extra 0) (enc x)) (.inl 0)
      (Sum.elim (extra 0) (enc x) (.inr base)++Sum.elim (extra 0) (enc x) (.inl 0))=
      Sum.elim (extra n) (enc x) := by
    funext i
    cases i with
    | inl j => fin_cases j <;> simp [extra,numeral,hb]
    | inr j => simp
  rw [he] at hf
  obtain ⟨u,hu,hr⟩ := countdown_lift c f enc B hc n x
  refine ⟨_,?_,Code.Exec.seq hf hr⟩
  simp only [Sum.elim_inr,hb,numeral,List.length_replicate]
  nlinarith
end WLTime.UnaryPrograms

namespace WLTime.TypedStack.Program
variable {K : Type uK} {C : Type uC} [DecidableEq K]

theorem repeat_lift (base : K) (p : Program K) (f : C → C) (enc : C → Stacks K Bool)
    (B n : ℕ) (hc : ∀ x,∃ t≤B,p.Exec (enc x) t (enc (f x)))
    (x : C) (hb : enc x base=UnaryPrograms.numeral n) :
    ∃ t≤n*(B+15)+3,(repeatN base p).Exec (enc x) t (enc (f^[n] x)) := by
  obtain ⟨t,ht,he⟩ := UnaryPrograms.repeat_lift (.inr base : Fin p.scratch ⊕ K) p.code f
    (fun x => p.ambient (enc x)) B n hc x hb
  refine ⟨t,ht,?_⟩
  apply Code.relabel_exec_of_maps _ (Equiv.injective _) he
  · intro k; cases k with
    | inl i => fin_cases i <;> rfl
    | inr i => cases i <;> rfl
  · intro k; cases k with
    | inl i => fin_cases i <;> rfl
    | inr i => cases i <;> rfl
  · intro l hl
    exact False.elim (hl ((merge 2 p.scratch).symm l) (Equiv.apply_symm_apply _ l))

end WLTime.TypedStack.Program

namespace WLTime.Universal
open TypedStack UnaryPrograms Reg

theorem steps_exec (M : OneTape) (m : ℕ) (hm : 0 < m) (s : ℕ) (c : Config M) :
    ∃ t ≤ (stepBound M+18*s)*m^s,
      (steps s).Exec (encode M m c) t (encode M m ((next M)^[m^s] c)) := by
  induction s generalizing c with
  | zero => simpa only [Nat.mul_zero,Nat.add_zero,pow_zero,Nat.mul_one,Function.iterate_one,steps,encode,next]
      using step_exec M c.1 c.2 m
  | succ s ih =>
    obtain ⟨t,ht,he⟩ := Program.repeat_lift base (steps s) ((next M)^[m^s]) (encode M m)
      ((stepBound M+18*s)*m^s) m ih c rfl
    refine ⟨t,?_,?_⟩
    · have hp : 1 ≤ m^s := Nat.one_le_pow _ _ hm
      apply ht.trans
      rw [pow_succ]
      nlinarith
    · simpa only [steps,pow_succ,Function.iterate_mul] using he

end WLTime.Universal

end OAI
end

section
-- module Solutions.OAIQW_WLTime.BoundedRun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uK

namespace WLTime.TypedStack.Program
variable {K : Type uK} [DecidableEq K]

theorem reverseInto_exec (a b : K) (hab : a≠b) (s : Stacks K Bool) :
    (reverseInto a b).Exec s (5*(s a).length+1)
      (Function.update (Function.update s a []) b ((s a).reverse++s b)) :=
  ofCode_exec (Code.transfer_exec a b hab false s)

theorem shift_exec (a b : K) (hab : a≠b) (s : Stacks K Bool) :
    (shift a b).Exec s 4
      (Function.update (Function.update s b ((s a).headD false::s b)) a (s a).tail) := by
  apply ofCode_exec
  have he := Code.Exec.seq (Code.Exec.pushDyn s b (fun v => (v a).getD false)) (Code.Exec.pop _ a)
  simpa [Function.update_of_ne hab,tops] using he

end WLTime.TypedStack.Program

namespace WLTime.Universal
open TypedStack UnaryPrograms Reg

theorem shiftPair_prefix (xs ys zs : List Bool) :
    shiftPair^[xs.length] (xs++ys,zs)=(ys,xs.reverse++zs) := by
  induction xs generalizing zs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    change shiftPair^[xs.length] (xs++ys,x::zs)=_
    rw [ih,List.reverse_cons,List.append_assoc]
    rfl

theorem takeDescription_exec (xs ys : List Bool) (s : Stacks Reg Bool)
    (hs : s search=xs++ys) (hi : s index=numeral xs.length)
    (ht : s temp=[]) (hb : s tab=[]) :
    ∃t≤24*xs.length+4,takeDescription.Exec s t
      (Function.update (Function.update s search ys) tab xs) := by
  let enc (p : List Bool × List Bool) := Function.update (Function.update s search p.1) temp p.2
  have hc (p) : (Program.shift search temp).Exec (enc p) 4 (enc (shiftPair p)) := by
    have he := Program.shift_exec search temp (by decide) (enc p)
    convert he using 1
    funext r; cases r <;> simp [enc,shiftPair]
  have hi' : enc (xs++ys,[]) index=numeral xs.length := by simp [enc,hi]
  obtain ⟨t,htime,he⟩ := Program.repeat_lift index (Program.shift search temp) shiftPair enc 4 xs.length
    (fun p => ⟨4,le_rfl,hc p⟩) (xs++ys,[]) hi'
  rw [shiftPair_prefix] at he
  have hin : enc (xs++ys,[])=s := by
    funext r; cases r <;> simp [enc,hs,ht]
  rw [hin] at he
  have hr := Program.reverseInto_exec temp tab (by decide) (enc (ys,xs.reverse++[]))
  have hout : Function.update (Function.update (enc (ys,xs.reverse++[])) temp []) tab
      (((enc (ys,xs.reverse++[])) temp).reverse++enc (ys,xs.reverse++[]) tab)=
      Function.update (Function.update s search ys) tab xs := by
    funext r; cases r <;> simp [enc,hb,ht]
  rw [hout] at hr
  have hf := Program.seq_exec he hr
  refine ⟨_,?_,hf⟩
  simp only [enc,Function.update_self,List.append_nil,List.length_reverse]
  omega

end WLTime.Universal

namespace WLTime.Universal
open TypedStack UnaryPrograms Reg

theorem tapeBody_exec (s : Stacks Reg Bool) (b : Bool) (xs : List Bool) (hs : s temp=b::xs) :
    ∃t≤11,tapeBody.Exec s t
      (Function.update (Function.update (Function.update s right (tile (bitValue b)++s right))
        temp xs) base (true::s base)) := by
  let a := Function.update s right (false::s right)
  let c := Function.update a right (true::a right)
  have h1 := Program.push_exec right false s
  have h2 := Program.push_exec right true a
  cases b with
  | false =>
    have hb := Program.branch_false (p:=Program.push right true) (test:=UnaryPrograms.isTrue temp)
      (by simp [UnaryPrograms.isTrue,tops,c,a,hs]) (Program.skip_exec c)
    have h3 := Program.pop_exec temp c
    have h4 := Program.push_exec base true (Function.update c temp (c temp).tail)
    have he := Program.seq_exec h1 (Program.seq_exec h2 (Program.seq_exec hb (Program.seq_exec h3 h4)))
    refine ⟨10,by omega,?_⟩
    convert he using 1 <;> try rfl
    funext r; cases r <;> simp [c,a,tile,bitValue,numeral,hs]
  | true =>
    have hb := Program.branch_true (q:=Program.skip) (test:=UnaryPrograms.isTrue temp)
      (by simp [UnaryPrograms.isTrue,tops,c,a,hs]) (Program.push_exec right true c)
    let d := Function.update c right (true::c right)
    have h3 := Program.pop_exec temp d
    have h4 := Program.push_exec base true (Function.update d temp (d temp).tail)
    have he := Program.seq_exec h1 (Program.seq_exec h2 (Program.seq_exec hb (Program.seq_exec h3 h4)))
    refine ⟨11,by omega,?_⟩
    convert he using 1 <;> try rfl
    funext r; cases r <;> simp [d,c,a,tile,bitValue,numeral,hs]

theorem tapeLoop_exec (xs : List Bool) (s : Stacks Reg Bool) (hs : s temp=xs) :
    ∃t≤12*xs.length+1,tapeLoop.Exec s t
      (Function.update (Function.update (Function.update s temp []) right
        (fields (xs.reverse.map bitValue)++s right)) base (numeral xs.length++s base)) := by
  induction xs generalizing s with
  | nil =>
    have he := Program.loop_false (p:=tapeBody) (test:=Code.nonempty temp) (s:=s)
      (by simp [Code.nonempty,tops,hs])
    refine ⟨1,by simp,?_⟩
    convert he using 1 <;> try rfl
    funext r; cases r <;> simp [hs,fields,numeral]
  | cons b xs ih =>
    let a := Function.update (Function.update (Function.update s right (tile (bitValue b)++s right))
      temp xs) base (true::s base)
    obtain ⟨t,ht,hb⟩ := tapeBody_exec s b xs hs
    obtain ⟨u,hu,hr⟩ := ih a (by simp [a])
    have he := Program.loop_true (test:=Code.nonempty temp)
      (by simp [Code.nonempty,tops,hs]) hb hr
    refine ⟨t+u+1,by simp only [List.length_cons]; omega,?_⟩
    convert he using 1 <;> try rfl
    funext r; cases r <;> simp [a,List.reverse_cons,List.map_append,List.append_assoc,tile]
    rw [numeral_add]
    simp only [numeral,List.replicate_one,List.append_assoc,List.singleton_append]

theorem inputPrep_exec (w : List Bool) :
    ∃t≤29*w.length+4,inputPrep.Exec (inputStore w) t (prepared w) := by
  let a := Function.update (inputStore w) search w
  let b := Function.update (Function.update a input []) temp w.reverse
  have h1 : (Program.copy input search).Exec (inputStore w) (12*w.length+2) a := by
    simpa [a,inputStore] using Program.copy_exec input search (by decide) (inputStore w)
  have h2 : (Program.reverseInto input temp).Exec a (5*w.length+1) b := by
    simpa [b,a,inputStore] using Program.reverseInto_exec input temp (by decide) a
  obtain ⟨t,ht,h3⟩ := tapeLoop_exec w.reverse b (by simp [b])
  have hout : Function.update (Function.update (Function.update b temp []) right
      (fields (w.reverse.reverse.map bitValue)++b right)) base (numeral w.reverse.length++b base)=prepared w := by
    funext r; cases r <;> simp [b,a,inputStore,prepared]
  rw [hout] at h3
  have he := Program.seq_exec h1 (Program.seq_exec h2 h3)
  refine ⟨_,?_,he⟩
  simp only [List.length_reverse] at ht
  omega

end WLTime.Universal

namespace WLTime.Universal
open TypedStack UnaryPrograms Reg

theorem parseProgram_exec (M : OneTape) (z : List Bool) :
    ∃ t ≤ 32*(Diagonal.description M).length+3*z.length+3*M.states+5*M.symbols+15,
      parseProgram.Exec (prepared (Diagonal.designation M++z)) t
        (encode M (Diagonal.designation M++z).length (initialConfig M (Diagonal.designation M++z))) := by
  let ds := Diagonal.description M
  let w := Diagonal.designation M++z
  let a := Function.update (Function.update (prepared w) search (ds++z)) index (numeral ds.length)
  let b := Function.update (Function.update a search z) tab ds
  let c := Function.update b search []
  let d := Function.update c index []
  let e := Function.update d tab (Diagonal.unary M.symbols++Diagonal.tableBits (Diagonal.raw M).table)
  have h1 : (Program.read search index).Exec (prepared w) (5*ds.length+3) a := by
    simpa [a,prepared,w,Diagonal.designation,unary_tile,List.append_assoc,ds]
      using Program.read_exec search index (by decide) (prepared w)
  obtain ⟨t2,ht2,h2⟩ := takeDescription_exec ds z a (by simp [a]) (by simp [a])
    (by simp [a,prepared]) (by simp [a,prepared])
  change takeDescription.Exec a t2 b at h2
  have h3 : (Program.clear search).Exec b (3*z.length+1) c := by
    simpa [c,b] using Program.clear_exec search b
  have h4 : (Program.clear index).Exec c (3*ds.length+1) d := by
    simpa [d,c,b,a] using Program.clear_exec index c
  have h5 : (skipField tab).Exec d (3*M.states+3) e := by
    simpa [e,d,c,b,ds,Diagonal.description,Diagonal.Raw.bits,Diagonal.raw,
      unary_tile,List.append_assoc] using skipField_exec tab d
  have h6 : (Program.read tab alpha).Exec e (5*M.symbols+3)
      (Function.update (Function.update e tab (Diagonal.tableBits (Diagonal.raw M).table)) alpha
        (numeral M.symbols)) := by
    simpa [e,d,c,b,a,prepared,unary_tile] using Program.read_exec tab alpha (by decide) e
  have hout : Function.update (Function.update e tab (Diagonal.tableBits (Diagonal.raw M).table)) alpha
      (numeral M.symbols)=encode M w.length (initialConfig M w) := by
    funext r; cases r <;> simp [e,d,c,b,a,prepared,encode,store,initialConfig,haltFlag,numeral]
    exact congrArg fields (map_symbols_val M w).symm
  rw [hout] at h6
  have he := Program.seq_exec h1 (Program.seq_exec h2 (Program.seq_exec h3
    (Program.seq_exec h4 (Program.seq_exec h5 h6))))
  refine ⟨_,?_,he⟩
  dsimp only [ds] at ht2 ⊢
  omega

theorem initProgram_exec (M : OneTape) (z : List Bool) :
    ∃ t ≤ 64*(Diagonal.designation M++z).length+3*M.states+5*M.symbols+19,
      initProgram.Exec (inputStore (Diagonal.designation M++z)) t
        (encode M (Diagonal.designation M++z).length (initialConfig M (Diagonal.designation M++z))) := by
  obtain ⟨t,ht,h1⟩ := inputPrep_exec (Diagonal.designation M++z)
  obtain ⟨u,hu,h2⟩ := parseProgram_exec M z
  refine ⟨t+u,?_,Program.seq_exec h1 h2⟩
  have hd : (Diagonal.description M).length ≤ (Diagonal.designation M++z).length := by
    simp only [Diagonal.designation,List.length_append]
    omega
  have hz : z.length ≤ (Diagonal.designation M++z).length := by simp
  omega

end WLTime.Universal

namespace WLTime.Universal
open OneTape

theorem initial_relative (M : OneTape) (w : List Bool) :
    Relative M (M.initial w) (initialConfig M w) := by
  refine ⟨rfl,?_⟩
  intro z
  simp only [TapePair.contents,initialConfig,OneTape.initial,zero_add]
  change (if z<0 then ([] : List (Fin M.symbols)).getD (-z-1).toNat (zeroSymbol M)
    else (w.map M.toTM.symbol).getD z.toNat (zeroSymbol M)) =
    if 0≤z ∧ z.toNat<w.length then M.toTM.symbol (w.getD z.toNat false) else zeroSymbol M
  dsimp only [OneTape.toTM] at *
  by_cases hz : z<0
  · have hn : ¬(0≤z ∧ z.toNat<w.length) := by omega
    rw [ite_eq_left hz,ite_eq_right hn,List.getD_nil]
  · rw [ite_eq_right hz]
    have hz' : 0≤z := by omega
    by_cases hb : z.toNat<w.length
    · rw [ite_eq_left ⟨hz',hb⟩,List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hb)]
      rw [List.getElem_map,List.getD_eq_getElem _ _ hb]
    · rw [ite_eq_right (by omega),List.getD_eq_default _ _ (by simp only [List.length_map]; omega)]

theorem next_relative (M : OneTape) (C : M.Config ℤ) (c : Config M) (h : Relative M C c) :
    Relative M (M.step lineShift C) (next M c) := by
  classical
  have ho : c.2.right.headD (zeroSymbol M)=C.tape C.head := by
    simpa only [TapePair.contents_zero,add_zero] using h.2 0
  by_cases hh : C.state.val=1 ∨ C.state.val=2
  · rw [M.step_halted lineShift C hh]
    constructor
    · simp only [next,nextState,h.1,hh,ite_true]
    · simpa only [next,nextTape,h.1,hh,ite_true] using h.2
  · constructor
    · simp only [next,nextState,h.1,hh,ite_false,ho,OneTape.step,OneTape.action]
    · intro z
      simp only [next,nextTape,h.1,hh,ite_false,ho,TapePair.contents_moveWrite]
      rw [h.2]
      simp only [OneTape.step,OneTape.action,hh,ite_false,moveAt_line,Function.update_apply]
      have he : C.head+(M.transition C.state (C.tape C.head)).2.2.displacement+z=C.head ↔
          z+(M.transition C.state (C.tape C.head)).2.2.displacement=0 := by omega
      rw [he]
      rw [show C.head+(z+(M.transition C.state (C.tape C.head)).2.2.displacement)=
        C.head+(M.transition C.state (C.tape C.head)).2.2.displacement+z by omega]
      by_cases hp : z+(M.transition C.state (C.tape C.head)).2.2.displacement=0 <;>
        simp only [hp,ite_true,ite_false]

theorem iterate_relative (M : OneTape) (w : List Bool) (t : ℕ) :
    Relative M (M.run lineShift (M.initial w) t) ((next M)^[t] (initialConfig M w)) := by
  induction t with
  | zero => exact initial_relative M w
  | succ t ih =>
    simp only [OneTape.run,Function.iterate_succ_apply'] at *
    exact next_relative M _ _ ih

theorem simulated_state (M : OneTape) (w : List Bool) (t : ℕ) :
    ((next M)^[t] (initialConfig M w)).1.val=(M.toTM.run w t).state.val := by
  have h := (iterate_relative M w t).1
  have ht := congrArg (fun C : M.toTM.Config => C.state.val) (M.embed_run w t)
  exact congrArg Fin.val h |>.trans ht

end WLTime.Universal

namespace WLTime.TypedStack.Program
variable {K : Type uK} [DecidableEq K]

theorem machine_initial (p : Program K) (k : K) (answer : Tops K Bool → Bool) (w : List Bool) :
    (p.machine k answer).initialConfig w=⟨.inr (.inl p.code.entry),p.ambient (inputStacks k w)⟩ := by
  dsimp only [Machine.initialConfig,machine]
  congr 1
  funext j
  cases j with
  | inl i => simp [ambient]
  | inr i => simp [ambient,inputStacks]

theorem machine_run (p : Program K) (k : K) (answer : Tops K Bool → Bool) (w : List Bool)
    {t out} (h : p.Exec (inputStacks k w) t out) :
    (p.machine k answer).run w (t+1)=⟨.inl (answer (tops out)),p.ambient out⟩ := by
  have he := (Code.exec_finite h).plug Sum.inl (.inr ()) (fun _ _ => rfl)
    (Execution.halt (tr:=finalTransition p answer) (q:=.inr ()) (s:=p.ambient out) rfl)
  rw [Machine.run,machine_initial]
  exact Execution.iterate (p.machine k answer) he

variable [Fintype K]

theorem oneTape_correct (p : Program K) (k : K) (answer : Tops K Bool → Bool) (w : List Bool)
    {t out} (h : p.Exec (inputStacks k w) t out) :
    (p.machine k answer).compile.oneTape.toTM.halts w ∧
    (p.machine k answer).compile.oneTape.toTM.time w ≤
      8*(p.scratch+Fintype.card K+1)*(w.length+t+2)^2 ∧
    ((p.machine k answer).compile.oneTape.toTM.accepts w ↔ answer (tops out)=true) := by
  have hrun := congrArg Config.state (p.machine_run k answer w h)
  have he := (p.machine k answer).oneTape_correct w (t+1) (answer (tops out)) hrun
  simpa only [Fintype.card_sum,Fintype.card_fin,show w.length+(t+1)+1=w.length+t+2 by omega] using he

end WLTime.TypedStack.Program

namespace WLTime.Universal
open TypedStack Reg

theorem boundedProgram_exec (s : ℕ) (M : OneTape) (z : List Bool)
    (hm : 0 < (Diagonal.designation M++z).length) :
    ∃ t ≤ 64*(Diagonal.designation M++z).length+3*M.states+5*M.symbols+19+
        (stepBound M+18*s)*(Diagonal.designation M++z).length^s,
      (boundedProgram s).Exec (inputStore (Diagonal.designation M++z)) t
        (encode M (Diagonal.designation M++z).length
          ((next M)^[(Diagonal.designation M++z).length^s] (initialConfig M (Diagonal.designation M++z)))) := by
  obtain ⟨t,ht,h1⟩ := initProgram_exec M z
  obtain ⟨u,hu,h2⟩ := steps_exec M (Diagonal.designation M++z).length hm s (initialConfig M (Diagonal.designation M++z))
  exact ⟨t+u,by omega,Program.seq_exec h1 h2⟩

theorem machine_correct (s : ℕ) (M : OneTape) (z : List Bool)
    (hm : 0 < (Diagonal.designation M++z).length) :
    (machine s).toTM.halts (Diagonal.designation M++z) ∧
    (machine s).toTM.time (Diagonal.designation M++z) ≤ timeBound s M (Diagonal.designation M++z).length ∧
    ((machine s).toTM.accepts (Diagonal.designation M++z) ↔
      ¬∃ t ≤ (Diagonal.designation M++z).length^s,
        (M.toTM.run (Diagonal.designation M++z) t).state.val=1) := by
  let w := Diagonal.designation M++z
  obtain ⟨t,ht,he⟩ := boundedProgram_exec s M z hm
  have hc := (boundedProgram s).oneTape_correct input answer w he
  change (machine s).toTM.halts w ∧ (machine s).toTM.time w ≤ timeBound s M w.length ∧
    ((machine s).toTM.accepts w ↔ ¬∃ t ≤ w.length^s, (M.toTM.run w t).state.val=1)
  refine ⟨hc.1,?_,?_⟩
  · apply hc.2.1.trans
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    dsimp only [w]
    omega
  · change ((boundedProgram s).machine input answer).compile.oneTape.toTM.accepts w ↔ _
    rw [hc.2.2]
    simp only [answer,tops,encode,store,haltFlag_answer,decide_eq_true_eq]
    rw [simulated_state]
    constructor
    · intro h ⟨u,hu,hacc⟩
      exact h (by rw [M.toTM.run_frozen w (Or.inl hacc) hu]; exact hacc)
    · intro h hacc
      exact h ⟨w.length^s,le_rfl,hacc⟩

end WLTime.Universal

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Diagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLTime.Diagonal
 theorem tableBits_length_upper (es : List Entry) (q g : ℕ)
    (he : ∀ e∈es,e.1<q ∧ e.2.1<g ∧ e.2.2<3) :
    (tableBits es).length ≤ (q+g+3)*es.length := by
  induction es with
  | nil => simp [tableBits]
  | cons e es ih =>
    have h := he e (by simp)
    have hs := ih (fun x hx => he x (by simp [hx]))
    change (entryBits e++tableBits es).length ≤ _
    rw [List.length_append,entryBits_length,List.length_cons]
    nlinarith
 theorem tableBits_length_lower (es : List Entry) : es.length ≤ (tableBits es).length := by
  induction es with
  | nil => simp [tableBits]
  | cons e es ih =>
    change (e::es).length ≤ (entryBits e++tableBits es).length
    rw [List.length_cons,List.length_append,entryBits_length]
    omega
 theorem designation_length (M : OneTape) :
    (designation M).length=2*(M.states+M.symbols+2+(tableBits (raw M).table).length)+1 := by
  simp only [designation,List.length_append,unary_length,description,Raw.bits,raw]
  ring
 theorem designation_bounds (M : OneTape) {m : ℕ} (hm : (designation M).length ≤ m) :
    M.states ≤ m ∧ M.symbols ≤ m ∧ M.states*M.symbols ≤ m ∧
    (tableBits (raw M).table).length ≤ m := by
  rw [designation_length] at hm
  have h := tableBits_length_lower (raw M).table
  rw [(raw_valid M).2.2.1] at h
  change M.states*M.symbols ≤ (tableBits (raw M).table).length at h
  omega
 theorem designation_upper (M : OneTape) (B : ℕ) (hq : M.states ≤ B) (hg : M.symbols ≤ B)
    (hB : 3 ≤ B) : (designation M).length ≤ 13*B^3 := by
  have he := tableBits_length_upper (raw M).table M.states M.symbols (raw_valid M).2.2.2
  rw [(raw_valid M).2.2.1] at he
  have ht : (tableBits (raw M).table).length ≤ 3*B^3 := by
    calc
      _ ≤ (M.states+M.symbols+3)*(M.states*M.symbols) := he
      _ ≤ (3*B)*(B*B) := Nat.mul_le_mul (by omega) (Nat.mul_le_mul hq hg)
      _ = 3*B^3 := by ring
  have hp : B ≤ B^3 := Nat.le_self_pow (by decide) B
  rw [designation_length]
  omega
end WLTime.Diagonal
namespace WLTime.Universal
 theorem stepBound_small (M : OneTape) {m : ℕ} (hfit : (Diagonal.designation M).length ≤ m)
    (hm : 1 ≤ m) : stepBound M ≤ 1000*m^2 := by
  obtain ⟨hq,hg,hqg,hbits⟩ := Diagonal.designation_bounds M hfit
  unfold stepBound
  calc
    _ ≤ (m+1)*(30*m+60*m+60*m+100)+50*m+100*m+100 := by gcongr
    _ ≤ 1000*m^2 := by nlinarith
 theorem timeBound_small (s : ℕ) (M : OneTape) {m : ℕ}
    (hfit : (Diagonal.designation M).length ≤ m) (hm : 2 ≤ m)
    (hs : 1 ≤ s) (hsm : 18*s ≤ m)
    (hfactor : 8*((boundedProgram s).scratch+Fintype.card Reg+1)*1200^2 ≤ m) :
    timeBound s M m ≤ m^(2*s+5) := by
  obtain ⟨hq,hg,_,_⟩ := Diagonal.designation_bounds M hfit
  have hstep := stepBound_small M hfit (by omega)
  have hpow : m ≤ m^s := Nat.le_self_pow (by omega) m
  have h1 : 65*m+3*M.states+5*M.symbols+21+(stepBound M+18*s)*m^s ≤ 1200*m^(s+2) := by
    rw [pow_add,pow_two]
    have hm2 : m ≤ m*m := by nlinarith
    have hpos : 1 ≤ m^s := one_le_pow₀ (by omega)
    nlinarith
  unfold timeBound
  calc
    _ ≤ 8*((boundedProgram s).scratch+Fintype.card Reg+1)*(1200*m^(s+2))^2 := by gcongr
    _ = (8*((boundedProgram s).scratch+Fintype.card Reg+1)*1200^2)*m^(2*s+4) := by ring
    _ ≤ m*m^(2*s+4) := Nat.mul_le_mul_right _ hfactor
    _ = m^(2*s+5) := by
      simpa only [show 2*s+5=(2*s+4)+1 by omega] using (pow_succ' m (2*s+4)).symm
end WLTime.Universal

namespace WLTime.Diagonal

theorem pointwise_contradiction (D : OneTape) (w : List Bool) (T : ℕ)
    (ht : D.toTM.halts w) (hb : D.toTM.time w ≤ T)
    (hc : D.toTM.accepts w ↔ ¬∃ t ≤ T,(D.toTM.run w t).state.val=1) : False := by
  rw [bounded_accepts_iff D w T ht hb] at hc
  exact not_iff_self hc.symm

end WLTime.Diagonal

namespace WLTime.Numeric
open Filter
open scoped Topology
 theorem polylog_sublinear (K r : ℕ) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, K*((Nat.digits 2 m).length+1)^r ≤ m := by
  have h : (fun x : ℝ => ((K : ℝ)*3^r)*(Real.logb 2 x)^r) =o[atTop] id :=
    Real.isLittleO_pow_logb_id_atTop.const_mul_left _
  have hb := tendsto_natCast_atTop_atTop.eventually (h.bound (by norm_num : (0 : ℝ)<1))
  have hall : ∀ᶠ m : ℕ in atTop, K*((Nat.digits 2 m).length+1)^r ≤ m := by
    filter_upwards [hb,eventually_ge_atTop 2] with m hm h2
    have hm0 : m ≠ 0 := by omega
    have hm2R : (2 : ℝ) ≤ m := by exact_mod_cast h2
    have hmposR : (0 : ℝ) < m := by linarith
    have hlog : 1 ≤ Real.logb 2 (m : ℝ) := by
      rw [Real.le_logb_iff_rpow_le (by norm_num) hmposR]
      simpa using hm2R
    have hd : (((Nat.digits 2 m).length+1 : ℕ) : ℝ) ≤ 3*Real.logb 2 m := by
      rw [Nat.length_digits 2 m (by omega) hm0]
      push_cast
      have ht := Real.natLog_le_logb m 2
      norm_num at ht
      linarith
    have hl0 : 0 ≤ Real.logb 2 (m : ℝ) := by linarith
    simp only [Real.norm_eq_abs,Function.id_def] at hm
    rw [abs_of_nonneg (by positivity),abs_of_nonneg (Nat.cast_nonneg m),one_mul] at hm
    have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ ((Nat.digits 2 m).length+1 : ℕ)) hd r
    have hp' := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg K)
    rw [mul_pow] at hp'
    have hh : (K : ℝ)*(((Nat.digits 2 m).length+1 : ℕ) : ℝ)^r ≤ (m : ℝ) := by nlinarith
    exact_mod_cast hh
  exact eventually_atTop.mp hall
end WLTime.Numeric

namespace WLTime.Numeric
 theorem base_lower (C m : ℕ) (hC : 1≤C) : m ≤ base C m := by
  have hm : m≤ m^2 := Nat.le_self_pow (by decide) m
  have hp : 1≤(C*m^2+1)^2+1 := by omega
  have hc : m^2≤C*m^2 := Nat.le_mul_of_pos_left _ (by omega)
  have ht := Nat.le_mul_of_pos_right (C*m^2) (by omega : 0<(C*m^2+1)^2+1)
  dsimp [base]; omega
 theorem base_upper (C m : ℕ) (hC : 1≤C) (hm : 1≤ m) : base C m ≤ 6*C^3*m^6 := by
  have hCm : 1≤C*m^2 := by
    have : 0<C*m^2 := by positivity
    omega
  have h1 : (C*m^2+1)^2+1≤5*(C*m^2)^2 := by nlinarith
  have h2 := Nat.mul_le_mul_left (C*m^2) h1
  have h3 : 1≤C^3*m^6 := by
    have : 0<C^3*m^6 := by positivity
    omega
  dsimp [base]
  nlinarith [show C*m^2*(5*(C*m^2)^2)=5*C^3*m^6 by ring]
 theorem chooseOrder_bounds (C n m₀ : ℕ) (hC : 1≤C) (hn : base C m₀≤n) :
    m₀≤chooseOrder C n ∧ base C (chooseOrder C n)≤n ∧ n<base C (chooseOrder C n+1) := by
  have hb : m₀≤n := (base_lower C m₀ hC).trans hn
  have h1 := Nat.le_findGreatest (P:=fun x => base C x≤n) hb hn
  have h2 := Nat.findGreatest_spec (P:=fun x => base C x≤n) hb hn
  refine ⟨h1,h2,?_⟩
  by_cases hlt : chooseOrder C n<n
  · exact lt_of_not_ge ((Nat.findGreatest_eq_iff.mp (rfl : chooseOrder C n=chooseOrder C n)).2.2
      (by omega) (by omega))
  · have hle : chooseOrder C n≤n := Nat.findGreatest_le n
    have h := base_lower C (chooseOrder C n+1) hC
    omega
 theorem order_polynomial (C n m : ℕ) (hC : 1≤C) (hm : 384*C^3≤ m)
    (hn : n<base C (m+1)) : n≤ m^8 := by
  have hc : 1≤C^3 := one_le_pow₀ hC
  have hm1 : 1≤ m := by nlinarith
  have hu := base_upper C (m+1) hC (by omega)
  have hp : (m+1)^6≤64*m^6 := by
    calc
      _≤(2*m)^6 := Nat.pow_le_pow_left (by omega) 6
      _=64*m^6 := by ring
  have hx : n≤384*C^3*m^6 := by nlinarith
  calc
    n≤384*C^3*m^6 := hx
    _≤ m*m^6 := Nat.mul_le_mul_right _ hm
    _=m^7 := by ring
    _≤ m^8 := Nat.pow_le_pow_right (by omega) (by decide)
end WLTime.Numeric
namespace WLTime.Numeric
 theorem pow_mono (m i j : ℕ) (hm : 0 < m) (h : i ≤ j) : m^i ≤ m^j := Nat.pow_le_pow_right hm h
 theorem grow_one (m X : ℕ) (hm : 2≤ m) (hX : 1≤X) : X+1≤X*m := by nlinarith
 theorem space_arith (m X : ℕ) (hm : m≤X) (hX : 0<X) : 2*(X-1)+m+2<4*X := by omega
 theorem digits_le (n : ℕ) : (Nat.digits 2 n).length≤ n+1 := by
  apply (Nat.digits_length_le_iff (by decide) n).mpr
  exact (Nat.lt_two_pow_self (n:=n)).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
 theorem digits_polynomial (n m e : ℕ) (he : 0< e) (hn : n≤ m^e) :
    (Nat.digits 2 n).length+1≤(e+1)*((Nat.digits 2 m).length+1) := by
  have hm := Nat.lt_base_pow_length_digits (m:=m) (by decide : 1< 2)
  have hp := Nat.pow_lt_pow_left hm (by omega : e≠0)
  have hn' : n< 2^((Nat.digits 2 m).length*e) := by
    rw [pow_mul] ; exact hn.trans_lt hp
  have hl := (Nat.digits_length_le_iff (by decide : 1< 2) n).mpr hn'
  nlinarith
 theorem sum_le_pow {m a b e : ℕ} (hm : 2≤ m) (ha : a≤ m^e) (hb : b≤ m^e) :
    a+b≤ m^(e+1) := by
  rw [pow_succ]
  nlinarith
 theorem input_small (n m : ℕ) (hm : 8≤ m) (hn : n≤ m^8) :
    2*(Nat.digits 2 n).length+1+2*n^2≤ m^20 := by
  have hd := digits_le n
  have hp : 1≤ m^8 := one_le_pow₀ (by omega)
  have hq : m^8≤ m^16 := Nat.pow_le_pow_right (by omega) (by decide)
  have hn2 : n^2≤ m^16 := by simpa only [←pow_mul] using Nat.pow_le_pow_left hn 2
  have hr : 8≤ m^4 := (show 8≤ m by omega).trans (Nat.le_self_pow (by decide) m)
  rw [show 20=16+4 by decide,pow_add]
  nlinarith
 theorem scale6 (m X x : ℕ) (hm : 7≤ m) (hx : x≤X) (hX : 1≤X) : 6*x+1≤X*m := by
  nlinarith only [hm,hx,hX]
 theorem consumer_inside (m B Y W X : ℕ) (hm : 16≤ m) (hmX : m≤X) (hB : B≤X) (hY : Y≤X) (hW : W≤X) :
    m+B+5*Y+W+3≤X*m := by nlinarith only [hm,hmX,hB,hY,hW]
 theorem writer_small (C charge n m : ℕ) (hm : 128≤ m) (hC : C≤ m)
    (hf : charge≤ m) (hn : n≤ m^8) :
    17*m+3+24*((Nat.digits 2 n).length+1)*(n+1)+(2*(2*(Nat.digits 2 n).length+1)+1)+
      charge*(6*(C+n+m+2)^27+1)^8 ≤ m^2400 := by
  have hm0 : 0< m := by omega
  have hm1 : 1≤ m := by omega
  have hm2 : 2≤ m := by omega
  have hm7 : 7≤ m := by omega
  have hp (e : ℕ) (he : e≠0) : m≤ m^e := Nat.le_self_pow he m
  have hd := digits_le n
  have hQ : C+n+m+2≤ m^11 := by
    have h8 := hp 8 (by decide)
    have h3 : 4≤ m^3 := (show 4≤ m by omega).trans (hp 3 (by decide))
    rw [show 11=8+3 by decide,pow_add]
    nlinarith only [hC,hn,h8,h3,hm2]
  have hQp : (C+n+m+2)^27≤ m^(11*27) := by
    exact (Nat.pow_le_pow_left hQ 27).trans_eq (pow_mul m 11 27).symm
  have h297 : 1≤ m^(11*27) := one_le_pow₀ hm1
  have hbody : 6*(C+n+m+2)^27+1≤ m^(11*27+1) := by
    rw [pow_succ m (11*27)]
    exact scale6 m (m^(11*27)) ((C+n+m+2)^27) hm7 hQp h297
  have hbp : (6*(C+n+m+2)^27+1)^8≤ m^((11*27+1)*8) := by
    exact (Nat.pow_le_pow_left hbody 8).trans_eq (pow_mul m (11*27+1) 8).symm
  have hc : charge*(6*(C+n+m+2)^27+1)^8≤ m^((11*27+1)*8+1) := by
    calc
      _≤ m*m^((11*27+1)*8) := Nat.mul_le_mul hf hbp
      _=m^((11*27+1)*8+1) := (pow_succ' m ((11*27+1)*8)).symm
  have h8 := hp 8 (by decide)
  have h16 : (m^8)^2=m^16 := by ring
  have hn2 : (n+1)^2≤ 4*m^16 := by nlinarith only [hn,h8,hm,h16]
  have hsmall : 17*m+3+24*((Nat.digits 2 n).length+1)*(n+1)+(2*(2*(Nat.digits 2 n).length+1)+1)≤ m^20 := by
    have h4 : 256≤ m^4 := (show 256≤128^4 by decide).trans (Nat.pow_le_pow_left hm 4)
    have hn16 : n≤ m^16 := hn.trans (Nat.pow_le_pow_right hm0 (by decide))
    have hm16 := hp 16 (by decide)
    rw [show 20=16+4 by decide,pow_add]
    have hplus : (Nat.digits 2 n).length+1≤2*(n+1) := by omega
    have hprod := Nat.mul_le_mul_right (n+1) hplus
    nlinarith only [hprod,hn2,h4,hn16,hm16,hm,hd]
  have h20 : m^20≤ m^((11*27+1)*8+1) := pow_mono m 20 ((11*27+1)*8+1) hm0 (by decide)
  exact (sum_le_pow hm2 (hsmall.trans h20) hc).trans
    (pow_mono m _ _ hm0 (by decide))
 theorem consumer_small (m a B Y v factor overhead : ℕ) (hm : 16≤ m)
    (hB : B≤ m^2400) (hY : Y≤ m^20) (hv : v≤ m^(8*a))
    (hf : factor≤ m) (ho : overhead≤ m) :
    factor*(m+B+5*Y+overhead*v+3)^2≤ m^(2*(max 2400 (8*a+1))+3) := by
  have hm0 : 0< m := lt_of_lt_of_le (by decide : 0<16) hm
  let r := max 2400 (8*a+1)
  have hr : 1≤ r := (by decide : 1≤ 2400).trans (le_max_left _ _)
  have h2400 : m^2400≤ m^r := pow_mono m 2400 r hm0 (le_max_left _ _)
  have h20 : m^20≤ m^r := Nat.pow_le_pow_right hm0 ((by decide : 20≤ 2400).trans (le_max_left _ _))
  have h8 : overhead*v≤ m^r := by
    calc
      _≤ m*m^(8*a) := Nat.mul_le_mul ho hv
      _=m^(8*a+1) := by ring
      _≤ m^r := Nat.pow_le_pow_right hm0 (le_max_right _ _)
  have hmr : m≤ m^r := Nat.le_self_pow (Nat.ne_of_gt hr) m
  have hB' := hB.trans h2400
  have hY' := hY.trans h20
  have hinside : m+B+5*Y+overhead*v+3≤ m^(r+1) := by
    rw [pow_succ]
    exact consumer_inside _ _ _ _ _ hm hmr hB' hY' h8
  calc
    _≤ m*(m^(r+1))^2 := Nat.mul_le_mul hf (Nat.pow_le_pow_left hinside 2)
    _=m^(2*r+3) := by ring
end WLTime.Numeric

namespace WLTime.OneTape.Symbolic
open scoped Classical
 theorem coefficient_pos (U : OneTape) (d q : ℕ) : 0< coefficient U d q (d+q+2) := by
  unfold coefficient Compression.ConsistencyData.rectCoefficient
  apply Nat.mul_pos
  · apply Fintype.card_pos_iff.mpr
    exact ⟨(⟨0,by omega⟩,Sum.inl (.inl .dummy))⟩
  · exact Compression.ConsistencyData.tagValues_card_pos _ _
end WLTime.OneTape.Symbolic
namespace WLTime
open OneTape.Symbolic OneTape.Symbolic.FullWriter
open scoped Classical
 theorem worstTime_ge (A : Model) (p : InputClass) {n : ℕ} (G H : Graph n) (hp : p.contains G H) :
    A.time n (encodePair G H)≤ worstTime A p n := by
  unfold worstTime
  exact (show A.time n (encodePair G H)≤ if p.contains G H then A.time n (encodePair G H) else 0 by simp [hp]).trans
    (Finset.le_sup (f:=fun pair : Graph n × Graph n => if p.contains pair.1 pair.2 then A.time n (encodePair pair.1 pair.2) else 0)
      (Finset.mem_univ (G,H)))
 theorem promised_pair (U : OneTape) (d q : ℕ) (hr : 2≤ d+q) (w : List Bool) (pad : ℕ) (p : InputClass) :
    p.contains (pairGraph U d q hr w pad 0) (pairGraph U d q hr w pad 1) := by
  cases p with
  | unrestricted => trivial
  | diameterTwo => exact ⟨pairGraph_diameter U d q hr w pad 0,pairGraph_diameter U d q hr w pad 1⟩

 theorem designation_small (U : OneTape) (d q : ℕ) (A : TM) :
    ∃m₀,∀m≥ m₀,∀n≤ m^8,(Diagonal.designation (consumer U d q A n)).length≤ m := by
  let K := statesBound U d q A+alphabetBound U d q A+3
  obtain ⟨m₀,hm₀⟩ := Numeric.polylog_sublinear (13*(K*9)^3) 3
  refine ⟨m₀,?_⟩
  intro m hm n hn
  have hd := Numeric.digits_polynomial n m 8 (by decide) hn
  let B := K*((Nat.digits 2 n).length+1)
  have hq : (consumer U d q A n).states≤ B := by
    exact (consumer_states U d q A n).trans (Nat.mul_le_mul_right _ (by dsimp [K]; omega))
  have hg : (consumer U d q A n).symbols≤ B := by
    have h := consumer_alphabet U d q A n
    dsimp [B,K]; nlinarith
  have hB : 3≤ B := by dsimp [B,K]; nlinarith
  calc
    _≤ 13*B^3 := Diagonal.designation_upper _ B hq hg hB
    _≤ 13*(K*9*((Nat.digits 2 m).length+1))^3 := by
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_left
      dsimp [B]
      nlinarith
    _=(13*(K*9)^3)*((Nat.digits 2 m).length+1)^3 := by ring
    _≤ m := hm₀ m hm

 theorem time_window (m s : ℕ) (hm : 2≤ m) (hs : 1≤ s) : m^(2*s+5)≤ m^(3*s+6)-1 := by
  have he : 2*s+5+1≤ 3*s+6 := by omega
  have hp := Nat.pow_le_pow_right (by omega : 0< m) he
  have hpos : 1≤ m^(2*s+5) := one_le_pow₀ (by omega)
  rw [pow_succ] at hp
  have hh : m^(2*s+5)+1≤ m^(2*s+5)*m := by
    exact Numeric.grow_one _ _ hm hpos
  exact Nat.le_sub_one_of_lt (lt_of_lt_of_le (Nat.lt_add_one _) (hh.trans hp))

 theorem space_window (m d q : ℕ) (hm : 2≤ m) (hd : 1≤ d) (hq : d+3≤ q) :
    2*(m^d-1)+m+2< m^(q+1) := by
  have hp := Nat.pow_le_pow_right (by omega : 0< m) (show d+2≤ q+1 by omega)
  have hmd := Nat.le_self_pow (by omega : d≠0) m
  rw [pow_add,pow_two] at hp
  have hm2 : 4≤ m*m := by nlinarith only [hm]
  have hx : m^d*4≤ m^(q+1) := (Nat.mul_le_mul_left (m^d) hm2).trans hp
  have ht : 0< m^d := pow_pos (by omega) _
  have hl := Numeric.space_arith m (m^d) hmd ht
  exact hl.trans_le (by simpa only [Nat.mul_comm] using hx)
end WLTime
namespace WLTime
open OneTape.Symbolic OneTape.Symbolic.FullWriter
open scoped Classical
 theorem pair_correct_convention (U : OneTape) (d q : ℕ) (hr : 2≤ d+q) (w : List Bool)
    (hm : 2≤ w.length) (pad : ℕ) (hL : 2*(w.length^d-1)+w.length+2< w.length^(q+1))
    (c : Convention) (k : ℕ) (hk : k=d+q+conventionShift c) :
    Equivalent c k (pairGraph U d q hr w pad 0) (pairGraph U d q hr w pad 1) ↔
      ¬∃t≤ w.length^d-1,(U.toTM.run w t).state.val=1 := by
  subst k
  cases c with
  | joint => exact (pairGraph_correct U d q hr w hm pad hL).1
  | separate => exact (pairGraph_correct U d q hr w hm pad hL).2

 theorem tm_pointwise (s d q k a n m : ℕ) (c : Convention) (p : InputClass) (A : TM)
    (hA : Decides (.turing A) c k p) (hk : k=d+q+conventionShift c)
    (hm : 128≤ m) (hs : 1≤ s) (hd : d=3*s+6) (hq : d+3≤ q)
    (ha : 2*max 2400 (8*a+1)+3≤ s)
    (hbase : baseOrder (Universal.machine s) d q m≤ n) (hn : n≤ m^8)
    (hfit : (Diagonal.designation (consumer (Universal.machine s) d q A n)).length≤ m)
    (hC : coefficient (Universal.machine s) d q (d+q+2)≤ m)
    (hcharge : (body (Universal.machine s) d q).charge≤ m)
    (hfactor : consumerFactor (Universal.machine s) d q A≤ m)
    (hAfac : 8*A.tapes+2≤ m)
    (hUfac : 8*((Universal.boundedProgram s).scratch+Fintype.card Universal.Reg+1)*1200^2≤ m)
    (hsm : 18*s≤ m) :
    ¬worstTime (.turing A) p n≤ n^a := by
  intro hfast
  let U := Universal.machine s
  let D := consumer U d q A n
  let z := List.replicate (m-(Diagonal.designation D).length) false
  let w := Diagonal.designation D++z
  have hlen : w.length=m := by
    dsimp [w,z]
    rw [List.length_append,List.length_replicate,Nat.add_sub_of_le hfit]
  have hr : 2≤ d+q := by omega
  let G := pairGraph U d q hr w (n-baseOrder U d q w.length) 0
  let H := pairGraph U d q hr w (n-baseOrder U d q w.length) 1
  let ys := encodePair G H
  have hgn : (listing U d q (d+q+2) w (n-baseOrder U d q w.length)).items.length=n := by
    rw [listing_length,hlen,Nat.add_sub_of_le hbase]
  have hprom : p.contains G H := promised_pair U d q hr w _ p
  have hdec := hA _ G H hprom
  change A.halts ys ∧ (A.accepts ys ↔ Equivalent c k G H) at hdec
  have htime : A.time ys≤ n^a := by
    have ht := worstTime_ge (.turing A) p G H hprom
    change A.time ys≤ worstTime (.turing A) p _ at ht
    rw [hgn] at ht
    exact ht.trans hfast
  have hprod := consumer_correct U d q A n w (by rw [hlen]; omega) hr
    (by simpa only [hlen] using hbase) ys rfl (A.time ys) (A.time_halted ys hdec.1)
  have hy : ys.length≤ m^20 := by
    have hy := input_length U d q n w hr (by simpa only [hlen] using hbase)
    exact hy.le.trans (Numeric.input_small n m (by omega) hn)
  have hb : budget U d q n w.length≤ m^2400 := by
    rw [hlen]
    simpa only [budget,encodeNat_length] using
      Numeric.writer_small (coefficient U d q (d+q+2)) (body U d q).charge n m hm hC hcharge hn
  have hv : A.time ys≤ m^(8*a) := by
    calc
      _≤ n^a := htime
      _≤(m^8)^a := Nat.pow_le_pow_left hn a
      _=m^(8*a) := (pow_mul m 8 a).symm
  have hDtime : D.toTM.time w≤ m^s := by
    have hbnd := Numeric.consumer_small m a (budget U d q n w.length) ys.length (A.time ys)
      (consumerFactor U d q A) (8*A.tapes+2) (by omega) hb hy hv hfactor hAfac
    have ht := hprod.2.1
    rw [hlen] at ht hbnd
    exact ht.trans (hbnd.trans (Nat.pow_le_pow_right (by omega) ha))
  have hU := Universal.machine_correct s D z (by change 0< w.length; rw [hlen]; omega)
  change U.toTM.halts w ∧ U.toTM.time w≤ Universal.timeBound s D w.length ∧
    (U.toTM.accepts w ↔ ¬∃t≤ w.length^s,(D.toTM.run w t).state.val=1) at hU
  have hUt : U.toTM.time w≤ w.length^d-1 := by
    apply hU.2.1.trans
    rw [hlen]
    apply (Universal.timeBound_small s D hfit (by omega) hs hsm hUfac).trans
    simpa only [hd] using time_window m s (by omega) hs
  have hwin : 2*(w.length^d-1)+w.length+2< w.length^(q+1) := by
    rw [hlen]; exact space_window m d q (by omega) (by omega) hq
  have hpair := pair_correct_convention U d q hr w (by rw [hlen]; omega) (n-baseOrder U d q w.length) hwin c k hk
  have hUb := Diagonal.bounded_accepts_iff U w (w.length^d-1) hU.1 hUt
  have hEq : Equivalent c k G H ↔ ¬U.toTM.accepts w := hpair.trans (not_congr hUb)
  have hc : D.toTM.accepts w ↔ ¬∃t≤ m^s,(D.toTM.run w t).state.val=1 := by
    have hh := hprod.2.2.trans (not_congr (hdec.2.trans hEq))
    rw [not_not] at hh
    exact hh.trans (by simpa only [hlen] using hU.2.2)
  exact Diagonal.pointwise_contradiction D w (m^s) hprod.1 hDtime hc
end WLTime

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Transducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uK uA uT

namespace WLTime
open OneTape.Symbolic OneTape.Symbolic.FullWriter
open scoped Classical
 theorem tm_integer_lower (k : ℕ) (hk : 100000000 ≤ k) (c : Convention) (p : InputClass) (A : TM)
    (hA : Decides (.turing A) c k p) :
    ∃ n₀,∀ n ≥ n₀,n^(k/1000) < worstTime (.turing A) p n := by
  let s := k/16
  let d := 3*s+6
  let q := k-d-conventionShift c
  let U := Universal.machine s
  let C := coefficient U d q (d+q+2)
  have hshift : 1 ≤ conventionShift c ∧ conventionShift c ≤ 2 := by cases c <;> decide
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hdim : k=d+q+conventionShift c := by dsimp [d,q,s]; omega
  have hq : d+3 ≤ q := by dsimp [q,d,s]; omega
  have ha : 2*max 2400 (8*(k/1000)+1)+3 ≤ s := by
    rcases max_cases 2400 (8*(k/1000)+1) with ⟨he,_⟩ | ⟨he,_⟩ <;> rw [he] <;> dsimp [s] <;> omega
  have hCpos : 1 ≤ C := coefficient_pos U d q
  obtain ⟨mfit,hfit⟩ := designation_small U d q A
  let m₀ := mfit+384*C^3+128+C+(body U d q).charge+consumerFactor U d q A+
    (8*A.tapes+2)+(8*((Universal.boundedProgram s).scratch+Fintype.card Universal.Reg+1)*1200^2)+18*s
  refine ⟨baseOrder U d q m₀,?_⟩
  intro n hn
  let m := Numeric.chooseOrder C n
  have hchoice := Numeric.chooseOrder_bounds C n m₀ hCpos hn
  have hm : m₀ ≤ m := hchoice.1
  have hbase : baseOrder U d q m ≤ n := hchoice.2.1
  have hmn : n ≤ m^8 := Numeric.order_polynomial C n m hCpos (by dsimp [m₀] at hm; omega) hchoice.2.2
  apply lt_of_not_ge
  exact tm_pointwise s d q k (k/1000) n m c p A hA hdim
    (by dsimp [m₀] at hm; omega) hs rfl hq ha hbase hmn
    (hfit m (by dsimp [m₀] at hm; omega) n hmn)
    (by change C≤ m; dsimp only [m₀] at hm; omega)
    (by change (body U d q).charge≤ m; dsimp only [m₀] at hm; omega)
    (by change consumerFactor U d q A≤ m; dsimp only [m₀] at hm; omega)
    (by dsimp [m₀] at hm; omega)
    (by dsimp [m₀] at hm; omega)
    (by dsimp [m₀] at hm; omega)

 theorem tm_real_lower (k : ℕ) (hk : 100000000 ≤ k) (c : Convention) (p : InputClass) (A : TM)
    (hA : Decides (.turing A) c k p) :
    ∃ n₀ : ℕ,∀ n : ℕ, n ≥ n₀ → (n : ℝ)^((1/2000 : ℝ)*(k : ℝ)) ≤ (worstTime (.turing A) p n : ℝ) := by
  obtain ⟨n₀,hn₀⟩ := tm_integer_lower k hk c p A hA
  refine ⟨n₀+1,?_⟩
  intro n hn
  have hint := hn₀ n (by omega)
  have hexp : (1/2000 : ℝ)*(k : ℝ) ≤ (k/1000 : ℕ) := by
    have h : k ≤ 2000*(k/1000) := by omega
    have hr : (k : ℝ) ≤ 2000*((k/1000 : ℕ) : ℝ) := by exact_mod_cast h
    linarith
  calc
    _ ≤ (n : ℝ)^((k/1000 : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ n by omega)) hexp
    _ = (n : ℝ)^(k/1000) := Real.rpow_natCast _ _
    _ ≤ (worstTime (.turing A) p n : ℝ) := by exact_mod_cast hint.le
end WLTime

end OAI
end

section
-- module Solutions.OAIQW_WLTime.RAMSimulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uK uX uT

namespace WLTime.RAMAlphabet
open TypedStack
open scoped Classical
noncomputable section
variable (A : RAM)
 theorem opCost_bound (w : ℕ) (op : WordOperation A.registers) :
    opCost A w op ≤ opConstant A op*(w+1)^(op.exponent+1) := by
  have hl := encode_length_bound w
  have hp : w+1≤(w+1)^(op.exponent+1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0<w+1) (by omega : 1≤op.exponent+1)
  have hq : (w+1)^op.exponent≤(w+1)^(op.exponent+1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hr : 2*(A.registers*w)≤2*A.registers*((w+1)^(op.exponent+1)) := by
    calc
      _=2*A.registers*w := by ring
      _≤_ := Nat.mul_le_mul_left _ (by omega)
  have hc := Nat.mul_le_mul_left op.constant hq
  have hin : (encodeNat w).length+2*(A.registers*w)+op.constant*(w+1)^op.exponent+1≤
      (2*A.registers+op.constant+4)*(w+1)^(op.exponent+1) := by nlinarith only [hl,hp,hr,hc]
  have hh := Nat.mul_le_mul_left (TMPort.factor op.implementation) hin
  dsimp only [opCost,opConstant]
  nlinarith only [hl,hp,hh]
 theorem unitCost_bound (w : ℕ) : unitCost A w ≤ constant A*(w+1)^exponent A := by
  have he : 1≤exponent A := by unfold exponent; omega
  have hw : w+1≤(w+1)^exponent A := by simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0<w+1) he
  have hs : (∑i : Index A,opCost A w (operation A i)) ≤
      (∑i : Index A,opConstant A (operation A i))*(w+1)^exponent A := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    have hi : (operation A i).exponent+1≤exponent A := by
      have hh := Finset.le_sup (f:=fun i : Index A => (operation A i).exponent) (Finset.mem_univ i)
      unfold exponent; omega
    exact (opCost_bound A w (operation A i)).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hi))
  have hb := Nat.mul_le_mul_left (1000*(A.registers+1)) hw
  dsimp only [unitCost,constant]
  nlinarith only [hs,hb]
end
end WLTime.RAMAlphabet

end OAI
end

section
-- module Solutions.OAIQW_WLTime.RAMBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uK uX

namespace WLTime.RAMAlphabet
open scoped Classical
noncomputable section
variable (A : RAM)
 theorem budget_bound (w len time : ℕ) :
    budget A w len time≤budgetConstant A*(w+1)^exponent A*(len+time+1)^2 := by
  let W := (w+1)^exponent A
  let X := len+time+1
  have he : 1≤exponent A := by unfold exponent; omega
  have hw : w+1≤W := by simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0<w+1) he
  have hW : 1≤W := by omega
  have hX : 1≤X := by dsimp [X]; omega
  have ht : time≤X := by dsimp [X]; omega
  have hl : len+1≤X := by dsimp [X]; omega
  have hXX : X≤X^2 := Nat.le_self_pow (by decide) X
  have hi : initBound A w len≤100*(A.registers+1)*W*X^2 := by
    exact (Nat.mul_le_mul (Nat.mul_le_mul_left _ hw) hl).trans (Nat.mul_le_mul_left _ hXX)
  have hc := unitCost_bound A w
  have hL : len+time*depth A+depth A+1≤(depth A+1)*X := by dsimp [X]; nlinarith
  have hs : stepBound A w (len+time*depth A)≤constant A*W*depth A*((depth A+1)*X)+A.locations := by
    unfold stepBound
    exact Nat.add_le_add_right (Nat.mul_le_mul (Nat.mul_le_mul_right _ hc) hL) _
  have hremain : (stepBound A w (len+time*depth A)+1)*time+1≤
      (constant A*depth A*(depth A+1)+A.locations+2)*W*X^2 := by
    have hz : stepBound A w (len+time*depth A)+1≤
        (constant A*depth A*(depth A+1)+A.locations+1)*W*X := by
      have hWX : 1≤W*X := Nat.mul_le_mul hW hX
      have hP := Nat.mul_le_mul_left (A.locations+1) hWX
      nlinarith only [hs,hP]
    have hmul := Nat.mul_le_mul hz ht
    have hWX2 : 1≤W*X^2 := Nat.mul_le_mul hW (one_le_pow₀ hX)
    nlinarith only [hmul,hWX2]
  dsimp only [budget,budgetConstant]
  change initBound A w len+(stepBound A w (len+time*depth A)+1)*time+1≤
    (100*(A.registers+1)+constant A*depth A*(depth A+1)+A.locations+2)*W*X^2
  nlinarith only [hi,hremain]
end
end WLTime.RAMAlphabet

namespace WLTime.RAMConsumer
open TypedStack
noncomputable section
variable {K : Type uK} [DecidableEq K] (A : RAM)
attribute [local instance] OAI.WLTime.RAMConsumer.instDecidableEqReg
local instance instDecidableEqLetter_r28a838_1 : DecidableEq (Letter A) := Classical.decEq _
variable [Fintype K]
 omit [DecidableEq K] [Fintype K] in
 theorem code_size (c : Code K Bool) (output : K) (w : ℕ) :
    (code A c output w).controlSize=c.controlSize+(RAMAlphabet.program A w).controlSize+5 := by
  simp only [code,preludeCode,Code.controlSize,Code.relabel_controlSize,Code.mapLetters_controlSize,Code.transfer]
  omega
end
end WLTime.RAMConsumer

namespace WLTime.OneTape.Symbolic.RAMWriter
open TypedStack
open scoped Classical
noncomputable section
variable (U : OneTape) (d q : ℕ) (A : RAM)
 theorem ramSize_spec (w : ℕ) : (RAMAlphabet.program A w).controlSize ≤ ramSize A*(w+1) :=
  Classical.choose_spec (RAMAlphabet.program_linear A) w
 theorem consumer_alphabet (n : ℕ) : (consumer U d q A n).symbols ≤ alphabetBound U d q A := by
  unfold consumer RAMConsumer.oneTape Code.haltOneTape
  rw [StackMachine.Machine.compile_symbols]
  change 3+2*((2+Fintype.card (RAMAlphabet.Letter A))+1)^Fintype.card
    (RAMConsumer.Reg A (Fin (FullWriter.program U d q n).scratch ⊕ FullWriter.Reg)) ≤ _
  have hreg : Fintype.card (RAMConsumer.Reg A (Fin (FullWriter.program U d q n).scratch ⊕ FullWriter.Reg)) =
      (FullWriter.program U d q n).scratch+4+Fintype.card (RAMAlphabet.Reg A) := by
    rw [Fintype.card_sum,Fintype.card_sum,Fintype.card_fin,FullWriter.card_reg]
  rw [hreg]
  have hs := FullWriter.scratch_le U d q n
  unfold alphabetBound tapesBound
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  rw [show 2+Fintype.card (RAMAlphabet.Letter A)+1=3+Fintype.card (RAMAlphabet.Letter A) by omega]
  exact Nat.pow_le_pow_right (by omega) (by omega)
 theorem consumer_states (n : ℕ) :
    (consumer U d q A n).states ≤ statesBound U d q A*((Nat.digits 2 n).length+A.width.bits n+2) := by
  have h := StackMachine.Machine.compile_states_bound
    (Code.haltMachine (RAMConsumer.code A (FullWriter.program U d q n).code (.inr FullWriter.Reg.output) (A.width.bits n))
      (.inl (.inr FullWriter.Reg.word)) Sum.inl (RAMConsumer.answer A)).compile
  change (consumer U d q A n).states ≤ 3+14*(Fintype.card
    (RAMConsumer.Reg A (Fin (FullWriter.program U d q n).scratch ⊕ FullWriter.Reg))+1)*
    (2+Fintype.card (RAMAlphabet.Letter A)+1)*
    (Fintype.card (Code.HaltState (RAMConsumer.code A (FullWriter.program U d q n).code (.inr FullWriter.Reg.output) (A.width.bits n)))+1)*
    (2+Fintype.card (RAMAlphabet.Letter A)+1)^Fintype.card
      (RAMConsumer.Reg A (Fin (FullWriter.program U d q n).scratch ⊕ FullWriter.Reg)) at h
  have hreg : Fintype.card (RAMConsumer.Reg A (Fin (FullWriter.program U d q n).scratch ⊕ FullWriter.Reg)) =
      (FullWriter.program U d q n).scratch+4+Fintype.card (RAMAlphabet.Reg A) := by
    rw [Fintype.card_sum,Fintype.card_sum,Fintype.card_fin,FullWriter.card_reg]
  rw [hreg] at h
  have hstate : Fintype.card (Code.HaltState (RAMConsumer.code A (FullWriter.program U d q n).code (.inr FullWriter.Reg.output) (A.width.bits n))) =
      (RAMConsumer.code A (FullWriter.program U d q n).code (.inr FullWriter.Reg.output) (A.width.bits n)).controlSize+1 := by
    rw [Fintype.card_sum,Code.card_state,Fintype.card_unit]
  rw [hstate,RAMConsumer.code_size] at h
  let Y := (Nat.digits 2 n).length+A.width.bits n+2
  let B := 3+Fintype.card (RAMAlphabet.Letter A)
  have hK : (FullWriter.program U d q n).scratch+4+Fintype.card (RAMAlphabet.Reg A) ≤ tapesBound U d q A := by
    have hs := FullWriter.scratch_le U d q n
    unfold tapesBound; omega
  have hq : (FullWriter.program U d q n).code.controlSize+(RAMAlphabet.program A (A.width.bits n)).controlSize+5+1+1 ≤
      (FullWriter.syntaxBound U d q+ramSize A+7)*Y := by
    have hs := FullWriter.syntax_le U d q n
    have hr := ramSize_spec A (A.width.bits n)
    dsimp only [Y]
    nlinarith only [hs,hr]
  have hp : B^((FullWriter.program U d q n).scratch+4+Fintype.card (RAMAlphabet.Reg A)) ≤ B^tapesBound U d q A :=
    Nat.pow_le_pow_right (by dsimp [B]; omega) hK
  rw [show 2+Fintype.card (RAMAlphabet.Letter A)+1=B by dsimp [B]; omega] at h
  have ht := Nat.mul_le_mul_right B (Nat.mul_le_mul_left 14 (Nat.add_le_add_right hK 1))
  have hz := Nat.add_le_add_left (Nat.mul_le_mul (Nat.mul_le_mul ht hq) hp) 3
  have hh := h.trans hz
  change (consumer U d q A n).states ≤ statesBound U d q A*Y
  unfold statesBound
  change (consumer U d q A n).states ≤ (3+14*(tapesBound U d q A+1)*B*(FullWriter.syntaxBound U d q+ramSize A+7)*B^tapesBound U d q A)*Y
  have hY : 1 ≤ Y := by dsimp [Y]; omega
  nlinarith only [hh,hY]
end
end WLTime.OneTape.Symbolic.RAMWriter

namespace WLTime.Numeric
 theorem ram_consumer_small (m a writer len time ram factor : ℕ) (hm : 8 ≤ m)
    (hb : writer ≤ m^2400) (hl : len ≤ m^20) (ht : time ≤ m^(8*a))
    (hr : ram ≤ m*(len+time+1)^2) (hf : factor ≤ m) :
    factor*(m+writer+5*len+ram+3)^2 ≤ m^(2*max 2400 (16*a+45)+3) := by
  let E := max 20 (8*a)
  let D := max 2400 (16*a+45)
  have hle : len ≤ m^E := hl.trans (pow_mono m 20 E (by omega) (le_max_left _ _))
  have hte : time ≤ m^E := ht.trans (pow_mono m (8*a) E (by omega) (le_max_right _ _))
  have hsum := sum_le_pow (by omega : 2 ≤ m) hle hte
  have hone : 1 ≤ m^(E+1) := one_le_pow₀ (by omega)
  have hsum' : len+time+1 ≤ m^(E+2) := by
    simpa only [show E+1+1=E+2 by omega] using sum_le_pow (by omega : 2 ≤ m) hsum hone
  have hram : ram ≤ m^(16*a+45) := by
    calc
      _ ≤ m*(len+time+1)^2 := hr
      _ ≤ m*(m^(E+2))^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsum' 2)
      _=m^(2*E+5) := by rw [←pow_mul,←pow_succ']; congr 1; omega
      _ ≤ m^(16*a+45) := pow_mono m _ _ (by omega) (by dsimp [E]; omega)
  have h5 : 5*len ≤ m^21 := by
    have h := Nat.mul_le_mul (show 5 ≤ m by omega) hl
    simpa only [pow_succ'] using h
  have hmD : m ≤ m^D := Nat.le_self_pow (by dsimp [D]; omega) m
  have hwD : writer ≤ m^D := hb.trans (pow_mono m 2400 D (by omega) (le_max_left _ _))
  have hlD : 5*len ≤ m^D := h5.trans (pow_mono m 21 D (by omega) (by dsimp [D]; omega))
  have hrD : ram ≤ m^D := hram.trans (pow_mono m (16*a+45) D (by omega) (le_max_right _ _))
  have h3D : 3 ≤ m^D := (by omega : 3 ≤ m).trans hmD
  have hbase : m+writer+5*len+ram+3 ≤ m^(D+1) := by
    rw [pow_succ]
    nlinarith only [hmD,hwD,hlD,hrD,h3D,hm]
  calc
    _ ≤ m*(m^(D+1))^2 := Nat.mul_le_mul hf (Nat.pow_le_pow_left hbase 2)
    _=m^(2*D+3) := by rw [←pow_mul,←pow_succ']; congr 1; omega
end WLTime.Numeric

namespace WLTime.OneTape.Symbolic.RAMWriter
open scoped Classical
noncomputable section
variable (A : RAM)
 theorem width_small (n m : ℕ) (hm : 2 ≤ m) (hn : n ≤ m^8) :
    A.width.bits n+1 ≤ widthFactor A*((Nat.digits 2 m).length+1) := by
  have hm8 : m ≤ m^8 := Nat.le_self_pow (by decide) m
  have hnm : n+2 ≤ m^9 := by
    simpa using Numeric.sum_le_pow hm hn (show 2 ≤ m^8 by omega)
  have hd := Numeric.digits_polynomial (n+2) m 9 (by decide) hnm
  have he : Nat.log2 (n+2)+1=(Nat.digits 2 (n+2)).length := by
    rw [Nat.length_digits 2 (n+2) (by decide) (by omega),Nat.log2_eq_log_two]
  have hw := A.width.logarithmic n
  rw [he] at hw
  have hx := Nat.mul_le_mul_left A.width.bound hd
  unfold widthFactor
  nlinarith only [hw,hx]
 theorem word_cost_small : ∃m₀,∀m ≥ m₀,∀n ≤ m^8,
    RAMAlphabet.budgetConstant A*(A.width.bits n+1)^RAMAlphabet.exponent A ≤ m := by
  obtain ⟨m₀,hm₀⟩ := Numeric.polylog_sublinear
    (RAMAlphabet.budgetConstant A*(widthFactor A)^RAMAlphabet.exponent A) (RAMAlphabet.exponent A)
  refine ⟨m₀+2,?_⟩
  intro m hm n hn
  have hw := width_small A n m (by omega) hn
  calc
    _ ≤ RAMAlphabet.budgetConstant A*(widthFactor A*((Nat.digits 2 m).length+1))^RAMAlphabet.exponent A :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hw _)
    _=(RAMAlphabet.budgetConstant A*(widthFactor A)^RAMAlphabet.exponent A)*((Nat.digits 2 m).length+1)^RAMAlphabet.exponent A := by rw [mul_pow]; ring
    _ ≤ m := hm₀ m (by omega)
variable (U : OneTape) (d q : ℕ)
 theorem designation_small : ∃m₀,∀m ≥ m₀,∀n ≤ m^8,
    (Diagonal.designation (consumer U d q A n)).length ≤ m := by
  let K := statesBound U d q A+alphabetBound U d q A+3
  let F := 9+widthFactor A
  obtain ⟨m₀,hm₀⟩ := Numeric.polylog_sublinear (13*(K*F)^3) 3
  refine ⟨m₀+2,?_⟩
  intro m hm n hn
  let Y := (Nat.digits 2 n).length+A.width.bits n+2
  let B := K*Y
  have hd := Numeric.digits_polynomial n m 8 (by decide) hn
  have hw := width_small A n m (by omega) hn
  have hY : Y ≤ F*((Nat.digits 2 m).length+1) := by dsimp [Y,F]; nlinarith only [hd,hw]
  have hq : (consumer U d q A n).states ≤ B :=
    (consumer_states U d q A n).trans (Nat.mul_le_mul_right _ (by dsimp [K]; omega))
  have hg : (consumer U d q A n).symbols ≤ B := by
    have h := consumer_alphabet U d q A n
    dsimp [B,K,Y]
    nlinarith
  have hB : 3 ≤ B := by dsimp [B,K,Y]; nlinarith
  calc
    _ ≤ 13*B^3 := Diagonal.designation_upper _ B hq hg hB
    _ ≤ 13*(K*F*((Nat.digits 2 m).length+1))^3 := by
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_left
      have h := Nat.mul_le_mul_left K hY
      simpa only [B,Nat.mul_assoc] using h
    _=(13*(K*F)^3)*((Nat.digits 2 m).length+1)^3 := by ring
    _ ≤ m := hm₀ m (by omega)
end
end WLTime.OneTape.Symbolic.RAMWriter

namespace WLTime
open OneTape.Symbolic OneTape.Symbolic.FullWriter
open scoped Classical
 theorem diagonal_graph_contradiction (s d q k m pad : ℕ) (c : Convention) (D : OneTape)
    (w z : List Bool) (hw : w=Diagonal.designation D++z) (hlen : w.length=m)
    (hk : k=d+q+conventionShift c) (hm : 128 ≤ m) (hs : 1 ≤ s)
    (hd : d=3*s+6) (hq : d+3 ≤ q) (hr : 2 ≤ d+q)
    (hfit : (Diagonal.designation D).length ≤ m)
    (hUfac : 8*((Universal.boundedProgram s).scratch+Fintype.card Universal.Reg+1)*1200^2 ≤ m)
    (hsm : 18*s ≤ m) (hhalt : D.toTM.halts w) (htime : D.toTM.time w ≤ m^s)
    (hpairD : D.toTM.accepts w ↔ ¬Equivalent c k
      (pairGraph (Universal.machine s) d q hr w pad 0)
      (pairGraph (Universal.machine s) d q hr w pad 1)) : False := by
  let U := Universal.machine s
  have hU := Universal.machine_correct s D z (by rw [←hw,hlen]; omega)
  rw [←hw] at hU
  have hUt : U.toTM.time w ≤ w.length^d-1 := by
    apply hU.2.1.trans
    rw [hlen]
    apply (Universal.timeBound_small s D hfit (by omega) hs hsm hUfac).trans
    simpa only [hd] using time_window m s (by omega) hs
  have hwin : 2*(w.length^d-1)+w.length+2<w.length^(q+1) := by
    rw [hlen]; exact space_window m d q (by omega) (by omega) hq
  have hpair := pair_correct_convention U d q hr w (by rw [hlen]; omega) pad hwin c k hk
  have hUb := Diagonal.bounded_accepts_iff U w (w.length^d-1) hU.1 hUt
  have hEq := hpair.trans (not_congr hUb)
  have hc : D.toTM.accepts w ↔ ¬∃t ≤ m^s,(D.toTM.run w t).state.val=1 := by
    have hh := hpairD.trans (not_congr hEq)
    rw [not_not] at hh
    exact hh.trans (by simpa only [hlen] using hU.2.2)
  exact Diagonal.pointwise_contradiction D w (m^s) hhalt htime hc
end WLTime

namespace WLTime
open OneTape.Symbolic OneTape.Symbolic.FullWriter
open scoped Classical
 theorem ram_decides_pair (U : OneTape) (d q k n a : ℕ) (w : List Bool)
    (hr : 2 ≤ d+q) (hbase : baseOrder U d q w.length ≤ n)
    (c : Convention) (p : InputClass) (A : RAM) (hA : Decides (.ram A) c k p)
    (hfast : worstTime (.ram A) p n ≤ n^a) :
    let G := pairGraph U d q hr w (n-baseOrder U d q w.length) 0
    let H := pairGraph U d q hr w (n-baseOrder U d q w.length) 1
    let ys := encodePair G H
    A.halts n ys ∧ A.time n ys ≤ n^a ∧ (A.accepts n ys ↔ Equivalent c k G H) := by
  dsimp only
  let G := pairGraph U d q hr w (n-baseOrder U d q w.length) 0
  let H := pairGraph U d q hr w (n-baseOrder U d q w.length) 1
  let ys := encodePair G H
  have hgn : (listing U d q (d+q+2) w (n-baseOrder U d q w.length)).items.length=n := by
    rw [listing_length,Nat.add_sub_of_le hbase]
  have hprom : p.contains G H := promised_pair U d q hr w _ p
  have hdec := hA _ G H hprom
  change A.halts _ ys ∧ (A.accepts _ ys ↔ Equivalent c k G H) at hdec
  have hhalt : A.halts n ys := by simpa only [hgn] using hdec.1
  have haccept : A.accepts n ys ↔ Equivalent c k G H := by
    have he : A.accepts n ys=A.accepts (listing U d q (d+q+2) w (n-baseOrder U d q w.length)).items.length ys :=
      congrArg (fun j => A.accepts j ys) hgn.symm
    rw [he]
    exact hdec.2
  have htime : A.time n ys ≤ n^a := by
    have ht := worstTime_ge (.ram A) p G H hprom
    change A.time _ ys ≤ worstTime (.ram A) p _ at ht
    rw [hgn] at ht
    exact ht.trans hfast
  exact ⟨hhalt,htime,haccept⟩
 theorem ram_pointwise (s d q k a n m : ℕ) (c : Convention) (p : InputClass) (A : RAM)
    (hA : Decides (.ram A) c k p) (hk : k=d+q+conventionShift c)
    (hm : 128 ≤  m) (hs : 1 ≤  s) (hd : d=3*s+6) (hq : d+3 ≤  q)
    (ha : 2*max 2400 (16*a+45)+3 ≤  s)
    (hbase : baseOrder (Universal.machine s) d q m ≤  n) (hn : n ≤  m^8)
    (hfit : (Diagonal.designation (RAMWriter.consumer (Universal.machine s) d q A n)).length ≤  m)
    (hC : coefficient (Universal.machine s) d q (d+q+2) ≤  m)
    (hcharge : (body (Universal.machine s) d q).charge ≤  m)
    (hfactor : RAMWriter.consumerFactor (Universal.machine s) d q A ≤  m)
    (hword : RAMAlphabet.budgetConstant A*(A.width.bits n+1)^RAMAlphabet.exponent A ≤ m)
    (hUfac : 8*((Universal.boundedProgram s).scratch+Fintype.card Universal.Reg+1)*1200^2 ≤  m)
    (hsm : 18*s ≤  m) :
    ¬worstTime (.ram A) p n ≤  n^a := by
  intro hfast
  let U := Universal.machine s
  let D := RAMWriter.consumer U d q A n
  let z := List.replicate (m-(Diagonal.designation D).length) false
  let w := Diagonal.designation D++z
  have hlen : w.length=m := by
    dsimp [w,z]
    rw [List.length_append,List.length_replicate,Nat.add_sub_of_le hfit]
  have hr : 2 ≤  d+q := by omega
  let G := pairGraph U d q hr w (n-baseOrder U d q w.length) 0
  let H := pairGraph U d q hr w (n-baseOrder U d q w.length) 1
  let ys := encodePair G H
  obtain ⟨hhalt,htime,haccept⟩ := ram_decides_pair U d q k n a w hr
    (by simpa only [hlen] using hbase) c p A hA hfast
  have hprod := RAMWriter.correct U d q A n w (by rw [hlen]; omega) hr
    (by simpa only [hlen] using hbase) ys rfl hhalt
  have hy : ys.length ≤  m^20 := by
    have hy := input_length U d q n w hr (by simpa only [hlen] using hbase)
    exact hy.le.trans (Numeric.input_small n m (by omega) hn)
  have hb : budget U d q n w.length ≤  m^2400 := by
    rw [hlen]
    simpa only [budget,encodeNat_length] using
      Numeric.writer_small (coefficient U d q (d+q+2)) (body U d q).charge n m hm hC hcharge hn
  have hv : A.time n ys ≤  m^(8*a) := by
    calc
      _ ≤  n^a := htime
      _ ≤ (m^8)^a := Nat.pow_le_pow_left hn a
      _=m^(8*a) := (pow_mul m 8 a).symm
  have hDtime : D.toTM.time w ≤  m^s := by
    have hramb : RAMAlphabet.budget A (A.width.bits n) ys.length (A.time n ys) ≤ m*(ys.length+A.time n ys+1)^2 :=
      (RAMAlphabet.budget_bound A _ _ _).trans (Nat.mul_le_mul_right _ hword)
    have hbnd := Numeric.ram_consumer_small m a (budget U d q n w.length) ys.length (A.time n ys)
      (RAMAlphabet.budget A (A.width.bits n) ys.length (A.time n ys)) (RAMWriter.consumerFactor U d q A)
      (by omega) hb hy hv hramb hfactor
    have ht := hprod.2.1
    rw [hlen] at ht hbnd
    exact ht.trans (hbnd.trans (Nat.pow_le_pow_right (by omega) ha))
  have heq : D.toTM.accepts w ↔ ¬Equivalent c k G H :=
    hprod.2.2.trans (not_congr haccept)
  exact diagonal_graph_contradiction s d q k m (n-baseOrder U d q w.length) c D w z rfl hlen
    hk hm hs hd hq hr hfit hUfac hsm hprod.1 hDtime heq
end WLTime

end OAI
end

section
-- module Solutions.OAIQW_WLTime.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLTime
open OneTape.Symbolic OneTape.Symbolic.FullWriter
open scoped Classical
 theorem ram_integer_lower (k : ℕ) (hk : 100000000  ≤  k) (c : Convention) (p : InputClass) (A : RAM)
    (hA : Decides (.ram A) c k p) :
    ∃ n₀,∀ n  ≥  n₀,n^(k/1000) < worstTime (.ram A) p n := by
  let s := k/16
  let d := 3*s+6
  let q := k-d-conventionShift c
  let U := Universal.machine s
  let C := coefficient U d q (d+q+2)
  have hshift : 1  ≤  conventionShift c ∧ conventionShift c  ≤  2 := by cases c <;> decide
  have hs : 1  ≤  s := by dsimp [s]; omega
  have hdim : k=d+q+conventionShift c := by dsimp [d,q,s]; omega
  have hq : d+3  ≤  q := by dsimp [q,d,s]; omega
  have ha : 2*max 2400 (16*(k/1000)+45)+3  ≤  s := by
    rcases max_cases 2400 (16*(k/1000)+45) with ⟨he,_⟩ | ⟨he,_⟩ <;> rw [he] <;> dsimp [s] <;> omega
  have hCpos : 1  ≤  C := coefficient_pos U d q
  obtain ⟨mfit,hfit⟩ := RAMWriter.designation_small A U d q
  obtain ⟨mword,hword⟩ := RAMWriter.word_cost_small A
  let m₀ := mfit+384*C^3+128+C+(body U d q).charge+RAMWriter.consumerFactor U d q A+
    mword+(8*((Universal.boundedProgram s).scratch+Fintype.card Universal.Reg+1)*1200^2)+18*s
  refine ⟨baseOrder U d q m₀,?_⟩
  intro n hn
  let m := Numeric.chooseOrder C n
  have hchoice := Numeric.chooseOrder_bounds C n m₀ hCpos hn
  have hm : m₀  ≤  m := hchoice.1
  have hbase : baseOrder U d q m  ≤  n := hchoice.2.1
  have hmn : n  ≤  m^8 := Numeric.order_polynomial C n m hCpos (by dsimp [m₀] at hm; omega) hchoice.2.2
  apply lt_of_not_ge
  exact ram_pointwise s d q k (k/1000) n m c p A hA hdim
    (by dsimp [m₀] at hm; omega) hs rfl hq ha hbase hmn
    (hfit m (by dsimp [m₀] at hm; omega) n hmn)
    (by change C ≤  m; dsimp only [m₀] at hm; omega)
    (by change (body U d q).charge ≤  m; dsimp only [m₀] at hm; omega)
    (by change RAMWriter.consumerFactor U d q A ≤  m; dsimp only [m₀] at hm; omega)
    (hword m (by dsimp [m₀] at hm; omega) n hmn)
    (by dsimp [m₀] at hm; omega)
    (by dsimp [m₀] at hm; omega)

end WLTime
namespace WLTime
 theorem ram_real_lower (k : ℕ) (hk : 100000000  ≤  k) (c : Convention) (p : InputClass) (A : RAM)
    (hA : Decides (.ram A) c k p) :
    ∃ n₀ : ℕ,∀ n : ℕ, n  ≥  n₀ → (n : ℝ)^((1/2000 : ℝ)*(k : ℝ))  ≤  (worstTime (.ram A) p n : ℝ) := by
  obtain ⟨n₀,hn₀⟩ := ram_integer_lower k hk c p A hA
  refine ⟨n₀+1,?_⟩
  intro n hn
  have hint := hn₀ n (by omega)
  have hexp : (1/2000 : ℝ)*(k : ℝ)  ≤  (k/1000 : ℕ) := by
    have h : k  ≤  2000*(k/1000) := by omega
    have hr : (k : ℝ)  ≤  2000*((k/1000 : ℕ) : ℝ) := by exact_mod_cast h
    linarith
  calc
    _  ≤  (n : ℝ)^((k/1000 : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1  ≤  n by omega)) hexp
    _ = (n : ℝ)^(k/1000) := Real.rpow_natCast _ _
    _  ≤  (worstTime (.ram A) p n : ℝ) := by exact_mod_cast hint.le
end WLTime

theorem WLTime.unconditional_time_lower_bound_oai : WLTime.MainClaim := by
  refine ⟨1/2000, by norm_num, 100000000, ?_⟩
  intro k hk convention p A hA
  cases A with
  | turing M => exact WLTime.tm_real_lower k hk convention p M hA
  | ram M => exact WLTime.ram_real_lower k hk convention p M hA

end OAI
end

theorem solution : type_of% @OAI.WLTime.unconditional_time_lower_bound_oai := @OAI.WLTime.unconditional_time_lower_bound_oai
