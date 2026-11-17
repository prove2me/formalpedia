-- Prove2me | solution 1 for PolySwap.KMS.theorem_3_19
-- status  : ACCEPTED   (prove)
-- author  : @typh
-- created : 2026-11-16T09:36:54.277894+00:00
-- url     : https://prove2.me/submissions/ef8e890b-72a5-4a6f-a30f-12257e1073a6

import Mathlib
import Definitions.Def_PolySwap_KMS_Complex
import Definitions.Def_PolySwap_KMS_Cone
import Definitions.Def_PolySwap_KMS_Dehn

open Classical

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace PolySwap.KMS.Sol319

open PolySwap.KMS WComplex

section General

variable {V : Type*} (X : WComplex V) (v₀ : V)

/-- Rewriting by `BT` (free) and `TR` (cost 1) moves, with an upper bound on the cost. -/
inductive Rw : ℕ → List V → List V → Prop
  | refl (n : ℕ) (A : List V) : Rw n A A
  | bt {n : ℕ} {A B C : List V} : X.BT v₀ A B → Rw n B C → Rw n A C
  | tr {n : ℕ} {A B C : List V} : X.TR v₀ A B → Rw n B C → Rw (n + 1) A C

variable {X v₀}

lemma Rw.mono {a : ℕ} {A B : List V} (h : Rw X v₀ a A B) : ∀ {b}, a ≤ b → Rw X v₀ b A B := by
  induction h with
  | refl n A => intro b _; exact Rw.refl b A
  | bt h _ ih => intro b hb; exact Rw.bt h (ih hb)
  | tr h _ ih =>
    intro b hb
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    exact Rw.tr h (ih (by omega))

lemma Rw.trans {a b : ℕ} {A B C : List V} (h : Rw X v₀ a A B) (h' : Rw X v₀ b B C) :
    Rw X v₀ (a + b) A C := by
  induction h with
  | refl n A => exact h'.mono (by omega)
  | bt h _ ih => exact Rw.bt h (ih h')
  | @tr n _ _ _ h _ ih =>
    have := Rw.tr h (ih h')
    rwa [show n + 1 + b = n + b + 1 by omega]

lemma Rw.symm {a : ℕ} {A B : List V} (h : Rw X v₀ a A B) : Rw X v₀ a B A := by
  induction h with
  | refl n A => exact Rw.refl n A
  | bt h _ ih => simpa using ih.trans (Rw.bt (Or.symm h) (Rw.refl 0 _))
  | tr h _ ih => simpa using ih.trans (Rw.tr (Or.symm h) (Rw.refl 0 _))

lemma len_of_BT {A B : List V} (h : X.BTstep v₀ A B) : A.length = B.length + 2 := by
  obtain ⟨u, v, Q₀, Q₁, -, ⟨⟨hQ, -⟩, -⟩, -, -, rfl, rfl⟩ := h
  have : Q₁.length ≠ 0 := by simpa using hQ
  simp [pcat]; omega

lemma len_of_TR {A B : List V} (h : X.TRstep v₀ A B) : A.length = B.length + 1 := by
  obtain ⟨u, v, w, Q₀, Q₁, -, -, -, -, -, ⟨⟨hQ, -⟩, -⟩, rfl, rfl⟩ := h
  have : Q₁.length ≠ 0 := by simpa using hQ
  simp [pcat]; omega

lemma not_TR_of_BT {A B : List V} (h : X.BT v₀ A B) : ¬ X.TR v₀ A B := by
  rintro (h' | h') <;> rcases h with h | h <;>
    · have := len_of_BT h; have := len_of_TR h'; omega

lemma trCount_cons_cons (A B : List V) (l : List (List V)) :
    X.trCount v₀ (A :: B :: l) = (if X.TR v₀ A B then 1 else 0) + X.trCount v₀ (B :: l) := by
  simp only [trCount, List.tail_cons, List.zip_cons_cons, List.countP_cons, decide_eq_true_eq]
  split_ifs <;> omega

lemma Rw.chain {n : ℕ} {A B : List V} (h : Rw X v₀ n A B) :
    ∃ l : List (List V), l.head? = some A ∧ l.getLast? = some B ∧
      l.IsChain (fun A B => X.TR v₀ A B ∨ X.BT v₀ A B) ∧ X.trCount v₀ l ≤ n := by
  induction h with
  | refl n A => exact ⟨[A], rfl, rfl, List.isChain_singleton _, by simp [trCount]⟩
  | @bt n A B C h _ ih =>
    obtain ⟨l, h1, h2, h3, h4⟩ := ih
    obtain ⟨l', rfl⟩ : ∃ l', l = B :: l' := by
      cases l with
      | nil => simp at h1
      | cons x l' => simp at h1; exact ⟨l', by rw [h1]⟩
    refine ⟨A :: B :: l', rfl, by simpa using h2, List.IsChain.cons_cons (Or.inr h) h3, ?_⟩
    rw [trCount_cons_cons, if_neg (not_TR_of_BT h)]; omega
  | @tr n A B C h _ ih =>
    obtain ⟨l, h1, h2, h3, h4⟩ := ih
    obtain ⟨l', rfl⟩ : ∃ l', l = B :: l' := by
      cases l with
      | nil => simp at h1
      | cons x l' => simp at h1; exact ⟨l', by rw [h1]⟩
    refine ⟨A :: B :: l', rfl, by simpa using h2, List.IsChain.cons_cons (Or.inl h) h3, ?_⟩
    rw [trCount_cons_cons]; split_ifs <;> omega

/-! ### Paths -/

variable (X)

def Adj (x y : V) : Prop := x ≠ y ∧ X.IsFace {x, y}

lemma vert_of_face {s : Finset V} (h : X.IsFace s) {x : V} (hx : x ∈ s) : x ∈ X.vertices := by
  obtain ⟨τ, hτ, hs⟩ := h
  simp only [vertices, Finset.mem_biUnion, id]
  exact ⟨τ, hτ, hs hx⟩

lemma face_sub {s t : Finset V} (h : X.IsFace t) (hst : s ⊆ t) : X.IsFace s := by
  obtain ⟨τ, hτ, hs⟩ := h
  exact ⟨τ, hτ, hst.trans hs⟩

variable {X}

lemma path_append_left {l₁ l₂ : List V} (h : X.IsPath (l₁ ++ l₂)) (hl : l₁ ≠ []) :
    X.IsPath l₁ :=
  ⟨hl, fun u hu => h.2.1 u (List.mem_append_left _ hu), h.2.2.left_of_append⟩

lemma path_append_right {l₁ l₂ : List V} (h : X.IsPath (l₁ ++ l₂)) (hl : l₂ ≠ []) :
    X.IsPath l₂ :=
  ⟨hl, fun u hu => h.2.1 u (List.mem_append_right _ hu), h.2.2.right_of_append⟩

lemma path_reverse {l : List V} (h : X.IsPath l) : X.IsPath l.reverse := by
  refine ⟨by simpa using h.1, fun u hu => h.2.1 u (List.mem_reverse.1 hu), ?_⟩
  rw [List.isChain_reverse]
  exact h.2.2.imp fun a b hab => ⟨hab.1.symm, by rw [Finset.pair_comm]; exact hab.2⟩

lemma bt_local {P S : List V} {u v : V} (h : X.IsPathFrom v₀ v₀ (P ++ u :: v :: u :: S)) :
    X.BT v₀ (P ++ u :: v :: u :: S) (P ++ u :: S) := by
  obtain ⟨hp, hh, hl⟩ := h
  have hp1 : X.IsPath (P ++ [u]) :=
    path_append_left (l₂ := v :: u :: S) (by simpa using hp) (by simp)
  have hp2 : X.IsPath (u :: S) :=
    path_append_right (l₁ := P ++ [u, v]) (by simpa using hp) (by simp)
  have hch : (u :: v :: u :: S).IsChain (fun u v => u ≠ v ∧ X.IsFace {u, v}) :=
    (path_append_right (l₁ := P) hp (by simp)).2.2
  rw [List.isChain_cons_cons] at hch
  refine Or.inl ⟨u, v, P ++ [u], (u :: S).reverse, ⟨hp1, ?_, by simp⟩,
    ⟨path_reverse hp2, ?_, by simp⟩, hch.1.1, hch.1.2, ?_, ?_⟩
  · cases P with
    | nil => simpa using hh
    | cons a P => simpa using hh
  · rw [List.head?_reverse]
    have : (u :: S).getLast? = (P ++ u :: v :: u :: S).getLast? := by
      rw [List.getLast?_append]; cases S <;> simp [List.getLast?_cons]
    rw [this, hl]
  · simp [pcat]
  · simp [pcat]

lemma tr_local {P S : List V} {u v w : V} (h : X.IsPathFrom v₀ v₀ (P ++ u :: v :: w :: S))
    (huw : u ≠ w) (hf : X.IsFace {u, v, w}) :
    X.TR v₀ (P ++ u :: v :: w :: S) (P ++ u :: w :: S) := by
  obtain ⟨hp, hh, hl⟩ := h
  have hp1 : X.IsPath (P ++ [u]) :=
    path_append_left (l₂ := v :: w :: S) (by simpa using hp) (by simp)
  have hp2 : X.IsPath (w :: S) :=
    path_append_right (l₁ := P ++ [u, v]) (by simpa using hp) (by simp)
  have hch : (u :: v :: w :: S).IsChain (fun u v => u ≠ v ∧ X.IsFace {u, v}) :=
    (path_append_right (l₁ := P) hp (by simp)).2.2
  rw [List.isChain_cons_cons, List.isChain_cons_cons] at hch
  refine Or.inl ⟨u, v, w, P ++ [u], (w :: S).reverse, hch.1.1, hch.2.1.1, huw, hf,
    ⟨hp1, ?_, by simp⟩, ⟨path_reverse hp2, ?_, by simp⟩, ?_, ?_⟩
  · cases P with
    | nil => simpa using hh
    | cons a P => simpa using hh
  · rw [List.head?_reverse]
    have : (w :: S).getLast? = (P ++ u :: v :: w :: S).getLast? := by
      rw [List.getLast?_append]; cases S <;> simp [List.getLast?_cons]
    rw [this, hl]
  · simp [pcat]
  · simp [pcat]

/-! ### Walks and their normal forms -/

variable (X v₀)

/-- A walk: consecutive vertices are equal or adjacent. -/
def IsWalk (W : List V) : Prop :=
  W ≠ [] ∧ (∀ x ∈ W, X.IsFace {x}) ∧ W.IsChain (fun x y => X.IsFace {x, y})

def WLoop (W : List V) : Prop := IsWalk X W ∧ W.head? = some v₀ ∧ W.getLast? = some v₀

/-- Remove consecutive repetitions. -/
def dd : V → List V → List V
  | a, [] => [a]
  | a, b :: l => if a = b then dd a l else a :: dd b l

def nrm : List V → List V
  | [] => []
  | a :: l => dd a l

def Hom (c : ℕ) (W W' : List V) : Prop :=
  (WLoop X v₀ W ↔ WLoop X v₀ W') ∧ (WLoop X v₀ W → Rw X v₀ c (nrm W) (nrm W'))

def LHom (c : ℕ) (S S' : List V) : Prop := ∀ pre suf, Hom X v₀ c (pre ++ S ++ suf) (pre ++ S' ++ suf)

variable {X v₀}

lemma dd_head (a : V) (l : List V) : ∃ t, dd a l = a :: t := by
  induction l generalizing a with
  | nil => exact ⟨[], rfl⟩
  | cons b l ih =>
    by_cases h : a = b
    · subst h; simpa [dd] using ih a
    · simp [dd, h]

lemma dd_split (l : List V) (a b : V) : ∃ Pre, ∀ m, dd a (l ++ b :: m) = Pre ++ dd b m := by
  induction l generalizing a with
  | nil =>
    by_cases h : a = b
    · subst h; exact ⟨[], fun m => by simp [dd]⟩
    · exact ⟨[a], fun m => by simp [dd, h]⟩
  | cons x l ih =>
    by_cases h : a = x
    · obtain ⟨Pre, hP⟩ := ih a
      exact ⟨Pre, fun m => by subst h; simp [dd, hP]⟩
    · obtain ⟨Pre, hP⟩ := ih x
      exact ⟨a :: Pre, fun m => by simp [dd, h, hP]⟩

lemma nrm_split (pre : List V) (b : V) : ∃ Pre, ∀ m, nrm (pre ++ b :: m) = Pre ++ dd b m := by
  cases pre with
  | nil => exact ⟨[], fun m => rfl⟩
  | cons a pre =>
    obtain ⟨Pre, h⟩ := dd_split pre a b
    exact ⟨Pre, fun m => h m⟩

lemma mem_dd {a : V} {l : List V} {x : V} (h : x ∈ dd a l) : x ∈ a :: l := by
  induction l generalizing a with
  | nil => simpa [dd] using h
  | cons b l ih =>
    by_cases hab : a = b
    · subst hab; simp only [dd, if_true] at h
      have := ih h; simp at this ⊢; tauto
    · simp only [dd, hab, if_false, List.mem_cons] at h
      rcases h with h | h
      · simp [h]
      · have := ih h; simp at this ⊢; tauto

lemma dd_getLast (a : V) (l : List V) : (dd a l).getLast? = (a :: l).getLast? := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih =>
    by_cases hab : a = b
    · subst hab; simp only [dd, if_true]; rw [ih]; cases l <;> simp [List.getLast?_cons]
    · simp only [dd, hab, if_false]
      obtain ⟨t, ht⟩ := dd_head b l
      rw [ht, List.getLast?_cons_cons, List.getLast?_cons_cons, ← ih b, ht]

lemma dd_chain (a : V) (l : List V) (h : (a :: l).IsChain (fun x y => X.IsFace {x, y})) :
    (dd a l).IsChain (fun u v => u ≠ v ∧ X.IsFace {u, v}) := by
  induction l generalizing a with
  | nil => exact List.isChain_singleton _
  | cons b l ih =>
    rw [List.isChain_cons_cons] at h
    by_cases hab : a = b
    · subst hab; simpa [dd] using ih a h.2
    · simp only [dd, hab, if_false]
      obtain ⟨t, ht⟩ := dd_head b l
      have := ih b h.2
      rw [ht] at this ⊢
      exact List.IsChain.cons_cons ⟨hab, h.1⟩ this

lemma nrm_loop {W : List V} (h : WLoop X v₀ W) : X.IsPathFrom v₀ v₀ (nrm W) := by
  obtain ⟨⟨hne, hv, hc⟩, hh, hl⟩ := h
  rcases W with _ | ⟨a, l⟩
  · exact absurd rfl hne
  simp only [List.head?_cons, Option.some.injEq] at hh
  subst hh
  obtain ⟨t, ht⟩ := dd_head a l
  refine ⟨⟨?_, fun x hx => ?_, dd_chain a l hc⟩, ?_, ?_⟩
  · simp [nrm, ht]
  · exact vert_of_face X (hv x (mem_dd hx)) (Finset.mem_singleton_self x)
  · simp [nrm, ht]
  · simp only [nrm]; rw [dd_getLast, hl]

lemma dd_of_path {a : V} {l : List V} (h : (a :: l).IsChain (fun u v => u ≠ v ∧ X.IsFace {u, v})) :
    dd a l = a :: l := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih =>
    rw [List.isChain_cons_cons] at h
    simp [dd, h.1.1, ih h.2]

lemma walk_of_path {l : List V} (h : X.IsPath l) : IsWalk X l := by
  refine ⟨h.1, fun x hx => ?_, h.2.2.imp fun a b hab => hab.2⟩
  have := h.2.1 x hx
  simp only [vertices, Finset.mem_biUnion, id] at this
  obtain ⟨τ, hτ, hx⟩ := this
  exact ⟨τ, hτ, by simpa using hx⟩

/-! ### The calculus `Hom` / `LHom` -/

lemma Hom.refl (c : ℕ) (W : List V) : Hom X v₀ c W W := ⟨Iff.rfl, fun _ => Rw.refl c _⟩

lemma Hom.trans {a b : ℕ} {W₁ W₂ W₃ : List V} (h₁ : Hom X v₀ a W₁ W₂) (h₂ : Hom X v₀ b W₂ W₃) :
    Hom X v₀ (a + b) W₁ W₃ :=
  ⟨h₁.1.trans h₂.1, fun h => (h₁.2 h).trans (h₂.2 (h₁.1.1 h))⟩

lemma Hom.symm {a : ℕ} {W₁ W₂ : List V} (h : Hom X v₀ a W₁ W₂) : Hom X v₀ a W₂ W₁ :=
  ⟨h.1.symm, fun hw => (h.2 (h.1.2 hw)).symm⟩

lemma Hom.mono {a b : ℕ} {W₁ W₂ : List V} (h : Hom X v₀ a W₁ W₂) (hab : a ≤ b) :
    Hom X v₀ b W₁ W₂ := ⟨h.1, fun hw => (h.2 hw).mono hab⟩

lemma Hom.of_eq {c : ℕ} {W W' : List V} (h : W = W') : Hom X v₀ c W W' := h ▸ Hom.refl c W

lemma LHom.refl (c : ℕ) (S : List V) : LHom X v₀ c S S := fun _ _ => Hom.refl c _

lemma LHom.of_eq {c : ℕ} {S S' : List V} (h : S = S') : LHom X v₀ c S S' :=
  h ▸ LHom.refl c S

lemma LHom.trans {a b : ℕ} {S₁ S₂ S₃ : List V} (h₁ : LHom X v₀ a S₁ S₂)
    (h₂ : LHom X v₀ b S₂ S₃) : LHom X v₀ (a + b) S₁ S₃ :=
  fun pre suf => (h₁ pre suf).trans (h₂ pre suf)

lemma LHom.symm {a : ℕ} {S₁ S₂ : List V} (h : LHom X v₀ a S₁ S₂) : LHom X v₀ a S₂ S₁ :=
  fun pre suf => (h pre suf).symm

lemma LHom.mono {a b : ℕ} {S₁ S₂ : List V} (h : LHom X v₀ a S₁ S₂) (hab : a ≤ b) :
    LHom X v₀ b S₁ S₂ := fun pre suf => (h pre suf).mono hab

lemma LHom.ctx {c : ℕ} {S S' : List V} (h : LHom X v₀ c S S') (P Q : List V) :
    LHom X v₀ c (P ++ S ++ Q) (P ++ S' ++ Q) := fun pre suf => by
  simpa [List.append_assoc] using h (pre ++ P) (Q ++ suf)

lemma LHom.app {a b : ℕ} {S S' T T' : List V} (h₁ : LHom X v₀ a S S') (h₂ : LHom X v₀ b T T') :
    LHom X v₀ (a + b) (S ++ T) (S' ++ T') :=
  (by simpa using h₁.ctx [] T : LHom X v₀ a (S ++ T) (S' ++ T)).trans
    (by simpa using h₂.ctx S' [])

lemma LHom.hom {c : ℕ} {S S' : List V} (h : LHom X v₀ c S S') : Hom X v₀ c S S' := by
  simpa using h [] []

/-- Replacing a walk segment by another with the same endpoints preserves `WLoop`. -/
lemma wloop_congr {S S' : List V} (hS : IsWalk X S) (hS' : IsWalk X S')
    (hh : S.head? = S'.head?) (hl : S.getLast? = S'.getLast?) (pre suf : List V) :
    WLoop X v₀ (pre ++ S ++ suf) ↔ WLoop X v₀ (pre ++ S' ++ suf) := by
  obtain ⟨hne, hv, hc⟩ := hS
  obtain ⟨hne', hv', hc'⟩ := hS'
  have key : ∀ T : List V, T ≠ [] → T.IsChain (fun x y => X.IsFace {x, y}) →
      ((pre ++ T ++ suf).IsChain (fun x y => X.IsFace {x, y}) ↔
        pre.IsChain (fun x y => X.IsFace {x, y}) ∧ suf.IsChain (fun x y => X.IsFace {x, y}) ∧
        (∀ x ∈ pre.getLast?, ∀ y ∈ T.head?, X.IsFace {x, y}) ∧
        (∀ x ∈ T.getLast?, ∀ y ∈ suf.head?, X.IsFace {x, y})) := by
    intro T hT hTc
    rw [List.append_assoc, List.isChain_append, List.isChain_append]
    have : (T ++ suf).head? = T.head? := by
      cases T with
      | nil => exact absurd rfl hT
      | cons a T => rfl
    rw [this]; tauto
  unfold WLoop IsWalk
  rw [key S hne hc, key S' hne' hc', hh, hl]
  have h1 : (pre ++ S ++ suf).head? = (pre ++ S' ++ suf).head? := by
    simp only [List.append_assoc, List.head?_append]
    cases S with
    | nil => exact absurd rfl hne
    | cons a S => cases S' with
      | nil => exact absurd rfl hne'
      | cons b S' => simp at hh; simp [hh]
  have h2 : (pre ++ S ++ suf).getLast? = (pre ++ S' ++ suf).getLast? := by
    simp only [List.getLast?_append]
    rw [hl]
  rw [h1, h2]
  constructor
  · rintro ⟨⟨-, hm, h⟩, hd, he⟩
    refine ⟨⟨by simp [hne'], fun x hx => ?_, h⟩, hd, he⟩
    simp only [List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · exact hm x (by simp [hx])
    · exact hv' x hx
    · exact hm x (by simp [hx])
  · rintro ⟨⟨-, hm, h⟩, hd, he⟩
    refine ⟨⟨by simp [hne], fun x hx => ?_, h⟩, hd, he⟩
    simp only [List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · exact hm x (by simp [hx])
    · exact hv x hx
    · exact hm x (by simp [hx])

lemma walk3 {a b d : V} (h : X.IsFace {a, b, d}) : IsWalk X [a, b, d] := by
  refine ⟨by simp, fun x hx => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    exact face_sub X h (by rcases hx with rfl | rfl | rfl <;> simp)
  · refine List.IsChain.cons_cons (face_sub X h ?_) (List.IsChain.cons_cons (face_sub X h ?_)
      (List.isChain_singleton _))
    · intro x; simp; tauto
    · intro x; simp; tauto

lemma walk2 {a b : V} (h : X.IsFace {a, b}) : IsWalk X [a, b] := by
  refine ⟨by simp, fun x hx => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    exact face_sub X h (by rcases hx with rfl | rfl <;> simp)
  · exact List.IsChain.cons_cons h (List.isChain_singleton _)

lemma walk1 {a : V} (h : X.IsFace {a}) : IsWalk X [a] :=
  ⟨by simp, fun x hx => by simp at hx; subst hx; exact h, List.isChain_singleton _⟩

/-- Deleting the middle vertex of a triangle. -/
lemma lhom_del {a b d : V} (hf : X.IsFace {a, b, d}) : LHom X v₀ 1 [a, b, d] [a, d] := by
  intro pre suf
  refine ⟨wloop_congr (walk3 hf) (walk2 (face_sub X hf (by intro x; simp; tauto))) rfl rfl pre suf,
    fun hw => ?_⟩
  have hp := nrm_loop hw
  obtain ⟨Pre, hPre⟩ := nrm_split pre a
  have e1 : pre ++ [a, b, d] ++ suf = pre ++ a :: (b :: d :: suf) := by simp
  have e2 : pre ++ [a, d] ++ suf = pre ++ a :: (d :: suf) := by simp
  rw [e1, hPre] at hp ⊢
  rw [e2, hPre]
  by_cases hab : a = b
  · subst hab; simp only [dd, if_true]; exact Rw.refl _ _
  by_cases hbd : b = d
  · subst hbd; simp only [dd, hab, if_false, if_true]; exact Rw.refl _ _
  obtain ⟨t, ht⟩ := dd_head d suf
  by_cases had : a = d
  · subst had
    simp only [dd, hab, if_false, hbd, if_true] at hp ⊢
    rw [ht] at hp ⊢
    exact Rw.bt (bt_local hp) (Rw.refl _ _)
  · simp only [dd, hab, if_false, hbd, had] at hp ⊢
    rw [ht] at hp ⊢
    exact Rw.tr (tr_local hp had hf) (Rw.refl _ _)

/-- Removing a backtrack `a b a`. -/
lemma lhom_bt {a b : V} (hf : X.IsFace {a, b}) : LHom X v₀ 0 [a, b, a] [a] := by
  intro pre suf
  have hf' : X.IsFace {a, b, a} := by
    refine face_sub X hf ?_; intro x; simp; tauto
  refine ⟨wloop_congr (walk3 hf') (walk1 (face_sub X hf (by simp))) rfl rfl pre suf,
    fun hw => ?_⟩
  have hp := nrm_loop hw
  obtain ⟨Pre, hPre⟩ := nrm_split pre a
  have e1 : pre ++ [a, b, a] ++ suf = pre ++ a :: (b :: a :: suf) := by simp
  have e2 : pre ++ [a] ++ suf = pre ++ a :: suf := by simp
  rw [e1, hPre] at hp ⊢
  rw [e2, hPre]
  by_cases hab : a = b
  · subst hab; simp only [dd, if_true]; exact Rw.refl _ _
  obtain ⟨t, ht⟩ := dd_head a suf
  simp only [dd, hab, if_false, Ne.symm hab] at hp ⊢
  rw [ht] at hp ⊢
  exact Rw.bt (bt_local hp) (Rw.refl _ _)

lemma lhom_stutter {a : V} : LHom X v₀ 0 [a, a] [a] := by
  intro pre suf
  have e1 : pre ++ [a, a] ++ suf = pre ++ [a] ++ (a :: suf) := by simp
  have e2 : pre ++ [a] ++ suf = pre ++ [] ++ (a :: suf) := by simp
  constructor
  · rw [e1, e2]
    constructor
    · rintro ⟨⟨-, hm, hc⟩, hh, hl⟩
      refine ⟨⟨by simp, fun x hx => hm x (by simp at hx ⊢; tauto), ?_⟩, ?_, ?_⟩
      · simp only [List.append_assoc, List.singleton_append, List.nil_append] at hc ⊢
        rw [List.isChain_append] at hc ⊢
        refine ⟨hc.1, (List.isChain_cons.1 hc.2.1).2, ?_⟩
        intro x hx y hy
        exact hc.2.2 x hx y (by simp at hy; simp [hy])
      · cases pre <;> simpa using hh
      · simpa [List.getLast?_append] using hl
    · rintro ⟨⟨-, hm, hc⟩, hh, hl⟩
      refine ⟨⟨by simp, fun x hx => hm x (by simp at hx ⊢; tauto), ?_⟩, ?_, ?_⟩
      · simp only [List.append_assoc, List.singleton_append, List.nil_append] at hc ⊢
        rw [List.isChain_append] at hc ⊢
        refine ⟨hc.1, List.IsChain.cons_cons ?_ hc.2.1, ?_⟩
        · simpa using hm a (by simp)
        · intro x hx y hy
          exact hc.2.2 x hx y (by simp at hy; simp [hy])
      · cases pre <;> simpa using hh
      · simpa [List.getLast?_append] using hl
  · intro _
    obtain ⟨Pre, hPre⟩ := nrm_split pre a
    have e3 : pre ++ [a, a] ++ suf = pre ++ a :: (a :: suf) := by simp
    have e4 : pre ++ [a] ++ suf = pre ++ a :: suf := by simp
    rw [e3, e4, hPre, hPre]
    simp only [dd, if_true]; exact Rw.refl _ _

lemma lhom_ins {a b d : V} (hf : X.IsFace {a, b, d}) : LHom X v₀ 1 [a, d] [a, b, d] :=
  (lhom_del hf).symm

/-- Collapsing a palindrome `Z⁻¹ ∘ Z`. -/
lemma lhom_pal (Z : List V) : ∀ (a e : V), (a :: Z).IsChain (fun x y => X.IsFace {x, y}) →
    (a :: Z).getLast? = some e → LHom X v₀ 0 ((a :: Z).reverse ++ Z) [e] := by
  induction Z with
  | nil =>
    intro a e _ he
    simp at he; subst he; exact LHom.refl _ _
  | cons b Z ih =>
    intro a e hc he
    rw [List.isChain_cons_cons] at hc
    have h1 : LHom X v₀ 0 ((a :: b :: Z).reverse ++ b :: Z) ((b :: Z).reverse ++ Z) := by
      have := (lhom_bt (X := X) (v₀ := v₀) (a := b) (b := a)
        (by rw [Finset.pair_comm]; exact hc.1)).ctx Z.reverse Z
      simpa using this
    have := h1.trans (ih b e hc.2 (by simpa [List.getLast?_cons] using he))
    simpa using this

lemma wl_le {α : Type*} (L : List (α × Bool)) : wordLength (FreeGroup.mk L) ≤ L.length := by
  unfold wordLength; exact FreeGroup.norm_mk_le

def Edge (X : WComplex V) (u v : V) : Prop := u ≠ v ∧ X.IsFace {u, v}

lemma path_pcat {a b c : V} {P Q : List V} (hP : X.IsPathFrom a b P) (hQ : X.IsPathFrom b c Q) :
    X.IsPathFrom a c (pcat P Q) := by
  obtain ⟨⟨hPn, hPv, hPc⟩, hPh, hPl⟩ := hP
  obtain ⟨⟨hQn, hQv, hQc⟩, hQh, hQl⟩ := hQ
  rcases Q with _ | ⟨b', Q⟩
  · exact absurd rfl hQn
  simp only [List.head?_cons, Option.some.injEq] at hQh
  subst hQh
  simp only [pcat, List.tail_cons]
  refine ⟨⟨by simp [hPn], fun u hu => ?_, ?_⟩, ?_, ?_⟩
  · rcases List.mem_append.1 hu with hu | hu
    · exact hPv u hu
    · exact hQv u (List.mem_cons_of_mem _ hu)
  · rw [List.isChain_append]
    refine ⟨hPc, hQc.tail, fun x hx y hy => ?_⟩
    rw [hPl] at hx; cases hx
    exact (List.isChain_cons.1 hQc).1 y hy
  · cases P with
    | nil => exact absurd rfl hPn
    | cons p P => simpa using hPh
  · rw [List.getLast?_append]
    cases Q with
    | nil => simpa [hPl] using hQl
    | cons q Q => simpa [List.getLast?_cons_cons] using hQl

lemma path_rev {a b : V} {P : List V} (hP : X.IsPathFrom a b P) : X.IsPathFrom b a P.reverse :=
  ⟨path_reverse hP.1, by rw [List.head?_reverse]; exact hP.2.2,
    by rw [List.getLast?_reverse]; exact hP.2.1⟩

lemma eqv_chain {R : List V → List V → Prop} (hR : ∀ A B, R A B → R B A) {A B : List V}
    (h : Relation.EqvGen R A B) :
    ∃ l : List (List V), l.head? = some A ∧ l.getLast? = some B ∧ l.IsChain R := by
  have key : Relation.ReflTransGen R A B ∧ Relation.ReflTransGen R B A := by
    induction h with
    | rel x y h => exact ⟨.single h, .single (hR _ _ h)⟩
    | refl x => exact ⟨.refl, .refl⟩
    | symm x y _ ih => exact ⟨ih.2, ih.1⟩
    | trans x y z _ _ ih₁ ih₂ => exact ⟨ih₁.1.trans ih₂.1, ih₂.2.trans ih₁.2⟩
  obtain ⟨l, hl, hlast⟩ := List.exists_isChain_cons_of_relationReflTransGen key.1
  exact ⟨A :: l, rfl, by rw [List.getLast?_eq_getLast_of_ne_nil (by simp), hlast], hl⟩

end General
section Coset

variable {G : Type*} [Group G] [Finite G] {ι : Type*} [Fintype ι] [Nonempty ι]
  (H : ι → Subgroup G)

/-- `g` lies in the coset `u`. -/
def Mem (g : G) (u : Σ i, G ⧸ H i) : Prop := u.2 = (g : G ⧸ H u.1)

def st : ι := Classical.arbitrary ι

/-- The vertex `g H_st` of type `st`. -/
def Xv (g : G) : Σ i, G ⧸ H i := ⟨st, (g : G ⧸ H st)⟩

/-- A type `i` with `g ∈ H i`, when one exists. -/
def kf (g : G) : ι := Classical.epsilon (fun i => g ∈ H i)

def cv (p s : G) : Σ i, G ⧸ H i := ⟨kf H s, (p : G ⧸ H (kf H s))⟩

def encS : G → List G → List ((Σ i, G ⧸ H i) × G)
  | _, [] => []
  | p, s :: l => (cv H p s, p * s) :: encS (p * s) l

def gt (S : List ((Σ i, G ⧸ H i) × G)) : List (Σ i, G ⧸ H i) :=
  S.flatMap (fun q => [q.1, Xv H q.2])

def ee : G → List G → List (Σ i, G ⧸ H i)
  | _, [] => []
  | p, s :: l => cv H p s :: Xv H (p * s) :: ee (p * s) l

/-- The walk of a word read from the chamber `p`. -/
def Ee (p : G) (l : List G) : List (Σ i, G ⧸ H i) := Xv H p :: ee H p l

def galOK : G → List ((Σ i, G ⧸ H i) × G) → Prop
  | _, [] => True
  | h, q :: S => Mem H h q.1 ∧ Mem H q.2 q.1 ∧ galOK q.2 S

abbrev LH (c : ℕ) (S S' : List (Σ i, G ⧸ H i)) : Prop :=
  LHom (cosetComplex G H) (Xv H 1) c S S'

variable {H}

lemma chamber_exists (g : G) : ∃ τ ∈ (cosetComplex G H).tops,
    ∀ i, (⟨i, (g : G ⧸ H i)⟩ : Σ i, G ⧸ H i) ∈ τ := by
  unfold cosetComplex
  simp only
  rw [dif_pos ‹Finite G›]
  exact ⟨_, Finset.mem_image.2 ⟨g, @Finset.mem_univ _ (Fintype.ofFinite G) g, rfl⟩,
    fun i => Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩⟩

lemma mems_of_face {s : Finset (Σ i, G ⧸ H i)} (h : (cosetComplex G H).IsFace s) :
    ∃ g, ∀ x ∈ s, Mem H g x := by
  obtain ⟨τ, hτ, hs⟩ := h
  unfold cosetComplex at hτ
  simp only at hτ
  rw [dif_pos ‹Finite G›] at hτ
  obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 hτ
  refine ⟨g, fun x hx => ?_⟩
  obtain ⟨i, -, hi⟩ := Finset.mem_image.1 (hs hx)
  rw [← hi]; rfl

local instance (priority := 2000) instDecSig : DecidableEq (Σ i, G ⧸ H i) :=
  fun a b => Classical.propDecidable (a = b)

lemma face_of_mems {g : G} {s : Finset (Σ i, G ⧸ H i)} (hs : ∀ x ∈ s, Mem H g x) :
    (cosetComplex G H).IsFace s := by
  obtain ⟨τ, hτ, hmem⟩ := chamber_exists (H := H) g
  refine ⟨τ, hτ, fun x hx => ?_⟩
  have h := hs x hx
  obtain ⟨i, q⟩ := x
  simp only [Mem] at h
  subst h
  exact hmem i

lemma face3 {g : G} {a b d : Σ i, G ⧸ H i} (ha : Mem H g a) (hb : Mem H g b) (hd : Mem H g d) :
    (cosetComplex G H).IsFace {a, b, d} :=
  face_of_mems (g := g) (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> assumption)

lemma face2 {g : G} {a b : Σ i, G ⧸ H i} (ha : Mem H g a) (hb : Mem H g b) :
    (cosetComplex G H).IsFace {a, b} :=
  face_of_mems (g := g) (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption)

lemma face1 (a : Σ i, G ⧸ H i) : (cosetComplex G H).IsFace {a} := by
  obtain ⟨i, q⟩ := a
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  exact face_of_mems (g := g) (by intro x hx; simp at hx; subst hx; rfl)

lemma mems_of_face2 {a b : Σ i, G ⧸ H i} (h : (cosetComplex G H).IsFace {a, b}) :
    ∃ g, Mem H g a ∧ Mem H g b := by
  obtain ⟨g, hg⟩ := mems_of_face h
  exact ⟨g, hg a (Finset.mem_insert_self a {b}),
    hg b (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))⟩

lemma mem_mul {g s : G} {u : Σ i, G ⧸ H i} (h : Mem H g u) (hs : s ∈ H u.1) :
    Mem H (g * s) u := by
  unfold Mem at h ⊢
  rw [h, QuotientGroup.eq]
  simpa using hs

lemma mem_diff {g g' : G} {u : Σ i, G ⧸ H i} (h : Mem H g u) (h' : Mem H g' u) :
    g⁻¹ * g' ∈ H u.1 := by
  unfold Mem at h h'
  rw [← QuotientGroup.eq, ← h, ← h']

lemma mem_Xv (g : G) : Mem H g (Xv H g) := rfl

lemma mem_cv (p s : G) : Mem H p (cv H p s) := rfl

lemma kf_spec {s : G} (hs : ∃ i, s ∈ H i) : s ∈ H (kf H s) := Classical.epsilon_spec hs

lemma mem_cv' {p s : G} (hs : ∃ i, s ∈ H i) : Mem H (p * s) (cv H p s) :=
  mem_mul (mem_cv p s) (kf_spec hs)

lemma kf_inv (s : G) : kf H s⁻¹ = kf H s := by
  unfold kf; simp only [inv_mem_iff]

lemma cv_inv {p s : G} (hs : ∃ i, s ∈ H i) : cv H (p * s) s⁻¹ = cv H p s := by
  unfold cv
  rw [kf_inv]
  have := mem_cv' (p := p) hs
  unfold Mem cv at this
  simp only at this
  rw [← this]

lemma Xv_eq {g g' : G} (h : Mem H g (Xv H g')) : Xv H g = Xv H g' := by
  unfold Mem Xv at h; unfold Xv; simp only at h; rw [h]

/-! ### Encodings -/

lemma gt_cons (q : (Σ i, G ⧸ H i) × G) (S : List ((Σ i, G ⧸ H i) × G)) :
    gt H (q :: S) = q.1 :: Xv H q.2 :: gt H S := by simp [gt]

lemma ee_eq_gt (p : G) (l : List G) : ee H p l = gt H (encS H p l) := by
  induction l generalizing p with
  | nil => rfl
  | cons s l ih => simp [ee, encS, gt, ih]

lemma ee_append (p : G) (l m : List G) : ee H p (l ++ m) = ee H p l ++ ee H (p * l.prod) m := by
  induction l generalizing p with
  | nil => simp [ee]
  | cons s l ih => simp [ee, ih, mul_assoc]

lemma Ee_append (p : G) (l m : List G) : Ee H p (l ++ m) = Ee H p l ++ ee H (p * l.prod) m := by
  simp [Ee, ee_append]

lemma Ee_cons (p s : G) (l : List G) : Ee H p (s :: l) = Xv H p :: cv H p s :: Ee H (p * s) l :=
  rfl

lemma Ee_last (p : G) (l : List G) : ∃ pre, Ee H p l = pre ++ [Xv H (p * l.prod)] := by
  induction l generalizing p with
  | nil => exact ⟨[], by simp [Ee, ee]⟩
  | cons s l ih =>
    obtain ⟨pre, h⟩ := ih (p * s)
    exact ⟨Xv H p :: cv H p s :: pre, by rw [Ee_cons, h]; simp [mul_assoc]⟩

lemma prod_invs (u : List G) : ((u.map (·⁻¹)).reverse).prod = u.prod⁻¹ := by
  rw [List.prod_inv_reverse]

lemma Ee_rev (u : List G) (hu : ∀ s ∈ u, ∃ i, s ∈ H i) (p : G) :
    Ee H (p * u.prod) ((u.map (·⁻¹)).reverse) = (Ee H p u).reverse := by
  induction u generalizing p with
  | nil => simp [Ee, ee]
  | cons s u ih =>
    have hs : ∃ i, s ∈ H i := hu s (by simp)
    have ih' := ih (fun t ht => hu t (by simp [ht])) (p * s)
    simp only [List.map_cons, List.reverse_cons, List.prod_cons]
    rw [Ee_append, prod_invs, ← mul_assoc, ih']
    simp only [Ee_cons, List.reverse_cons, List.append_assoc]
    simp [ee, cv_inv hs, mul_assoc]

lemma galOK_encS (p : G) (l : List G) (hl : ∀ s ∈ l, ∃ i, s ∈ H i) :
    galOK H p (encS H p l) := by
  induction l generalizing p with
  | nil => trivial
  | cons s l ih =>
    exact ⟨mem_cv p s, mem_cv' (hl s (by simp)), ih (p * s) (fun t ht => hl t (by simp [ht]))⟩

lemma galOK_walk (h : G) (S : List ((Σ i, G ⧸ H i) × G)) (hS : galOK H h S) :
    IsWalk (cosetComplex G H) (Xv H h :: gt H S) := by
  induction S generalizing h with
  | nil => exact walk1 (face1 _)
  | cons q S ih =>
    obtain ⟨v, h'⟩ := q
    obtain ⟨hv, hv', hS⟩ := hS
    have := ih h' hS
    rw [gt_cons]
    refine ⟨by simp, fun x _ => face1 x, ?_⟩
    exact List.IsChain.cons_cons (face2 (mem_Xv h) hv)
      (List.IsChain.cons_cons (face2 hv' (mem_Xv h')) this.2.2)

lemma gal_swap (h : G) (S S' : List ((Σ i, G ⧸ H i) × G)) (hS : galOK H h S)
    (hS' : galOK H h S') (hsn : S.map Prod.snd = S'.map Prod.snd) :
    LH H (2 * S.length) (Xv H h :: gt H S) (Xv H h :: gt H S') := by
  induction S generalizing h S' with
  | nil =>
    cases S' with
    | nil => exact LHom.refl _ _
    | cons _ _ => simp at hsn
  | cons q S ih =>
    cases S' with
    | nil => simp at hsn
    | cons q' S' =>
      obtain ⟨v, h₁⟩ := q
      obtain ⟨v', h₁'⟩ := q'
      simp only [List.map_cons, List.cons.injEq] at hsn
      obtain ⟨rfl, hsn⟩ := hsn
      obtain ⟨hv, hv1, hS⟩ := hS
      obtain ⟨hv', hv1', hS'⟩ := hS'
      have step : LH H 2 [Xv H h, v, Xv H h₁] [Xv H h, v', Xv H h₁] := by
        have a1 := (lhom_ins (X := cosetComplex G H) (v₀ := Xv H 1)
          (face3 (mem_Xv h) hv' hv)).ctx [] [Xv H h₁]
        have a2 := (lhom_del (X := cosetComplex G H) (v₀ := Xv H 1)
          (face3 hv1' hv1 (mem_Xv h₁))).ctx [Xv H h] []
        simpa using a1.trans a2
      have a1 : LH H 2 (Xv H h :: v :: Xv H h₁ :: gt H S) (Xv H h :: v' :: Xv H h₁ :: gt H S) := by
        simpa using step.ctx [] (gt H S)
      have a2 : LH H (2 * S.length) (Xv H h :: v' :: Xv H h₁ :: gt H S)
          (Xv H h :: v' :: Xv H h₁ :: gt H S') := by
        simpa using (ih h₁ S' hS hS' hsn).ctx [Xv H h, v'] []
      rw [gt_cons, gt_cons]
      exact (a1.trans a2).mono (by simp; omega)

/-- Collapsing the star of `c`. -/
lemma lhom_star (c : Σ i, G ⧸ H i) (P : List G) (hP : ∀ s ∈ P, s ∈ H c.1) (h : G)
    (hc : Mem H h c) :
    LH H 0 (c :: Xv H h :: gt H ((encS H h P).map (fun x => (c, x.2))))
      [c, Xv H (h * P.prod)] := by
  induction P generalizing h with
  | nil => simp [encS, gt]; exact LHom.refl _ _
  | cons s P ih =>
    have hs : s ∈ H c.1 := hP s (by simp)
    have a1 := (lhom_bt (X := cosetComplex G H) (v₀ := Xv H 1) (face2 hc (mem_Xv h))).ctx []
      (Xv H (h * s) :: gt H ((encS H (h * s) P).map (fun x => (c, x.2))))
    have a2 := ih (fun t ht => hP t (by simp [ht])) (h * s) (mem_mul hc hs)
    have := a1.trans a2
    simp only [encS, List.map_cons, gt_cons, List.prod_cons, ← mul_assoc]
    simpa using this

lemma galOK_star (c : Σ i, G ⧸ H i) (P : List G) (hP : ∀ s ∈ P, s ∈ H c.1) (h : G)
    (hc : Mem H h c) : galOK H h ((encS H h P).map (fun x => (c, x.2))) := by
  induction P generalizing h with
  | nil => trivial
  | cons s P ih =>
    have hs : s ∈ H c.1 := hP s (by simp)
    exact ⟨hc, mem_mul hc hs, ih (fun t ht => hP t (by simp [ht])) (h * s) (mem_mul hc hs)⟩

lemma length_encS (p : G) (l : List G) : (encS H p l).length = l.length := by
  induction l generalizing p with
  | nil => rfl
  | cons s l ih => simp [encS, ih]

/-- A relator of `H_i` collapses with at most `2 |P|` triangle moves. -/
lemma lhom_rel (i : ι) (P : List G) (hP : ∀ s ∈ P, s ∈ H i) (hprod : P.prod = 1) (q : G) :
    LH H (2 * P.length) (Ee H q P) [Xv H q] := by
  cases P with
  | nil => exact (LHom.refl 0 _).mono (by simp)
  | cons s P =>
    set c : Σ i, G ⧸ H i := ⟨i, (q : G ⧸ H i)⟩
    have hc : Mem H q c := rfl
    have hP' : ∀ t ∈ s :: P, t ∈ H c.1 := hP
    have a1 := gal_swap q (encS H q (s :: P)) ((encS H q (s :: P)).map (fun x => (c, x.2)))
      (galOK_encS q _ (fun t ht => ⟨i, hP t ht⟩)) (galOK_star c _ hP' q hc)
      (by simp [Function.comp_def])
    rw [length_encS] at a1
    have hs : s ∈ H c.1 := hP' s (by simp)
    have a2 := (lhom_star c P (fun t ht => hP' t (by simp [ht])) (q * s) (mem_mul hc hs)).ctx
      [Xv H q] []
    have a3 := (lhom_bt (X := cosetComplex G H) (v₀ := Xv H 1) (face2 (mem_Xv q) hc)).ctx [] []
    have e : q * s * P.prod = q := by
      rw [mul_assoc, ← List.prod_cons, hprod, mul_one]
    rw [e] at a2
    simp only [List.nil_append, List.append_nil, List.singleton_append] at a2 a3
    simp only [encS, List.map_cons, gt_cons] at a1
    have := a1.trans (a2.trans a3)
    simpa [Ee, ee_eq_gt, encS, gt_cons] using this

/-- A factor with trivial product can be removed from the middle of a word. -/
lemma lhom_factor {c : ℕ} (F : List G) (hF : ∀ q, LH H c (Ee H q F) [Xv H q])
    (hFp : F.prod = 1) (p : G) (A B : List G) :
    LH H c (Ee H p (A ++ F ++ B)) (Ee H p (A ++ B)) := by
  obtain ⟨pre, hpre⟩ := Ee_last (H := H) p A
  have e1 : Ee H p (A ++ F ++ B) = pre ++ Ee H (p * A.prod) F ++ ee H (p * A.prod) B := by
    rw [List.append_assoc, Ee_append, ee_append, hFp, mul_one, hpre]; simp [Ee]
  have e2 : Ee H p (A ++ B) = pre ++ [Xv H (p * A.prod)] ++ ee H (p * A.prod) B := by
    rw [Ee_append, hpre]
  rw [e1, e2]
  exact (hF _).ctx _ _

lemma lhom_conj {c : ℕ} (u P : List G) (hu : ∀ s ∈ u, ∃ i, s ∈ H i)
    (hP : ∀ q, LH H c (Ee H q P) [Xv H q]) (hPp : P.prod = 1) (q : G) :
    LH H c (Ee H q ((u.map (·⁻¹)).reverse ++ P ++ u)) [Xv H q] := by
  set q' := q * u.prod⁻¹
  have hq : q' * u.prod = q := by simp [q']
  have e1 : Ee H q ((u.map (·⁻¹)).reverse ++ P ++ u) =
      (ee H q' u).reverse ++ Ee H q' P ++ ee H q' u := by
    rw [List.append_assoc, Ee_append, ee_append, hPp, mul_one, prod_invs]
    have : Ee H q (List.map (·⁻¹) u).reverse = (Ee H q' u).reverse := by
      rw [← Ee_rev u hu q', hq]
    rw [this]; simp [Ee, q']
  rw [e1]
  have a1 := (hP q').ctx (ee H q' u).reverse (ee H q' u)
  have hw := galOK_walk q' _ (galOK_encS (H := H) q' u hu)
  rw [← ee_eq_gt] at hw
  obtain ⟨pre, hpre⟩ := Ee_last (H := H) q' u
  have a2 := lhom_pal (X := cosetComplex G H) (v₀ := Xv H 1) (ee H q' u) (Xv H q') (Xv H q)
    hw.2.2 (by rw [← Ee, hpre, hq]; simp)
  rw [List.reverse_cons] at a2
  exact a1.trans a2

/-! ### Free-group words -/

/-- The value of a letter. -/
def lv (x : CosetGen H × Bool) : G := cond x.2 x.1.1 x.1.1⁻¹

lemma lv_mem (x : CosetGen H × Bool) : ∃ i, lv x ∈ H i := by
  obtain ⟨⟨g, -, i, hi⟩, b⟩ := x
  cases b
  · exact ⟨i, inv_mem hi⟩
  · exact ⟨i, hi⟩

lemma lv_not (x : CosetGen H) (b : Bool) : lv (x, !b) = (lv (x, b))⁻¹ := by
  cases b <;> simp [lv]

lemma vals_mem (L : List (CosetGen H × Bool)) : ∀ s ∈ L.map lv, ∃ i, s ∈ H i := by
  intro s hs
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hs
  exact lv_mem x

lemma lhom_red_step {L₁ L₂ : List (CosetGen H × Bool)} (h : FreeGroup.Red.Step L₁ L₂) (p : G) :
    LH H 0 (Ee H p (L₁.map lv)) (Ee H p (L₂.map lv)) := by
  cases h with
  | @not L₁ L₂ x b =>
    have hv : ∃ i, (lv (x, b))⁻¹ ∈ H i := by
      obtain ⟨i, hi⟩ := lv_mem (x, b); exact ⟨i, inv_mem hi⟩
    have hF : ∀ q, LH H 0 (Ee H q [lv (x, b), (lv (x, b))⁻¹]) [Xv H q] := by
      intro q
      have := lhom_conj (H := H) [(lv (x, b))⁻¹] [] (by simpa using hv)
        (fun q => LHom.refl 0 _) (by simp) q
      simpa using this
    have := lhom_factor _ hF (by simp) p (L₁.map lv) (L₂.map lv)
    simpa [lv_not] using this

lemma lhom_red {L₁ L₂ : List (CosetGen H × Bool)} (h : FreeGroup.Red L₁ L₂) (p : G) :
    LH H 0 (Ee H p (L₁.map lv)) (Ee H p (L₂.map lv)) := by
  unfold FreeGroup.Red at h
  induction h with
  | refl => exact LHom.refl _ _
  | tail _ hs ih => exact ih.trans (lhom_red_step hs p)

/-- The letter of a group element (none for `1`). -/
def toLet (g : G) : Option (CosetGen H × Bool) :=
  if h : g ≠ 1 ∧ ∃ i, g ∈ H i then some (⟨g, h⟩, true) else none

lemma lhom_filter (l : List G) (hl : ∀ s ∈ l, ∃ i, s ∈ H i) (p : G) :
    LH H 0 (Ee H p l) (Ee H p ((l.filterMap (toLet (H := H))).map lv)) := by
  induction l generalizing p with
  | nil => exact LHom.refl _ _
  | cons s l ih =>
    have ih' := ih (fun t ht => hl t (by simp [ht]))
    by_cases hs : s = 1
    · subst hs
      have hF : ∀ q, LH H 0 (Ee H q [1]) [Xv H q] := fun q => by
        have := (lhom_bt (X := cosetComplex G H) (v₀ := Xv H 1)
          (face2 (mem_Xv q) (mem_cv q 1))).ctx [] []
        simpa [Ee, ee] using this
      have := lhom_factor [1] hF (by simp) p [] l
      rw [List.filterMap_cons_none (by simp [toLet])]
      simpa using this.trans (ih' p)
    · rw [List.filterMap_cons_some (b := (⟨s, hs, hl s (by simp)⟩, true))
        (by simp [toLet, hs, hl s (by simp)])]
      simpa [Ee_cons, lv] using (ih' (p * s)).ctx [Xv H p, cv H p s] []

lemma prod_filter (l : List G) (hl : ∀ s ∈ l, ∃ i, s ∈ H i) :
    ((l.filterMap (toLet (H := H))).map lv).prod = l.prod := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    have ih' := ih (fun t ht => hl t (by simp [ht]))
    by_cases hs : s = 1
    · subst hs
      rw [List.filterMap_cons_none (by simp [toLet])]
      simpa using ih'
    · rw [List.filterMap_cons_some (b := (⟨s, hs, hl s (by simp)⟩, true))
        (by simp [toLet, hs, hl s (by simp)])]
      simp [lv, ih']

lemma mk_map_true (l : List (CosetGen H)) :
    FreeGroup.mk (l.map (·, true)) = (l.map FreeGroup.of).prod := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.map_cons, List.map_cons, List.prod_cons, ← ih, FreeGroup.of, FreeGroup.mul_mk]
    rfl

lemma vals_invRev (L : List (CosetGen H × Bool)) :
    (FreeGroup.invRev L).map lv = ((L.map lv).map (·⁻¹)).reverse := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [FreeGroup.invRev_cons, List.map_append, ih]
    obtain ⟨x, b⟩ := a
    simp [FreeGroup.invRev, lv_not]

lemma rel_letters {ρ : FreeGroup (CosetGen H)} (h : ρ ∈ cosetRel H ∨ ρ⁻¹ ∈ cosetRel H) :
    ∃ Pl : List (CosetGen H × Bool), FreeGroup.mk Pl = ρ ∧ ∃ i,
      (∀ s ∈ Pl.map lv, s ∈ H i) ∧ (Pl.map lv).prod = 1 ∧ Pl.length ≤ 3 := by
  rcases h with h | h
  · obtain ⟨i, h⟩ := Set.mem_iUnion.1 h
    obtain ⟨l, -, h3, hmem, hprod, rfl⟩ := h
    refine ⟨l.map (·, true), mk_map_true l, i, ?_, ?_, by simpa using h3⟩
    · intro s hs
      rw [List.map_map] at hs
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hs
      exact hmem x hx
    · simpa [lv, Function.comp_def] using hprod
  · obtain ⟨i, h⟩ := Set.mem_iUnion.1 h
    obtain ⟨l, -, h3, hmem, hprod, hρ⟩ := h
    refine ⟨FreeGroup.invRev (l.map (·, true)), ?_, i, ?_, ?_, by simpa [FreeGroup.invRev] using h3⟩
    · rw [← FreeGroup.inv_mk, mk_map_true, ← hρ, inv_inv]
    · intro s hs
      rw [vals_invRev] at hs
      simp only [List.mem_reverse, List.map_map, List.mem_map] at hs
      obtain ⟨x, hx, rfl⟩ := hs
      exact inv_mem (hmem x hx)
    · rw [vals_invRev, ← List.prod_inv_reverse]
      simpa [lv, Function.comp_def] using hprod

lemma lhom_total (l : List (FreeGroup (CosetGen H) × FreeGroup (CosetGen H)))
    (hl : ∀ p ∈ l, p.2 ∈ cosetRel H ∨ p.2⁻¹ ∈ cosetRel H) :
    ∃ Lt : List (CosetGen H × Bool), FreeGroup.mk Lt = (l.map (fun p => p.1⁻¹ * p.2 * p.1)).prod ∧
      ∀ q, LH H (6 * l.length) (Ee H q (Lt.map lv)) [Xv H q] := by
  induction l with
  | nil => exact ⟨[], by simp [FreeGroup.one_eq_mk], fun q => LHom.refl _ _⟩
  | cons p l ih =>
    obtain ⟨Lt, hmk, hLt⟩ := ih (fun p hp => hl p (by simp [hp]))
    obtain ⟨u, ρ⟩ := p
    obtain ⟨Pl, hPl, i, hmem, hprod, hlen⟩ := rel_letters (hl (u, ρ) (by simp))
    set U := u.toWord
    refine ⟨FreeGroup.invRev U ++ Pl ++ U ++ Lt, ?_, ?_⟩
    · rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.inv_mk,
        hPl, FreeGroup.mk_toWord, hmk]
      simp
    · intro q
      have hF : ∀ q, LH H 6 (Ee H q ((FreeGroup.invRev U ++ Pl ++ U).map lv)) [Xv H q] := by
        intro q
        have := lhom_conj (U.map lv) (Pl.map lv) (vals_mem U)
          (fun q => ((lhom_rel i _ hmem hprod q).mono
            (show 2 * (Pl.map lv).length ≤ 6 by simp; omega) : LH H 6 _ _)) hprod q
        simpa [vals_invRev] using this
      have hFp : ((FreeGroup.invRev U ++ Pl ++ U).map lv).prod = 1 := by
        rw [List.map_append, List.map_append, vals_invRev, List.prod_append, List.prod_append,
          prod_invs, hprod]; simp
      have := (lhom_factor _ hF hFp q [] (Lt.map lv)).trans (hLt q)
      simp only [List.nil_append, List.map_append] at this ⊢
      refine this.mono ?_
      simp; omega

/-! ### From a loop to a word -/

lemma gallery (T : List (Σ i, G ⧸ H i)) : ∀ (v : Σ i, G ⧸ H i) (g₀ e : G), Mem H g₀ v →
    (v :: T).IsChain (fun x y => (cosetComplex G H).IsFace {x, y}) →
    (∀ y ∈ (v :: T).getLast?, Mem H e y) →
    ∃ S, galOK H g₀ S ∧ S.length = T.length + 1 ∧ (S.map Prod.snd).getLast? = some e ∧
      LH H T.length (gt H S) (v :: T ++ [Xv H e]) := by
  induction T with
  | nil =>
    intro v g₀ e hv _ he
    exact ⟨[(v, e)], ⟨hv, he v (by simp), trivial⟩, rfl, rfl, by simp [gt]; exact LHom.refl _ _⟩
  | cons w T ih =>
    intro v g₀ e hv hc he
    rw [List.isChain_cons_cons] at hc
    obtain ⟨g₁, hg₁v, hg₁w⟩ := mems_of_face2 hc.1
    obtain ⟨S, hS, hlen, hlast, hL⟩ := ih w g₁ e hg₁w hc.2
      (fun y hy => he y (by rw [List.getLast?_cons_cons]; exact hy))
    refine ⟨(v, g₁) :: S, ⟨hv, hg₁v, hS⟩, by simp [hlen], ?_, ?_⟩
    · cases S with
      | nil => simp at hlen
      | cons q S => simpa [List.getLast?_cons_cons] using hlast
    · have a1 := hL.ctx [v, Xv H g₁] []
      have a2 := (lhom_del (X := cosetComplex G H) (v₀ := Xv H 1)
        (face3 hg₁v (mem_Xv g₁) hg₁w)).ctx [] (T ++ [Xv H e])
      simp only [List.nil_append, List.append_nil, List.cons_append] at a1 a2
      rw [gt_cons]
      exact (a1.trans a2).mono (by simp)

def diffs : G → List G → List G
  | _, [] => []
  | h, h' :: C => (h⁻¹ * h') :: diffs h' C

lemma encS_diffs (h : G) (C : List G) : (encS H h (diffs h C)).map Prod.snd = C := by
  induction C generalizing h with
  | nil => rfl
  | cons h' C ih => simp [diffs, encS, ih]

lemma diffs_mem (h : G) (S : List ((Σ i, G ⧸ H i) × G)) (hS : galOK H h S) :
    ∀ s ∈ diffs h (S.map Prod.snd), ∃ i, s ∈ H i := by
  induction S generalizing h with
  | nil => simp [diffs]
  | cons q S ih =>
    obtain ⟨v, h'⟩ := q
    obtain ⟨hv, hv', hS⟩ := hS
    intro s hs
    simp only [List.map_cons, diffs, List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact ⟨v.1, mem_diff hv hv'⟩
    · exact ih h' hS s hs

lemma diffs_prod (h : G) (C : List G) : h * (diffs h C).prod = C.getLast?.getD h := by
  induction C generalizing h with
  | nil => simp [diffs]
  | cons h' C ih => simp [diffs, ← mul_assoc, ih, List.getLast?_cons]

lemma diffs_length (h : G) (C : List G) : (diffs h C).length = C.length := by
  induction C generalizing h with
  | nil => rfl
  | cons h' C ih => simp [diffs, ih]

/-! ### Contracting a loop -/

theorem main_fin (L : List (Σ i, G ⧸ H i))
    (hL : (cosetComplex G H).IsPathFrom (Xv H 1) (Xv H 1) L) (A : ℕ)
    (hA : ∀ w : FreeGroup (CosetGen H), FreeGroup.lift Subtype.val w = 1 →
      wordLength w ≤ L.length - 1 → area (cosetRel H) w ≤ A) :
    Rw (cosetComplex G H) (Xv H 1) (3 * (L.length - 1) + 6 * A) L [Xv H 1] := by
  have hW : WLoop (cosetComplex G H) (Xv H 1) L := ⟨walk_of_path hL.1, hL.2.1, hL.2.2⟩
  obtain ⟨⟨hne, -, hch⟩, hh, hl⟩ := hL
  have hnrm : nrm L = L := by
    cases L with
    | nil => exact absurd rfl hne
    | cons a l => exact dd_of_path hch
  suffices h : LH H (3 * (L.length - 1) + 6 * A) L [Xv H 1] by
    have := h.hom.2 hW
    rwa [hnrm] at this
  cases L with
  | nil => exact absurd rfl hne
  | cons a rest =>
  simp only [List.head?_cons, Option.some.injEq] at hh
  subst hh
  cases rest with
  | nil => exact LHom.refl _ _
  | cons v T =>
  have fc := hch.imp (fun _ _ h => h.2)
  rw [List.isChain_cons_cons] at fc
  rw [List.getLast?_cons_cons] at hl
  obtain ⟨g₀, hg1, hgv⟩ := mems_of_face2 fc.1
  obtain ⟨S, hS, hlen, hlast, hgal⟩ := gallery T v g₀ g₀ hgv fc.2 (fun y hy => by
    rw [hl] at hy; cases hy; exact hg1)
  have hXg : Xv H g₀ = Xv H 1 := Xv_eq hg1
  set sv := diffs g₀ (S.map Prod.snd)
  have hsv : ∀ s ∈ sv, ∃ i, s ∈ H i := diffs_mem g₀ S hS
  have hsvp : sv.prod = 1 := by
    have := diffs_prod g₀ (S.map Prod.snd)
    rw [hlast] at this
    simpa using this
  have hsvl : sv.length = T.length + 1 := by simp [sv, diffs_length, hlen]
  have aswap := gal_swap g₀ S (encS H g₀ sv) hS (galOK_encS g₀ sv hsv) (by rw [encS_diffs])
  rw [← ee_eq_gt] at aswap
  change LH H _ (Xv H g₀ :: gt H S) (Ee H g₀ sv) at aswap
  set Lw := sv.filterMap (toLet (H := H))
  have afilt := lhom_filter sv hsv g₀
  have hlift : FreeGroup.lift Subtype.val (FreeGroup.mk Lw) = 1 := by
    exact (prod_filter sv hsv).trans hsvp
  have hwl : wordLength (FreeGroup.mk Lw) ≤ (Xv H 1 :: v :: T).length - 1 := by
    refine (wl_le Lw).trans ?_
    have : Lw.length ≤ sv.length := List.length_filterMap_le _ _
    simp only [List.length_cons]; omega
  have harea := hA _ hlift hwl
  obtain ⟨l, hlc, hll⟩ : ∃ l : List (FreeGroup (CosetGen H) × FreeGroup (CosetGen H)),
      ((∀ p ∈ l, p.2 ∈ cosetRel H ∨ p.2⁻¹ ∈ cosetRel H) ∧
        FreeGroup.mk Lw = (l.map (fun p => p.1⁻¹ * p.2 * p.1)).prod) ∧ l.length ≤ A := by
    have : area (cosetRel H) (FreeGroup.mk Lw) < ((A + 1 : ℕ) : ℕ∞) :=
      lt_of_le_of_lt harea (by exact_mod_cast Nat.lt_succ_self A)
    unfold area at this
    rw [iInf_lt_iff] at this
    obtain ⟨l, hl⟩ := this
    rw [iInf_lt_iff] at hl
    obtain ⟨hc, hlt⟩ := hl
    exact ⟨l, hc, by exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast hlt)⟩
  obtain ⟨Lt, hmk, hLt⟩ := lhom_total l hlc.1
  have hred : FreeGroup.reduce Lw = FreeGroup.reduce Lt := by
    rw [← FreeGroup.toWord_mk, ← FreeGroup.toWord_mk, hmk, ← hlc.2]
  have ar1 := lhom_red (FreeGroup.reduce.red : FreeGroup.Red Lw (FreeGroup.reduce Lw)) g₀
  have ar2 := (lhom_red (FreeGroup.reduce.red : FreeGroup.Red Lt (FreeGroup.reduce Lt)) g₀).symm
  rw [hred] at ar1
  have aend := hLt g₀
  obtain ⟨M, hM⟩ := List.getLast?_eq_some_iff.1 hl
  have ast := (lhom_stutter (X := cosetComplex G H) (v₀ := Xv H 1) (a := Xv H 1)).ctx
    (Xv H 1 :: M) []
  have agal := hgal.ctx [Xv H g₀] []
  rw [hXg] at agal aswap aend
  rw [hM] at agal
  simp only [List.append_nil, List.cons_append, List.append_assoc]
    at ast agal
  have key : LH H (T.length + 2 * S.length + 6 * l.length) (Xv H 1 :: v :: T) [Xv H 1] := by
    rw [hM]
    have := ast.symm.trans (agal.symm.trans (aswap.trans (afilt.trans (ar1.trans
      (ar2.trans aend)))))
    exact this.mono (by omega)
  exact key.mono (by simp only [List.length_cons]; omega)

end Coset

section Final

open PolySwap.KMS

theorem main {G : Type*} [Group G] [Finite G] {ι : Type*} [Fintype ι]
    (hι : 3 ≤ Fintype.card ι) (H : ι → Subgroup G)
    (hY : (cosetComplex G H).IsOneConnected) (D : ℕ) (hD : (cosetComplex G H).diam = D) :
    ∃ C : WComplex.OneCone (Σ i, G ⧸ H i), (cosetComplex G H).IsOneCone C ∧
      (cosetComplex G H).rad0 C ≤ D ∧
      (cosetComplex G H).rad1 C ≤ 15 * (cosetDehn H (2 * D + 1) + ((2 * D + 1 : ℕ) : ℕ∞)) := by
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  set X := cosetComplex G H
  set v₀ := Xv H 1
  have hvert : ∀ u, u ∈ X.vertices := fun u => vert_of_face X (face1 u) (Finset.mem_singleton_self u)
  have hpath : ∀ u, ∃ P, X.IsPathFrom v₀ u P ∧ P.length ≤ D + 1 := by
    intro u
    have h1 : X.edist v₀ u ≤ X.diam :=
      le_iSup₂_of_le (f := fun u _ => ⨆ v ∈ X.vertices, X.edist u v) v₀ (hvert v₀)
        (le_iSup₂_of_le (f := fun v _ => X.edist v₀ v) u (hvert u) le_rfl)
    rw [hD] at h1
    have h2 : X.edist v₀ u < ((D + 1 : ℕ) : ℕ∞) :=
      lt_of_le_of_lt h1 (by exact_mod_cast Nat.lt_succ_self D)
    unfold WComplex.edist at h2
    rw [iInf_lt_iff] at h2
    obtain ⟨P, hP⟩ := h2
    rw [iInf_lt_iff] at hP
    obtain ⟨hP, hlt⟩ := hP
    have : P.length - 1 < D + 1 := by exact_mod_cast hlt
    exact ⟨P, hP, by omega⟩
  have hsingle : X.IsPathFrom v₀ v₀ [v₀] :=
    ⟨⟨by simp, by simp [hvert], List.isChain_singleton _⟩, rfl, rfl⟩
  let Pf : (Σ i, G ⧸ H i) → List (Σ i, G ⧸ H i) := fun u =>
    if u = v₀ then [v₀] else Classical.choose (hpath u)
  have hPf : ∀ u, X.IsPathFrom v₀ u (Pf u) ∧ (Pf u).length ≤ D + 1 := by
    intro u
    by_cases hu : u = v₀
    · subst hu; simp only [Pf, if_true]; exact ⟨hsingle, by simp⟩
    · simp only [Pf, hu, if_false]; exact Classical.choose_spec (hpath u)
  have hT : ∀ u v, Edge X u v → ∃ T : List (List (Σ i, G ⧸ H i)),
      T.head? = some (pcat (pcat (Pf u) [u, v]) (Pf v).reverse) ∧
      T.IsChain (fun A B => X.TR v₀ A B ∨ X.BT v₀ A B) ∧ T.getLast? = some [v₀] ∧
      ((X.trCount v₀ T : ℕ) : ℕ∞) ≤
        15 * (cosetDehn H (2 * D + 1) + ((2 * D + 1 : ℕ) : ℕ∞)) := by
    intro u v huv
    set L := pcat (pcat (Pf u) [u, v]) (Pf v).reverse
    have hL : X.IsPathFrom v₀ v₀ L := by
      refine path_pcat (path_pcat (hPf u).1 ?_) (path_rev (hPf v).1)
      exact ⟨⟨by simp, by simp [hvert], List.IsChain.cons_cons huv (List.isChain_singleton _)⟩,
        rfl, rfl⟩
    have hLlen : L.length - 1 ≤ 2 * D + 1 := by
      have h1 := (hPf u).2
      have h2 := (hPf v).2
      simp only [L, pcat, List.length_append, List.length_tail, List.length_reverse,
        List.length_cons, List.length_nil]
      omega
    cases hdehn : cosetDehn H (2 * D + 1) using ENat.recTopCoe with
    | top =>
      obtain ⟨T, h1, h2, h3⟩ := eqv_chain (fun A B h => h.elim (fun h => Or.inl (Or.symm h))
        (fun h => Or.inr (Or.symm h))) (hY.2 v₀ (hvert v₀) L hL)
      refine ⟨T, h1, h3, h2, ?_⟩
      simp
    | coe A =>
      have hA : ∀ w : FreeGroup (CosetGen H), FreeGroup.lift Subtype.val w = 1 →
          wordLength w ≤ L.length - 1 → area (cosetRel H) w ≤ A := by
        intro w h1 h2
        rw [← hdehn]
        exact le_iSup₂_of_le (f := fun w (_ : FreeGroup.lift Subtype.val w = 1 ∧
          wordLength w ≤ 2 * D + 1) => area (cosetRel H) w) w ⟨h1, h2.trans hLlen⟩ le_rfl
      obtain ⟨T, h1, h2, h3, h4⟩ := (main_fin L hL A hA).chain
      refine ⟨T, h1, h3, h2, ?_⟩
      have : (cosetComplex G H).trCount (Xv H 1) T ≤ 15 * (A + (2 * D + 1)) := by omega
      exact_mod_cast this
  refine ⟨⟨v₀, Pf, fun u v => if h : Edge X u v then Classical.choose (hT u v h) else []⟩,
    ⟨hvert v₀, by simp [Pf], fun u _ hu => by simpa [Pf, hu] using (hPf u).1, ?_⟩, ?_, ?_⟩
  · intro u v huv hf
    have h : Edge X u v := ⟨huv, hf⟩
    simp only [dif_pos h]
    obtain ⟨h1, h2, h3, -⟩ := Classical.choose_spec (hT u v h)
    exact ⟨h1, h2, h3⟩
  · refine iSup₂_le fun u _ => ?_
    have := (hPf u).2
    exact_mod_cast (show (Pf u).length - 1 ≤ D by omega)
  · refine iSup_le fun u => iSup_le fun v => iSup_le fun h => ?_
    have h' : Edge X u v := h
    simp only [dif_pos h']
    exact (Classical.choose_spec (hT u v h')).2.2.2

end Final

end PolySwap.KMS.Sol319

open PolySwap.KMS in
theorem solution {G : Type*} [Group G] [Finite G] {ι : Type*} [Fintype ι]
    (hι : 3 ≤ Fintype.card ι) (H : ι → Subgroup G)
    (hY : (cosetComplex G H).IsOneConnected) (D : ℕ) (hD : (cosetComplex G H).diam = D) :
    ∃ C : WComplex.OneCone (Σ i, G ⧸ H i), (cosetComplex G H).IsOneCone C ∧
      (cosetComplex G H).rad0 C ≤ D ∧
      (cosetComplex G H).rad1 C ≤ 15 * (cosetDehn H (2 * D + 1) + ((2 * D + 1 : ℕ) : ℕ∞)) :=
  PolySwap.KMS.Sol319.main hι H hY D hD
