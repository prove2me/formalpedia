-- Prove2me | solution 1 for StrongPerfectGraph.Main.double_split_perfect
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T06:27:14.579537+00:00
-- url     : https://prove2.me/submissions/b6b4fb56-3d43-4e72-8071-343e4c349935

import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsBasic
import Definitions.Def_StrongPerfectGraph_Main_IsPerfect

open StrongPerfectGraph.Main

namespace SPGTDoubleSplit

lemma chi_le_of_color {W : Type*} (K : SimpleGraph W) {α : Type*} [Fintype α] (f : W → α)
    (hf : ∀ u v, K.Adj u v → f u ≠ f v) : K.chromaticNumber ≤ (Fintype.card α : ℕ∞) :=
  (SimpleGraph.Coloring.mk f (fun {u v} h => hf u v h)).colorable.chromaticNumber_le

lemma card_le_clique {W : Type*} [Finite W] (K : SimpleGraph W) {α : Type*} [Fintype α]
    (g : α → W) (hg : Function.Injective g) (hadj : ∀ a b, a ≠ b → K.Adj (g a) (g b)) :
    Fintype.card α ≤ K.cliqueNum := by
  classical
  have hcl : K.IsClique ((Finset.univ.map ⟨g, hg⟩ : Finset W) : Set W) := by
    intro x hx y hy hxy
    simp only [Finset.coe_map, Function.Embedding.coeFn_mk, Finset.coe_univ, Set.image_univ,
      Set.mem_range] at hx hy
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact hadj a b (fun h => hxy (by rw [h]))
  have := hcl.card_le_cliqueNum
  simpa using this

/-- A 2-colourable graph has chromatic number at most its clique number. -/
lemma chi_le_clique_of_colorable_two {W : Type*} [Finite W] (K : SimpleGraph W)
    (hK : K.Colorable 2) : K.chromaticNumber ≤ (K.cliqueNum : ℕ∞) := by
  classical
  by_cases hbot : K = ⊥
  · subst hbot
    rcases isEmpty_or_nonempty W with hW | hW
    · simp [SimpleGraph.chromaticNumber_eq_zero_of_isEmpty]
    · rw [SimpleGraph.chromaticNumber_bot]
      obtain ⟨w⟩ := hW
      have : (⊥ : SimpleGraph W).IsClique (({w} : Finset W) : Set W) := by simp
      have h1 := this.card_le_cliqueNum
      simp at h1
      exact_mod_cast h1
  · obtain ⟨u, v, huv⟩ : ∃ u v, K.Adj u v := by
      by_contra h
      push Not at h
      exact hbot (by ext a b; simp [h a b])
    have hcl : K.IsClique (({u, v} : Finset W) : Set W) := by
      rw [Finset.coe_pair]; exact SimpleGraph.isClique_pair.mpr (fun _ => huv)
    have h2 := hcl.card_le_cliqueNum
    rw [Finset.card_pair huv.ne] at h2
    calc K.chromaticNumber ≤ 2 := hK.chromaticNumber_le
      _ ≤ (K.cliqueNum : ℕ∞) := by exact_mod_cast h2


section Labels

variable {V : Type*} [Finite V] (G : SimpleGraph V) {m n : ℕ}
  (e : (Fin m × Bool) ⊕ (Fin n × Bool) ≃ V) (X : Set V)

lemma chi_le_of_label {α : Type*} [Fintype α] (F : (Fin m × Bool) ⊕ (Fin n × Bool) → α)
    (hF : ∀ x y, e x ∈ X → e y ∈ X → G.Adj (e x) (e y) → F x ≠ F y) :
    (G.induce X).chromaticNumber ≤ (Fintype.card α : ℕ∞) := by
  apply chi_le_of_color (G.induce X) (fun u => F (e.symm u.1))
  intro u v huv
  have hu : e (e.symm u.1) ∈ X := by simp
  have hv : e (e.symm v.1) ∈ X := by simp
  apply hF _ _ hu hv
  simpa using huv

lemma card_le_clique_of_label {α : Type*} [Fintype α] (g : α → (Fin m × Bool) ⊕ (Fin n × Bool))
    (hg : Function.Injective g) (hgX : ∀ a, e (g a) ∈ X)
    (hadj : ∀ a b, a ≠ b → G.Adj (e (g a)) (e (g b))) :
    Fintype.card α ≤ (G.induce X).cliqueNum := by
  apply card_le_clique (G.induce X) (fun a => (⟨e (g a), hgX a⟩ : X))
  · intro a b hab
    apply hg
    have := congrArg Subtype.val hab
    simpa using this
  · intro a b hab
    simpa using hadj a b hab

end Labels



lemma bool_other {Q : Bool → Prop} (h : Q false ∨ Q true) (b : Bool) (hb : ¬ Q b) : Q (!b) := by
  cases b <;> simp_all

section Core

variable {V : Type*} [Finite V] (G : SimpleGraph V) {m n : ℕ}
  (e : (Fin m × Bool) ⊕ (Fin n × Bool) ≃ V) (σ : Fin m → Fin n → Bool) (X : Set V)

/-- The pair `j` has a vertex in `X`. -/
def Pr (j : Fin n) : Prop := e (.inr (j, false)) ∈ X ∨ e (.inr (j, true)) ∈ X

/-- Only the non-neighbour of `(i,s)` in pair `j` lies in `X`. -/
def Fr (i : Fin m) (s : Bool) (j : Fin n) : Prop :=
  e (.inr (j, !(Bool.xor s (σ i j)))) ∈ X ∧ e (.inr (j, Bool.xor s (σ i j))) ∉ X

variable {G e σ X}

omit [Finite V] in
lemma pr_of {j : Fin n} {t : Bool} (h : e (.inr (j, t)) ∈ X) : Pr e X j := by
  cases t
  · exact Or.inl h
  · exact Or.inr h

omit [Finite V] in
lemma pr_of_fr {i : Fin m} {s : Bool} {j : Fin n} (h : Fr e σ X i s j) : Pr e X j := pr_of h.1

omit [Finite V] in
lemma fr_two {i : Fin m} {s t : Bool} {j : Fin n} (hst : s ≠ t) (h1 : Fr e σ X i s j)
    (h2 : Fr e σ X i t j) : False := by
  obtain ⟨a1, b1⟩ := h1
  obtain ⟨a2, b2⟩ := h2
  have ht : t = !s := by revert hst; cases s <;> cases t <;> decide
  subst ht
  apply b2
  have : Bool.xor (!s) (σ i j) = !(Bool.xor s (σ i j)) := by cases s <;> cases σ i j <;> rfl
  rw [this]; exact a1

/-- A noncomputable choice of a free pair. -/
noncomputable def pick (i : Fin m) (s : Bool) (h : ∃ j, Fr e σ X i s j) : {j // Pr e X j} :=
  ⟨h.choose, pr_of_fr h.choose_spec⟩

omit [Finite V] in
lemma pick_spec (i : Fin m) (s : Bool) (h : ∃ j, Fr e σ X i s j) :
    Fr e σ X i s (pick (e := e) (σ := σ) (X := X) i s h).1 := h.choose_spec

end Core


section Cases

open Classical

variable {V : Type*} [Finite V] {G : SimpleGraph V} {m n : ℕ}
  {e : (Fin m × Bool) ⊕ (Fin n × Bool) ≃ V} {σ : Fin m → Fin n → Bool} {X : Set V}

lemma case_noP
    (hAA : ∀ i k s t, G.Adj (e (.inl (i, s))) (e (.inl (k, t))) → i = k ∧ s ≠ t)
    (hP : ∀ j, ¬ Pr e X j) :
    (G.induce X).chromaticNumber ≤ ((G.induce X).cliqueNum : ℕ∞) := by
  apply chi_le_clique_of_colorable_two
  let F : (Fin m × Bool) ⊕ (Fin n × Bool) → Bool := fun x =>
    match x with
    | .inl (_, s) => s
    | .inr _ => false
  have := chi_le_of_label G e X F (by
    intro x y hx hy hxy
    rcases x with ⟨i, s⟩ | ⟨j, s⟩
    · rcases y with ⟨k, t⟩ | ⟨k, t⟩
      · exact (hAA i k s t hxy).2
      · exact absurd (pr_of hy) (hP k)
    · exact absurd (pr_of hx) (hP j))
  rw [Fintype.card_bool] at this
  exact (SimpleGraph.chromaticNumber_le_iff_colorable).mp (by exact_mod_cast this)

/-- One present vertex from each present pair. -/
noncomputable def rep (e : (Fin m × Bool) ⊕ (Fin n × Bool) ≃ V) (X : Set V)
    (j : {j // Pr e X j}) : (Fin m × Bool) ⊕ (Fin n × Bool) :=
  open Classical in
  if e (.inr (j.1, false)) ∈ X then .inr (j.1, false) else .inr (j.1, true)

omit [Finite V] in
lemma rep_mem (j : {j // Pr e X j}) : e (rep e X j) ∈ X := by
  classical
  unfold rep; split_ifs with h
  · exact h
  · exact j.2.resolve_left h

omit [Finite V] in
lemma rep_eq (j : {j // Pr e X j}) : ∃ t, rep e X j = .inr (j.1, t) := by
  classical
  unfold rep; split_ifs
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

omit [Finite V] in
lemma rep_inj : Function.Injective (rep e X) := by
  intro a b hab
  obtain ⟨t, ht⟩ := rep_eq (e := e) (X := X) a
  obtain ⟨u, hu⟩ := rep_eq (e := e) (X := X) b
  rw [ht, hu] at hab
  simp only [Sum.inr.injEq, Prod.mk.injEq] at hab
  exact Subtype.ext hab.1

lemma clique_P
    (hCC : ∀ j k s t, G.Adj (e (.inr (j, s))) (e (.inr (k, t))) ↔ j ≠ k) :
    Fintype.card {j // Pr e X j} ≤ (G.induce X).cliqueNum := by
  classical
  apply card_le_clique_of_label G e X (rep e X) rep_inj rep_mem
  intro a b hab
  obtain ⟨t, ht⟩ := rep_eq (e := e) (X := X) a
  obtain ⟨u, hu⟩ := rep_eq (e := e) (X := X) b
  rw [ht, hu]
  exact (hCC _ _ _ _).mpr (fun h => hab (Subtype.ext h))

lemma color_allfree
    (hAA : ∀ i k s t, G.Adj (e (.inl (i, s))) (e (.inl (k, t))) → i = k ∧ s ≠ t)
    (hCC : ∀ j k s t, G.Adj (e (.inr (j, s))) (e (.inr (k, t))) ↔ j ≠ k)
    (hAC : ∀ i j s t, G.Adj (e (.inl (i, s))) (e (.inr (j, t))) ↔ t = Bool.xor s (σ i j))
    (d0 : {j // Pr e X j})
    (hR : ∀ i s, e (.inl (i, s)) ∈ X → ∃ j, Fr e σ X i s j) :
    (G.induce X).chromaticNumber ≤ (Fintype.card {j // Pr e X j} : ℕ∞) := by
  classical
  let F : (Fin m × Bool) ⊕ (Fin n × Bool) → {j // Pr e X j} := fun x =>
    match x with
    | .inl (i, s) => if h : ∃ j, Fr e σ X i s j then pick i s h else d0
    | .inr (j, _) => if h : Pr e X j then ⟨j, h⟩ else d0
  have hAC' : ∀ i s j t, e (.inl (i, s)) ∈ X → e (.inr (j, t)) ∈ X →
      G.Adj (e (.inl (i, s))) (e (.inr (j, t))) → F (.inl (i, s)) ≠ F (.inr (j, t)) := by
    intro i s j t hx hy hxy
    have hex := hR i s hx
    simp only [F, dif_pos hex, dif_pos (pr_of hy)]
    intro heq
    have hsp := pick_spec i s hex
    rw [heq] at hsp
    rw [hAC] at hxy
    subst hxy
    exact hsp.2 hy
  apply chi_le_of_label G e X F
  intro x y hx hy hxy
  rcases x with ⟨i, s⟩ | ⟨j, s⟩ <;> rcases y with ⟨k, t⟩ | ⟨k, t⟩
  · obtain ⟨rfl, hst⟩ := hAA i k s t hxy
    have hex1 := hR i s hx
    have hex2 := hR i t hy
    simp only [F, dif_pos hex1, dif_pos hex2]
    intro heq
    have hs1 := pick_spec i s hex1
    rw [heq] at hs1
    exact fr_two hst hs1 (pick_spec i t hex2)
  · exact hAC' i s k t hx hy hxy
  · exact (hAC' k t j s hy hx hxy.symm).symm
  · have hjk := (hCC j k s t).mp hxy
    simp only [F, dif_pos (pr_of hx), dif_pos (pr_of hy)]
    intro heq
    exact hjk (congrArg Subtype.val heq)


/-- The neighbour labels of a "needy" ab-vertex. -/
def gN (i0 : Fin m) (s0 : Bool) (σ : Fin m → Fin n → Bool) (P : Fin n → Prop) :
    Option {j // P j} → (Fin m × Bool) ⊕ (Fin n × Bool)
  | none => .inl (i0, s0)
  | some j => .inr (j.1, Bool.xor s0 (σ i0 j.1))

lemma clique_need
    (hCC : ∀ j k s t, G.Adj (e (.inr (j, s))) (e (.inr (k, t))) ↔ j ≠ k)
    (hAC : ∀ i j s t, G.Adj (e (.inl (i, s))) (e (.inr (j, t))) ↔ t = Bool.xor s (σ i j))
    (i0 : Fin m) (s0 : Bool) (hx0 : e (.inl (i0, s0)) ∈ X) (hnf : ∀ j, ¬ Fr e σ X i0 s0 j) :
    Fintype.card (Option {j // Pr e X j}) ≤ (G.induce X).cliqueNum := by
  apply card_le_clique_of_label G e X (gN i0 s0 σ (Pr e X))
  · intro a b hab
    rcases a with _ | a <;> rcases b with _ | b <;> simp only [gN, reduceCtorEq] at hab
    · rfl
    · simp only [Sum.inr.injEq, Prod.mk.injEq] at hab
      rw [Subtype.ext hab.1]
  · intro o
    rcases o with _ | ⟨j, hj⟩
    · exact hx0
    · show e (.inr (j, Bool.xor s0 (σ i0 j))) ∈ X
      by_contra hno
      exact hnf j ⟨bool_other (Q := fun t => e (.inr (j, t)) ∈ X) hj _ hno, hno⟩
  · intro a b hab
    rcases a with _ | a <;> rcases b with _ | b
    · exact absurd rfl hab
    · exact (hAC _ _ _ _).mpr rfl
    · exact ((hAC _ _ _ _).mpr rfl).symm
    · exact (hCC _ _ _ _).mpr (fun h => hab (by rw [Subtype.ext h]))

/-- Colour of a cd-vertex when pair `j0` is split. -/
noncomputable def fcdF (e : (Fin m × Bool) ⊕ (Fin n × Bool) ≃ V) (X : Set V) (j0 : Fin n)
    (j : Fin n) (t : Bool) : Option {j // Pr e X j} :=
  if j = j0 ∧ t = true then none else if h : Pr e X j then some ⟨j, h⟩ else none

omit [Finite V] in
lemma fcdF_ne {j0 j k : Fin n} {t u : Bool} (hj : Pr e X j) (hk : Pr e X k) (hjk : j ≠ k) :
    fcdF e X j0 j t ≠ fcdF e X j0 k u := by
  unfold fcdF
  rw [dif_pos hj, dif_pos hk]
  split_ifs with h1 h2 h2
  · exact absurd (h1.1.trans h2.1.symm) hjk
  · simp
  · simp
  · intro h; simp only [Option.some.injEq, Subtype.mk.injEq] at h; exact hjk h

omit [Finite V] in
lemma fcdF_pair {j0 : Fin n} (hP0 : Pr e X j0) (b : Bool) :
    fcdF e X j0 j0 b ≠ fcdF e X j0 j0 (!b) := by
  unfold fcdF
  rw [dif_pos hP0]
  cases b <;> simp

omit [Finite V] in
lemma fcdF_j0 {j0 : Fin n} (hP0 : Pr e X j0) (b : Bool) :
    fcdF e X j0 j0 b = none ∨ fcdF e X j0 j0 b = some ⟨j0, hP0⟩ := by
  unfold fcdF
  rw [dif_pos hP0]
  split_ifs <;> simp

lemma color_F
    (hAA : ∀ i k s t, G.Adj (e (.inl (i, s))) (e (.inl (k, t))) → i = k ∧ s ≠ t)
    (hCC : ∀ j k s t, G.Adj (e (.inr (j, s))) (e (.inr (k, t))) ↔ j ≠ k)
    (hAC : ∀ i j s t, G.Adj (e (.inl (i, s))) (e (.inr (j, t))) ↔ t = Bool.xor s (σ i j))
    (j0 : Fin n) (hj0f : e (.inr (j0, false)) ∈ X) (hj0t : e (.inr (j0, true)) ∈ X) :
    (G.induce X).chromaticNumber ≤ (Fintype.card (Option {j // Pr e X j}) : ℕ∞) := by
  have hP0 : Pr e X j0 := Or.inl hj0f
  have hfree_ne : ∀ i s j, Fr e σ X i s j → j ≠ j0 := by
    intro i s j hfr hj
    subst hj
    apply hfr.2
    cases Bool.xor s (σ i j) <;> assumption
  let F : (Fin m × Bool) ⊕ (Fin n × Bool) → Option {j // Pr e X j} := fun x =>
    match x with
    | .inl (i, s) => if h : ∃ j, Fr e σ X i s j then some (pick i s h)
        else fcdF e X j0 j0 (!(Bool.xor s (σ i j0)))
    | .inr (j, t) => fcdF e X j0 j t
  have hAC' : ∀ i s j t, e (.inl (i, s)) ∈ X → e (.inr (j, t)) ∈ X →
      G.Adj (e (.inl (i, s))) (e (.inr (j, t))) → F (.inl (i, s)) ≠ F (.inr (j, t)) := by
    intro i s j t hx hy hxy
    rw [hAC] at hxy
    subst hxy
    have hPj := pr_of hy
    by_cases hex : ∃ j, Fr e σ X i s j
    · simp only [F, dif_pos hex]
      unfold fcdF
      rw [dif_pos hPj]
      split_ifs
      · simp
      · intro heq
        simp only [Option.some.injEq] at heq
        have hsp := pick_spec i s hex
        rw [heq] at hsp
        exact hsp.2 hy
    · simp only [F, dif_neg hex]
      by_cases hjj : j = j0
      · subst hjj
        have := fcdF_pair (e := e) (X := X) hP0 (Bool.xor s (σ i j))
        exact fun h => this h.symm
      · have hR : fcdF e X j0 j (Bool.xor s (σ i j)) = some ⟨j, hPj⟩ := by
          unfold fcdF; rw [if_neg (fun h => hjj h.1), dif_pos hPj]
        rw [hR]
        rcases fcdF_j0 (e := e) (X := X) hP0 (!(Bool.xor s (σ i j0))) with h | h <;> rw [h]
        · simp
        · intro h; simp only [Option.some.injEq, Subtype.mk.injEq] at h; exact hjj h.symm
  apply chi_le_of_label G e X F
  intro x y hx hy hxy
  rcases x with ⟨i, s⟩ | ⟨j, s⟩ <;> rcases y with ⟨k, t⟩ | ⟨k, t⟩
  · obtain ⟨rfl, hst⟩ := hAA i k s t hxy
    have ht : t = !s := by revert hst; cases s <;> cases t <;> decide
    by_cases hex1 : ∃ j, Fr e σ X i s j <;> by_cases hex2 : ∃ j, Fr e σ X i t j
    · simp only [F, dif_pos hex1, dif_pos hex2]
      intro heq
      simp only [Option.some.injEq] at heq
      have hs1 := pick_spec i s hex1
      rw [heq] at hs1
      exact fr_two hst hs1 (pick_spec i t hex2)
    · have hne := hfree_ne i s _ (pick_spec i s hex1)
      simp only [F, dif_pos hex1, dif_neg hex2]
      rcases fcdF_j0 (e := e) (X := X) hP0 (!(Bool.xor t (σ i j0))) with h | h <;> rw [h]
      · simp
      · intro heq; simp only [Option.some.injEq] at heq; exact hne (congrArg Subtype.val heq)
    · have hne := hfree_ne i t _ (pick_spec i t hex2)
      simp only [F, dif_neg hex1, dif_pos hex2]
      rcases fcdF_j0 (e := e) (X := X) hP0 (!(Bool.xor s (σ i j0))) with h | h <;> rw [h]
      · simp
      · intro heq; simp only [Option.some.injEq] at heq
        exact hne (congrArg Subtype.val heq).symm
    · simp only [F, dif_neg hex1, dif_neg hex2]
      subst ht
      have : (!(Bool.xor (!s) (σ i j0))) = !(!(Bool.xor s (σ i j0))) := by
        cases s <;> cases σ i j0 <;> rfl
      rw [this]
      exact fcdF_pair (e := e) (X := X) hP0 _
  · exact hAC' i s k t hx hy hxy
  · exact (hAC' k t j s hy hx hxy.symm).symm
  · exact fcdF_ne (pr_of hx) (pr_of hy) ((hCC j k s t).mp hxy)

lemma color_noF
    (hAA : ∀ i k s t, G.Adj (e (.inl (i, s))) (e (.inl (k, t))) → i = k ∧ s ≠ t)
    (hCC : ∀ j k s t, G.Adj (e (.inr (j, s))) (e (.inr (k, t))) ↔ j ≠ k)
    (hAC : ∀ i j s t, G.Adj (e (.inl (i, s))) (e (.inr (j, t))) ↔ t = Bool.xor s (σ i j))
    (jP : Fin n) (hjP : Pr e X jP)
    (hF : ∀ j, e (.inr (j, false)) ∈ X → e (.inr (j, true)) ∉ X) :
    (G.induce X).chromaticNumber ≤ (Fintype.card (Option {j // Pr e X j}) : ℕ∞) := by
  let fcd : Fin n → Option {j // Pr e X j} := fun j =>
    if h : Pr e X j then some ⟨j, h⟩ else none
  let F : (Fin m × Bool) ⊕ (Fin n × Bool) → Option {j // Pr e X j} := fun x =>
    match x with
    | .inl (i, s) => if h : ∃ j, Fr e σ X i s j then some (pick i s h) else none
    | .inr (j, _) => fcd j
  have hAC' : ∀ i s j t, e (.inl (i, s)) ∈ X → e (.inr (j, t)) ∈ X →
      G.Adj (e (.inl (i, s))) (e (.inr (j, t))) → F (.inl (i, s)) ≠ F (.inr (j, t)) := by
    intro i s j t hx hy hxy
    rw [hAC] at hxy
    subst hxy
    have hPj := pr_of hy
    by_cases hex : ∃ j, Fr e σ X i s j
    · simp only [F, dif_pos hex, fcd, dif_pos hPj]
      intro heq
      simp only [Option.some.injEq] at heq
      have hsp := pick_spec i s hex
      rw [heq] at hsp
      exact hsp.2 hy
    · simp [F, dif_neg hex, fcd, dif_pos hPj]
  apply chi_le_of_label G e X F
  intro x y hx hy hxy
  rcases x with ⟨i, s⟩ | ⟨j, s⟩ <;> rcases y with ⟨k, t⟩ | ⟨k, t⟩
  · obtain ⟨rfl, hst⟩ := hAA i k s t hxy
    have ht : t = !s := by revert hst; cases s <;> cases t <;> decide
    by_cases hex1 : ∃ j, Fr e σ X i s j <;> by_cases hex2 : ∃ j, Fr e σ X i t j
    · simp only [F, dif_pos hex1, dif_pos hex2]
      intro heq
      simp only [Option.some.injEq] at heq
      have hs1 := pick_spec i s hex1
      rw [heq] at hs1
      exact fr_two hst hs1 (pick_spec i t hex2)
    · simp [F, dif_pos hex1, dif_neg hex2]
    · simp [F, dif_neg hex1, dif_pos hex2]
    · exfalso
      subst ht
      -- the single present vertex of pair `jP` is free for one of the two ab-vertices
      have hsing := hF jP
      have hx1 : ∀ j, ¬ Fr e σ X i s j := fun j h => hex1 ⟨j, h⟩
      have hx2 : ∀ j, ¬ Fr e σ X i (!s) j := fun j h => hex2 ⟨j, h⟩
      have a1 := hx1 jP
      have a2 := hx2 jP
      unfold Fr at a1 a2
      unfold Pr at hjP
      have hb : Bool.xor (!s) (σ i jP) = !(Bool.xor s (σ i jP)) := by
        cases s <;> cases σ i jP <;> rfl
      rw [hb, Bool.not_not] at a2
      generalize Bool.xor s (σ i jP) = b at a1 a2
      cases b <;> simp only [Bool.not_false, Bool.not_true] at a1 a2 <;> tauto
  · exact hAC' i s k t hx hy hxy
  · exact (hAC' k t j s hy hx hxy.symm).symm
  · have hjk := (hCC j k s t).mp hxy
    simp only [F, fcd, dif_pos (pr_of hx), dif_pos (pr_of hy)]
    intro heq
    simp only [Option.some.injEq, Subtype.mk.injEq] at heq
    exact hjk heq

end Cases

/-- The core estimate: in a double split graph every induced subgraph satisfies `χ ≤ ω`. -/
theorem key {V : Type*} [Finite V] (G : SimpleGraph V) {m n : ℕ}
    (e : (Fin m × Bool) ⊕ (Fin n × Bool) ≃ V) (σ : Fin m → Fin n → Bool)
    (hAA : ∀ i k s t, G.Adj (e (.inl (i, s))) (e (.inl (k, t))) → i = k ∧ s ≠ t)
    (hCC : ∀ j k s t, G.Adj (e (.inr (j, s))) (e (.inr (k, t))) ↔ j ≠ k)
    (hAC : ∀ i j s t, G.Adj (e (.inl (i, s))) (e (.inr (j, t))) ↔ t = Bool.xor s (σ i j))
    (X : Set V) : (G.induce X).chromaticNumber ≤ ((G.induce X).cliqueNum : ℕ∞) := by
  classical
  by_cases hP : ∃ j, Pr e X j
  swap
  · push Not at hP
    exact case_noP hAA hP
  obtain ⟨jP, hjP⟩ := hP
  by_cases hR : ∃ i s, e (.inl (i, s)) ∈ X ∧ ∀ j, ¬ Fr e σ X i s j
  · obtain ⟨i0, s0, hx0, hnf⟩ := hR
    have h2 := clique_need hCC hAC i0 s0 hx0 hnf
    have h1 : (G.induce X).chromaticNumber ≤ (Fintype.card (Option {j // Pr e X j}) : ℕ∞) := by
      by_cases hF : ∃ j0, e (.inr (j0, false)) ∈ X ∧ e (.inr (j0, true)) ∈ X
      · obtain ⟨j0, hf, ht⟩ := hF
        exact color_F hAA hCC hAC j0 hf ht
      · push Not at hF
        exact color_noF hAA hCC hAC jP hjP hF
    exact h1.trans (by exact_mod_cast h2)
  · push Not at hR
    have h1 := color_allfree hAA hCC hAC ⟨jP, hjP⟩ hR
    have h2 := clique_P (G := G) (e := e) (X := X) hCC
    exact h1.trans (by exact_mod_cast h2)

end SPGTDoubleSplit

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : IsDoubleSplit G) : IsPerfect G := by
  classical
  obtain ⟨m, n, -, -, e, h1, h2, h3, h4, h5⟩ := hG
  let σ : Fin m → Fin n → Bool := fun i j =>
    !(decide (G.Adj (e (.inl (i, false))) (e (.inr (j, false)))))
  have hAA : ∀ i k s t, G.Adj (e (.inl (i, s))) (e (.inl (k, t))) → i = k ∧ s ≠ t := by
    intro i k s t h
    by_cases hik : i = k
    · subst hik
      refine ⟨rfl, fun hst => ?_⟩
      subst hst
      exact G.irrefl h
    · exact absurd h (h3 i k hik s t)
  have hCC : ∀ j k s t, G.Adj (e (.inr (j, s))) (e (.inr (k, t))) ↔ j ≠ k := by
    intro j k s t
    constructor
    · intro h hjk
      subst hjk
      cases s <;> cases t
      · exact G.irrefl h
      · exact h2 j h
      · exact h2 j h.symm
      · exact G.irrefl h
    · intro hjk
      exact h4 j k hjk s t
  have hAC : ∀ i j s t, G.Adj (e (.inl (i, s))) (e (.inr (j, t))) ↔ t = Bool.xor s (σ i j) := by
    intro i j s t
    rcases h5 i j with ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩
    · cases s <;> cases t <;> simp [σ, a, b, c, d]
    · cases s <;> cases t <;> simp [σ, a, b, c, d]
  intro X
  exact le_antisymm (SPGTDoubleSplit.key G e σ hAA hCC hAC X)
    (G.induce X).cliqueNum_le_chromaticNumber
