-- Prove2me | solution 1 for TenChallenges.isAlphaWQO_of_omega_one
-- status  : ACCEPTED   (prove)
-- author  : @Davide
-- created : 2026-11-23T11:32:41.437976+00:00
-- url     : https://prove2.me/submissions/0497b0a9-1dc1-41b8-b62a-065be683b66c

import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Ordinal.Principal
import Mathlib.Data.Set.Countable
import Definitions.Def_TenChallenges_AlphaWQO

universe u

set_option linter.deprecated false

open Ordinal Set

namespace TenChallenges.OmegaOne

/-! ### Unfolding equations for `leStar` -/

section Unfold

variable {Q : Type u} (le : Q → Q → Prop)

theorem leStar_zero_zero (X Y : VStar Q 0) :
    leStar le 0 X 0 Y ↔ le (cast (VStar_zero Q) X) (cast (VStar_zero Q) Y) := by
  unfold leStar
  simp only [Ordinal.limitRecOn_zero]

theorem leStar_zero_succ (X : VStar Q 0) (β : Ordinal.{u}) (Y : VStar Q (Order.succ β)) :
    leStar le 0 X (Order.succ β) Y ↔
      ∃ y ∈ (cast (VStar_succ Q β) Y).val, leStar le 0 X β y := by
  unfold leStar
  simp only [Ordinal.limitRecOn_zero, Ordinal.limitRecOn_succ]

theorem leStar_zero_limit (X : VStar Q 0) {β : Ordinal.{u}} (hb : Order.IsSuccLimit β)
    (Y : VStar Q β) :
    leStar le 0 X β Y ↔
      leStar le 0 X (Ordinal.typein (α := β.ToType) (· < ·) (cast (VStar_limit Q hb) Y).1)
        (cast (VStar_limit Q hb) Y).2 := by
  unfold leStar
  simp only [Ordinal.limitRecOn_zero, Ordinal.limitRecOn_limit _ _ _ _ hb]

theorem leStar_succ_zero (α : Ordinal.{u}) (X : VStar Q (Order.succ α)) (Y : VStar Q 0) :
    leStar le (Order.succ α) X 0 Y ↔
      ∀ x ∈ (cast (VStar_succ Q α) X).val, leStar le α x 0 Y := by
  conv_lhs => unfold leStar
  simp only [Ordinal.limitRecOn_succ, Ordinal.limitRecOn_zero]
  rfl

theorem leStar_succ_succ (α : Ordinal.{u}) (X : VStar Q (Order.succ α)) (β : Ordinal.{u})
    (Y : VStar Q (Order.succ β)) :
    leStar le (Order.succ α) X (Order.succ β) Y ↔
      ∀ x ∈ (cast (VStar_succ Q α) X).val,
        ∃ y ∈ (cast (VStar_succ Q β) Y).val, leStar le α x β y := by
  conv_lhs => unfold leStar
  simp only [Ordinal.limitRecOn_succ]
  rfl

theorem leStar_succ_limit (α : Ordinal.{u}) (X : VStar Q (Order.succ α)) {β : Ordinal.{u}}
    (hb : Order.IsSuccLimit β) (Y : VStar Q β) :
    leStar le (Order.succ α) X β Y ↔
      leStar le (Order.succ α) X
        (Ordinal.typein (α := β.ToType) (· < ·) (cast (VStar_limit Q hb) Y).1)
        (cast (VStar_limit Q hb) Y).2 := by
  unfold leStar
  simp only [Ordinal.limitRecOn_succ, Ordinal.limitRecOn_limit _ _ _ _ hb]

theorem leStar_limit_left {α : Ordinal.{u}} (ha : Order.IsSuccLimit α) (X : VStar Q α)
    (β : Ordinal.{u}) (Y : VStar Q β) :
    leStar le α X β Y ↔
      leStar le (Ordinal.typein (α := α.ToType) (· < ·) (cast (VStar_limit Q ha) X).1)
        (cast (VStar_limit Q ha) X).2 β Y := by
  conv_lhs => unfold leStar
  rw [Ordinal.limitRecOn_limit _ _ _ _ ha]
  rfl

end Unfold


/-! ### Positions and their views -/

/-- A position: an element of some level of the hierarchy. -/
abbrev Pos (Q : Type u) := Σ a : Ordinal.{u}, VStar Q a

section View
variable {Q : Type u}

/-- A position is, up to limit tags, an element of `Q` or a set of positions. -/
noncomputable def view (a : Ordinal.{u}) : VStar Q a → Q ⊕ Set (Pos Q) :=
  Ordinal.limitRecOn (motive := fun a => VStar Q a → Q ⊕ Set (Pos Q)) a
    (fun X => Sum.inl (cast (VStar_zero Q) X))
    (fun α _ X => Sum.inr ((fun x => (⟨α, x⟩ : Pos Q)) '' (cast (VStar_succ Q α) X).val))
    (fun a ha ih X => ih (Ordinal.typein (α := a.ToType) (· < ·) (cast (VStar_limit Q ha) X).1)
      (Ordinal.typein_lt_self _) (cast (VStar_limit Q ha) X).2)

theorem view_zero (X : VStar Q 0) : view 0 X = Sum.inl (cast (VStar_zero Q) X) := by
  unfold view; rw [Ordinal.limitRecOn_zero]

theorem view_succ (α : Ordinal.{u}) (X : VStar Q (Order.succ α)) :
    view (Order.succ α) X =
      Sum.inr ((fun x => (⟨α, x⟩ : Pos Q)) '' (cast (VStar_succ Q α) X).val) := by
  unfold view; rw [Ordinal.limitRecOn_succ]

theorem view_limit {a : Ordinal.{u}} (ha : Order.IsSuccLimit a) (X : VStar Q a) :
    view a X = view (Ordinal.typein (α := a.ToType) (· < ·) (cast (VStar_limit Q ha) X).1)
      (cast (VStar_limit Q ha) X).2 := by
  conv_lhs => unfold view
  rw [Ordinal.limitRecOn_limit _ _ _ _ ha]
  rfl

/-- The view of a position. -/
noncomputable def vw (X : Pos Q) : Q ⊕ Set (Pos Q) := view X.1 X.2

/-- The game relation on positions. -/
def gle (le : Q → Q → Prop) (X Y : Pos Q) : Prop := leStar le X.1 X.2 Y.1 Y.2

/-- One round of the game, in terms of the views. -/
def step (le : Q → Q → Prop) (X Y : Pos Q) : Q ⊕ Set (Pos Q) → Q ⊕ Set (Pos Q) → Prop
  | Sum.inl p, Sum.inl q => le p q
  | Sum.inl _, Sum.inr B => ∃ y ∈ B, gle le X y
  | Sum.inr A, Sum.inl _ => ∀ x ∈ A, gle le x Y
  | Sum.inr A, Sum.inr B => ∀ x ∈ A, ∃ y ∈ B, gle le x y

/-- Every position has the same view and the same game as one of level `0` or successor level. -/
theorem exists_base (le : Q → Q → Prop) (a : Ordinal.{u}) : ∀ X : VStar Q a,
    ∃ X' : Pos Q, X'.1 ≤ a ∧ (X'.1 = 0 ∨ ∃ α, X'.1 = Order.succ α) ∧ vw X' = view a X ∧
      (∀ b Y, leStar le a X b Y ↔ leStar le X'.1 X'.2 b Y) ∧
      (∀ Z : Pos Q, gle le Z ⟨a, X⟩ ↔ gle le Z X') := by
  have right : ∀ {a : Ordinal.{u}} (ha : Order.IsSuccLimit a) (X : VStar Q a) (c : Ordinal.{u})
      (Z : VStar Q c), leStar le c Z a X ↔
        leStar le c Z (Ordinal.typein (α := a.ToType) (· < ·) (cast (VStar_limit Q ha) X).1)
          (cast (VStar_limit Q ha) X).2 := by
    intro a ha X c
    induction c using Ordinal.limitRecOn with
    | zero => intro Z; exact leStar_zero_limit le Z ha X
    | add_one γ _ => intro Z; exact leStar_succ_limit le γ Z ha X
    | limit γ hγ ih =>
      intro Z
      rw [leStar_limit_left le hγ, leStar_limit_left le hγ]
      exact ih _ (Ordinal.typein_lt_self _) _
  induction a using Ordinal.limitRecOn with
  | zero => intro X; exact ⟨⟨0, X⟩, le_rfl, Or.inl rfl, rfl, fun _ _ => Iff.rfl, fun _ => Iff.rfl⟩
  | add_one α _ =>
    intro X
    exact ⟨⟨Order.succ α, X⟩, le_rfl, Or.inr ⟨α, rfl⟩, rfl, fun _ _ => Iff.rfl, fun _ => Iff.rfl⟩
  | limit a ha ih =>
    intro X
    obtain ⟨X', h1, h2, h3, h4, h5⟩ := ih _ (Ordinal.typein_lt_self _) (cast (VStar_limit Q ha) X).2
    refine ⟨X', h1.trans (Ordinal.typein_lt_self _).le, h2, h3.trans (view_limit ha X).symm, ?_, ?_⟩
    · intro b Y; exact (leStar_limit_left le ha X b Y).trans (h4 b Y)
    · intro Z; exact (right ha X Z.1 Z.2).trans (h5 Z)

theorem step_base (le : Q → Q → Prop) (X Y : Pos Q)
    (hX : X.1 = 0 ∨ ∃ α, X.1 = Order.succ α) (hY : Y.1 = 0 ∨ ∃ α, Y.1 = Order.succ α) :
    gle le X Y ↔ step le X Y (vw X) (vw Y) := by
  obtain ⟨a, X⟩ := X
  obtain ⟨b, Y⟩ := Y
  rcases hX with hX | ⟨α, hX⟩ <;> rcases hY with hY | ⟨β, hY⟩ <;> dsimp only at hX hY <;> subst hX <;> subst hY
  · simp only [vw, view_zero, step]; exact leStar_zero_zero le X Y
  · simp only [vw, view_zero, view_succ, step, Set.exists_mem_image]
    exact leStar_zero_succ le X β Y
  · simp only [vw, view_zero, view_succ, step, Set.forall_mem_image]
    exact leStar_succ_zero le α X Y
  · simp only [vw, view_succ, step, Set.forall_mem_image, Set.exists_mem_image]
    exact leStar_succ_succ le α X β Y

theorem gle_iff (le : Q → Q → Prop) (X Y : Pos Q) :
    gle le X Y ↔ step le X Y (vw X) (vw Y) := by
  obtain ⟨X', _, hX, vX, lX, rX⟩ := exists_base le X.1 X.2
  obtain ⟨Y', _, hY, vY, lY, rY⟩ := exists_base le Y.1 Y.2
  have key : ∀ Z, gle le X Z ↔ gle le X' Z := fun Z => lX Z.1 Z.2
  rw [key, rY X', step_base le X' Y' hX hY, vX, vY]
  change step le X' Y' (vw X) (vw Y) ↔ _
  rcases vw X with p | A <;> rcases vw Y with q | B <;> simp only [step]
  · simp only [key]
  · exact forall₂_congr fun x _ => (rY x).symm

/-- Members of a position have smaller level. -/
theorem mem_lt {X : Pos Q} {A : Set (Pos Q)} (h : vw X = Sum.inr A) :
    A.Nonempty ∧ ∀ x ∈ A, x.1 < X.1 := by
  obtain ⟨X', hle, hX, vX, _, _⟩ := exists_base (fun _ _ => True) X.1 X.2
  have h' : vw X' = Sum.inr A := vX.trans h
  obtain ⟨a, X'⟩ := X'
  rcases hX with hX | ⟨α, hX⟩ <;> dsimp only at hX <;> subst hX
  · simp [vw, view_zero] at h'
  · simp only [vw, view_succ, Sum.inr.injEq] at h'
    subst h'
    refine ⟨(cast (VStar_succ Q α) X').2.image _, ?_⟩
    rintro _ ⟨x, _, rfl⟩
    exact (Order.lt_succ α).trans_le hle

/-- Raising a position to a limit level. -/
theorem exists_tag {o : Ordinal.{u}} (ho : Order.IsSuccLimit o) (Z : Pos Q) (h : Z.1 < o) :
    ∃ Z' : VStar Q o, view o Z' = vw Z := by
  obtain ⟨b, Z⟩ := Z
  have hb : b < Ordinal.type (α := o.ToType) (· < ·) := by simpa using h
  obtain ⟨i, rfl⟩ := Ordinal.typein_surj (α := o.ToType) (· < ·) hb
  refine ⟨cast (VStar_limit Q ho).symm ⟨i, Z⟩, ?_⟩
  rw [view_limit ho]
  have : cast (VStar_limit Q ho) (cast (VStar_limit Q ho).symm ⟨i, Z⟩) = ⟨i, Z⟩ := by simp
  rw [this]
  rfl

end View

/-! ### Countable realisations -/

theorem isSuccLimit_omega_one : Order.IsSuccLimit (ω_ 1 : Ordinal.{u}) := by
  rw [← Cardinal.ord_aleph]
  exact Cardinal.isSuccLimit_ord (Cardinal.aleph0_le_aleph 1)

theorem add_omega_lt {a : Ordinal.{u}} (h : a < ω_ 1) : a + ω < ω_ 1 := by
  rw [← Cardinal.ord_aleph, Cardinal.lt_ord] at h ⊢
  rw [Ordinal.card_add, Ordinal.card_omega0]
  exact Cardinal.add_lt_of_lt (Cardinal.aleph0_le_aleph 1) h Cardinal.aleph0_lt_aleph_one

section Realise
variable {Q : Type u}

/-- `Real D X Z`: `Z` is a copy of `X` in which only the members lying in `D` are kept. -/
inductive Real (D : Set (Pos Q)) : Pos Q → Pos Q → Prop
  | leaf {X Z : Pos Q} (p : Q) : vw X = Sum.inl p → vw Z = Sum.inl p → Real D X Z
  | node {X Z : Pos Q} (A B : Set (Pos Q)) : vw X = Sum.inr A → vw Z = Sum.inr B →
      (u v : Pos Q → Pos Q) →
      (∀ x ∈ A, x ∈ D → u x ∈ B) → (∀ x ∈ A, x ∈ D → Real D x (u x)) →
      (∀ z ∈ B, v z ∈ A) → (∀ z ∈ B, v z ∈ D) → (∀ z ∈ B, Real D (v z) z) → Real D X Z

theorem Real.mk' {D : Set (Pos Q)} {X Z : Pos Q} (A B : Set (Pos Q)) (hX : vw X = Sum.inr A)
    (hZ : vw Z = Sum.inr B) (h₁ : ∀ x ∈ A, x ∈ D → ∃ z ∈ B, Real D x z)
    (h₂ : ∀ z ∈ B, ∃ x ∈ A, x ∈ D ∧ Real D x z) : Real D X Z := by
  classical
  have h₁' : ∀ x, ∃ z, x ∈ A → x ∈ D → z ∈ B ∧ Real D x z := fun x => by
    by_cases h : x ∈ A ∧ x ∈ D
    · obtain ⟨z, hz⟩ := h₁ x h.1 h.2; exact ⟨z, fun _ _ => hz⟩
    · exact ⟨x, fun a b => absurd ⟨a, b⟩ h⟩
  have h₂' : ∀ z, ∃ x, z ∈ B → x ∈ A ∧ x ∈ D ∧ Real D x z := fun z => by
    by_cases h : z ∈ B
    · obtain ⟨x, hx⟩ := h₂ z h; exact ⟨x, fun _ => hx⟩
    · exact ⟨z, fun a => absurd a h⟩
  choose u hu using h₁'
  choose v hv using h₂'
  exact .node A B hX hZ u v (fun x a b => (hu x a b).1) (fun x a b => (hu x a b).2)
    (fun z a => (hv z a).1) (fun z a => (hv z a).2.1) (fun z a => (hv z a).2.2)

theorem Real.congr {D : Set (Pos Q)} {X Z Z' : Pos Q} (h : Real D X Z) (e : vw Z' = vw Z) :
    Real D X Z' := by
  cases h with
  | leaf p h1 h2 => exact .leaf p h1 (e.trans h2)
  | node A B h1 h2 u v a b c d f => exact .node A B h1 (e.trans h2) u v a b c d f

/-- If every set in `D` meets `D` and `D` is countable, elements of `D` are realised below `ω₁`. -/
theorem exists_real {D : Set (Pos Q)} (hD : D.Countable)
    (hne : ∀ X ∈ D, ∀ A, vw X = Sum.inr A → (A ∩ D).Nonempty) :
    ∀ (a : Ordinal.{u}) (X : Pos Q), X.1 = a → X ∈ D →
      ∃ Z : Pos Q, Z.1 < ω_ 1 ∧ Real D X Z := by
  intro a
  induction a using WellFoundedLT.induction with
  | ind a ih =>
  rintro X rfl hX
  cases hv : vw X with
  | inl p =>
    refine ⟨⟨0, cast (VStar_zero Q).symm p⟩, Ordinal.omega_pos 1, .leaf p hv ?_⟩
    simp [vw, view_zero]
  | inr A =>
    obtain ⟨g, hg⟩ := (hD.mono Set.inter_subset_right).exists_eq_range (hne X hX A hv)
    have hgm : ∀ n, g n ∈ A ∩ D := fun n => hg ▸ Set.mem_range_self n
    choose z hz1 hz2 using fun n => ih _ ((mem_lt hv).2 _ (hgm n).1) (g n) rfl (hgm n).2
    have hsup : (⨆ n, (z n).1) < ω_ 1 := Ordinal.iSup_lt_omega_one hz1
    let o : Ordinal.{u} := (⨆ n, (z n).1) + ω
    have ho : Order.IsSuccLimit o := Ordinal.isSuccLimit_add _ Ordinal.isSuccLimit_omega0
    have holt : o < ω_ 1 := add_omega_lt hsup
    have hzo : ∀ n, (z n).1 < o := fun n =>
      (le_ciSup (Ordinal.bddAbove_range _) n).trans_lt
        (lt_add_of_pos_right _ Ordinal.omega0_pos)
    choose t ht using fun n => exists_tag ho (z n) (hzo n)
    have hr : ∀ n, Real D (g n) ⟨o, t n⟩ := fun n => (hz2 n).congr (ht n)
    refine ⟨⟨Order.succ o, cast (VStar_succ Q o).symm ⟨Set.range t, Set.range_nonempty t⟩⟩,
      isSuccLimit_omega_one.succ_lt holt,
      .mk' A (Set.range fun n => (⟨o, t n⟩ : Pos Q)) hv ?_ ?_ ?_⟩
    · simp only [vw, view_succ, cast_cast, cast_eq, ← Set.range_comp]
      rfl
    · intro x hxA hxD
      obtain ⟨n, rfl⟩ : x ∈ Set.range g := hg ▸ ⟨hxA, hxD⟩
      exact ⟨_, ⟨n, rfl⟩, hr n⟩
    · rintro _ ⟨n, rfl⟩
      exact ⟨g n, (hgm n).1, (hgm n).2, hr n⟩

/-- Player I's strategy survives in the realisations. -/
theorem real_not_gle (le : Q → Q → Prop) {D : Set (Pos Q)}
    (hw : ∀ X ∈ D, ∀ Y ∈ D, ¬ gle le X Y → ∀ A, vw X = Sum.inr A →
      ∃ x ∈ A, x ∈ D ∧ (∀ q, vw Y = Sum.inl q → ¬ gle le x Y) ∧
        (∀ B, vw Y = Sum.inr B → ∀ y ∈ B, ¬ gle le x y)) :
    ∀ (a b : Ordinal.{u}) (X Y Z W : Pos Q), X.1 = a → Y.1 = b → X ∈ D → Y ∈ D →
      Real D X Z → Real D Y W → ¬ gle le X Y → ¬ gle le Z W := by
  intro a
  induction a using WellFoundedLT.induction with
  | ind a iha =>
  intro b
  induction b using WellFoundedLT.induction with
  | ind b ihb =>
  rintro X Y Z W rfl rfl hX hY hZ hW hn h
  rw [gle_iff] at h
  have hn' := hn
  rw [gle_iff] at hn'
  cases hZ with
  | leaf p x1 z1 =>
    have hZ : Real D X Z := .leaf p x1 z1
    cases hW with
    | leaf q y1 w1 =>
      rw [x1, y1] at hn'; rw [z1, w1] at h; exact hn' h
    | node A B y1 w1 u v _ _ c d f =>
      rw [x1, y1] at hn'; rw [z1, w1] at h
      obtain ⟨w, hwB, h⟩ := h
      have hyA := c w hwB
      have hyD := d w hwB
      have hr := f w hwB
      exact ihb _ ((mem_lt y1).2 _ hyA) X (v w) Z w rfl rfl hX hyD hZ hr
        (fun hh => hn' ⟨_, hyA, hh⟩) h
  | node A B x1 z1 u v l1 l2 _ _ _ =>
    obtain ⟨x, hxA, hxD, w1', w2'⟩ := hw X hX Y hY hn A x1
    have hzB := l1 x hxA hxD
    have hr := l2 x hxA hxD
    have hlt := (mem_lt x1).2 x hxA
    cases hW with
    | leaf q y1 w1 =>
      rw [z1, w1] at h
      exact iha _ hlt _ x Y (u x) W rfl rfl hxD hY hr (.leaf q y1 w1) (w1' q y1) (h _ hzB)
    | node A' B' y1 w1 u' v' _ _ c d f =>
      rw [z1, w1] at h
      obtain ⟨w, hwB, h⟩ := h _ hzB
      have hyA := c w hwB
      have hyD := d w hwB
      have hr' := f w hwB
      exact iha _ hlt _ x (v' w) (u x) w rfl rfl hxD hyD hr hr' (w2' A' y1 _ hyA) h

/-- A single function choosing Player I's answers. -/
theorem exists_strategy (le : Q → Q → Prop) : ∃ w : Pos Q → Pos Q → Pos Q,
    ∀ X Y A, vw X = Sum.inr A → w X Y ∈ A ∧ (¬ gle le X Y →
      (∀ q, vw Y = Sum.inl q → ¬ gle le (w X Y) Y) ∧
        (∀ B, vw Y = Sum.inr B → ∀ y ∈ B, ¬ gle le (w X Y) y)) := by
  have : ∀ X Y : Pos Q, ∃ x : Pos Q, ∀ A, vw X = Sum.inr A → x ∈ A ∧ (¬ gle le X Y →
      (∀ q, vw Y = Sum.inl q → ¬ gle le x Y) ∧
        (∀ B, vw Y = Sum.inr B → ∀ y ∈ B, ¬ gle le x y)) := by
    intro X Y
    cases hX : vw X with
    | inl p => exact ⟨X, fun A h => by cases h⟩
    | inr A =>
      by_cases hn : gle le X Y
      · obtain ⟨x, hx⟩ := (mem_lt hX).1
        exact ⟨x, fun A' h => by cases h; exact ⟨hx, fun h => absurd hn h⟩⟩
      · have hn' := hn
        rw [gle_iff, hX] at hn'
        cases hY : vw Y with
        | inl q =>
          rw [hY] at hn'
          simp only [step, not_forall] at hn'
          obtain ⟨x, hx, hxY⟩ := hn'
          exact ⟨x, fun A' h => by
            cases h; exact ⟨hx, fun _ => ⟨fun _ _ => hxY, fun B h => by cases h⟩⟩⟩
        | inr B =>
          rw [hY] at hn'
          simp only [step, not_forall, not_exists, not_and] at hn'
          obtain ⟨x, hx, hxY⟩ := hn'
          exact ⟨x, fun A' h => by
            cases h
            exact ⟨hx, fun _ => ⟨fun q h => (by cases h), fun B' h => (by cases h; exact hxY)⟩⟩⟩
  choose w hw using this
  exact ⟨w, hw⟩

/-- A countable set generates a countable set closed under a binary operation. -/
theorem exists_countable_closed {P : Type*} (w : P → P → P) (S : Set P) (hS : S.Countable) :
    ∃ D : Set P, S ⊆ D ∧ D.Countable ∧ ∀ x ∈ D, ∀ y ∈ D, w x y ∈ D := by
  let E : ℕ → Set P := fun n => Nat.rec S (fun _ T => T ∪ Set.image2 w T T) n
  have hsucc : ∀ n, E (n + 1) = E n ∪ Set.image2 w (E n) (E n) := fun _ => rfl
  have hmono : Monotone E := monotone_nat_of_le_succ fun n => by
    rw [hsucc]; exact Set.subset_union_left
  refine ⟨⋃ n, E n, Set.subset_iUnion E 0, Set.countable_iUnion fun n => ?_, ?_⟩
  · induction n with
    | zero => exact hS
    | succ n ih => rw [hsucc]; exact ih.union (ih.image2 ih w)
  · intro x hx y hy
    obtain ⟨m, hm⟩ := Set.mem_iUnion.1 hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hy
    refine Set.mem_iUnion.2 ⟨max m n + 1, ?_⟩
    rw [hsucc]
    exact Or.inr ⟨x, hmono (le_max_left m n) hm, y, hmono (le_max_right m n) hn, rfl⟩

end Realise

end TenChallenges.OmegaOne

open TenChallenges.OmegaOne in
theorem solution {Q : Type u} (le : Q → Q → Prop) (α : Ordinal.{u}) :
    IsAlphaWQO le (ω_ 1) → IsAlphaWQO le α := by
  intro h f
  by_contra hbad
  push Not at hbad
  obtain ⟨w, hw⟩ := exists_strategy le
  obtain ⟨D, hfD, hD, hcl⟩ := exists_countable_closed w
    (Set.range fun n => (⟨α, f n⟩ : Pos Q)) (Set.countable_range _)
  have hfn : ∀ n, (⟨α, f n⟩ : Pos Q) ∈ D := fun n => hfD ⟨n, rfl⟩
  choose Z hZ1 hZ2 using fun n => exists_real hD
    (fun X hX A hA => ⟨w X X, (hw X X A hA).1, hcl X hX X hX⟩) _ _ rfl (hfn n)
  choose t ht using fun n => exists_tag isSuccLimit_omega_one (Z n) (hZ1 n)
  obtain ⟨i, j, hij, hle⟩ := h t
  refine real_not_gle le (D := D) ?_ _ _ _ _ ⟨ω_ 1, t i⟩ ⟨ω_ 1, t j⟩ rfl rfl (hfn i) (hfn j)
    ((hZ2 i).congr (ht i)) ((hZ2 j).congr (ht j)) (hbad i j hij) hle
  intro X hX Y hY hn A hA
  exact ⟨w X Y, (hw X Y A hA).1, hcl X hX Y hY, (hw X Y A hA).2 hn⟩
