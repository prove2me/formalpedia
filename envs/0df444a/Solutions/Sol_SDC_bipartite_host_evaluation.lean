-- Prove2me | solution 1 for SDC.bipartite_host_evaluation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T09:52:45.763357+00:00
-- url     : https://prove2.me/submissions/5fe802ab-e6d2-43b6-a476-093e92da28c6

import Mathlib
import Definitions.Def_SDC_graphs
import Definitions.Def_SDC_density
open SDC

theorem sdc89_card_pattern : Nat.card PatternVertex = 35 := by
  simp

theorem sdc89_wi {W : Type*} [Fintype W] [Nonempty W] (G : SimpleGraph W) :
    homDensity H G < (edgeDensity G) ^ 66 ↔
      homCount H G * (Fintype.card W) ^ 132 <
        (2 * edgeCard G) ^ 66 * (Fintype.card W) ^ 35 := by
  unfold homDensity edgeDensity
  rw [sdc89_card_pattern, Nat.card_eq_fintype_card]
  have hm : (0 : ℝ) < (Fintype.card W : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [div_pow, ← pow_mul, div_lt_div_iff₀ (by positivity) (by positivity)]
  norm_num
  constructor <;> intro h <;> exact_mod_cast h
theorem sdc89_hom_bip {α β W : Type*} [Fintype α] [DecidableEq α] [Fintype β] [Fintype W]
    (F : SimpleGraph (α ⊕ β)) (R : α → β → Prop)
    (h1 : ∀ a b, F.Adj (Sum.inl a) (Sum.inr b) ↔ R a b)
    (h2 : ∀ a a', ¬ F.Adj (Sum.inl a) (Sum.inl a'))
    (h3 : ∀ b b', ¬ F.Adj (Sum.inr b) (Sum.inr b')) (G : SimpleGraph W) :
    homCount F G = ∑ φ : α → W, ∏ b : β,
      (⋂ a, ⋂ (_ : R a b), G.neighborSet (φ a)).ncard := by
  classical
  let e : {hom : α ⊕ β → W // ∀ l r, F.Adj l r → G.Adj (hom l) (hom r)} ≃
      Σ φ : α → W, ∀ b : β, ↥(⋂ a, ⋂ (_ : R a b), G.neighborSet (φ a)) :=
    { toFun := fun h => ⟨h.1 ∘ Sum.inl, fun b => ⟨h.1 (Sum.inr b), by
          simp only [Set.mem_iInter, SimpleGraph.mem_neighborSet, Function.comp]
          intro a hab
          exact h.2 _ _ ((h1 a b).2 hab)⟩⟩
      invFun := fun x => ⟨Sum.elim x.1 (fun b => (x.2 b).1), by
          intro l r hlr
          rcases l with a | b <;> rcases r with a' | b'
          · exact absurd hlr (h2 a a')
          · have hm := (x.2 b').2
            simp only [Set.mem_iInter, SimpleGraph.mem_neighborSet] at hm
            exact hm a ((h1 a b').1 hlr)
          · have hm := (x.2 b).2
            simp only [Set.mem_iInter, SimpleGraph.mem_neighborSet] at hm
            exact (hm a' ((h1 a' b).1 hlr.symm)).symm
          · exact absurd hlr (h3 b b')⟩
      left_inv := fun h => by
        apply Subtype.ext; funext x; rcases x with a | b <;> rfl
      right_inv := fun x => rfl }
  unfold homCount
  rw [Nat.card_congr e, Nat.card_sigma]
  refine Finset.sum_congr rfl fun φ _ => ?_
  rw [Nat.card_pi]
  refine Finset.prod_congr rfl fun b _ => ?_
  exact Nat.card_coe_set_eq _

theorem sdc89_cb_eq (a b : ℕ) : completeBipartite a b = completeBipartiteGraph (Fin a) (Fin b) := by
  ext x y; cases x <;> cases y <;> simp [completeBipartite, cbAdj]

theorem sdc89_cb_adj (a b : ℕ) (x y : Fin a ⊕ Fin b) :
    (completeBipartite a b).Adj x y ↔ x.isLeft ≠ y.isLeft := by
  cases x <;> cases y <;> simp [completeBipartite, cbAdj]

theorem sdc89_cb_edgeCard (a b : ℕ) : edgeCard (completeBipartite a b) = a * b := by
  unfold edgeCard
  rw [sdc89_cb_eq, Nat.card_coe_set_eq, Set.ncard_def, SimpleGraph.encard_edgeSet_completeBipartiteGraph]
  simp

theorem sdc89_split {α β γ δ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [Fintype δ] :
    Nat.card {h : α ⊕ β → γ ⊕ δ // (∀ x, (h (Sum.inl x)).isLeft) ∧ ∀ y, (h (Sum.inr y)).isRight}
      = Fintype.card γ ^ Fintype.card α * Fintype.card δ ^ Fintype.card β := by
  let e : {h : α ⊕ β → γ ⊕ δ // (∀ x, (h (Sum.inl x)).isLeft) ∧ ∀ y, (h (Sum.inr y)).isRight}
      ≃ (α → γ) × (β → δ) :=
    { toFun := fun h => (fun x => (h.1 (Sum.inl x)).getLeft (h.2.1 x),
        fun y => (h.1 (Sum.inr y)).getRight (h.2.2 y))
      invFun := fun g => ⟨Sum.elim (Sum.inl ∘ g.1) (Sum.inr ∘ g.2), by simp⟩
      left_inv := fun h => by
        apply Subtype.ext; funext z
        rcases z with x | y
        · simp
        · simp
      right_inv := fun g => by simp }
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_fun, Nat.card_fun]
  simp [Nat.card_eq_fintype_card]

theorem sdc89_conn (s : Fin 13 → Bool) (t : Fin 22 → Bool)
    (h : ∀ f, ∀ p ∈ faces f, s p ≠ t f) :
    ((∀ p, s p = true) ∧ ∀ f, t f = false) ∨ ((∀ p, s p = false) ∧ ∀ f, t f = true) := by
  have E : ∀ f p q, p ∈ faces f → q ∈ faces f → s p = s q := by
    intro f p q hp hq
    have h1 := h f p hp; have h2 := h f q hq
    revert h1 h2; cases s p <;> cases s q <;> cases t f <;> simp
  have c : ∀ p, s p = s 0 := by
    have e1 : s 1 = s 0 := E 0 1 0 (by decide) (by decide)
    have e2 : s 2 = s 0 := E 2 2 0 (by decide) (by decide)
    have e3 : s 3 = s 0 := E 0 3 0 (by decide) (by decide)
    have e9 : s 9 = s 0 := E 1 9 0 (by decide) (by decide)
    have e4 : s 4 = s 0 := (E 8 4 2 (by decide) (by decide)).trans e2
    have e10 : s 10 = s 0 := (E 4 10 1 (by decide) (by decide)).trans e1
    have e7 : s 7 = s 0 := (E 5 7 1 (by decide) (by decide)).trans e1
    have e12 : s 12 = s 0 := (E 6 12 1 (by decide) (by decide)).trans e1
    have e11 : s 11 = s 0 := (E 10 11 3 (by decide) (by decide)).trans e3
    have e8 : s 8 = s 0 := (E 12 8 4 (by decide) (by decide)).trans e4
    have e5 : s 5 = s 0 := (E 14 5 7 (by decide) (by decide)).trans e7
    have e6 : s 6 = s 0 := (E 14 6 7 (by decide) (by decide)).trans e7
    intro p; fin_cases p <;> first | rfl | assumption
  have ne : ∀ f : Fin 22, ∃ p, p ∈ faces f := by decide
  have ct : ∀ f, t f = !s 0 := by
    intro f
    obtain ⟨p, hp⟩ := ne f
    have := h f p hp
    rw [c p] at this
    revert this; cases s 0 <;> cases t f <;> simp
  cases h0 : s 0
  · right; exact ⟨fun p => (c p).trans h0, fun f => by rw [ct f, h0]; rfl⟩
  · left; exact ⟨fun p => (c p).trans h0, fun f => by rw [ct f, h0]; rfl⟩

theorem sdc89_cb_homCount (a b : ℕ) :
    homCount H (completeBipartite a b) = a ^ 13 * b ^ 22 + b ^ 13 * a ^ 22 := by
  classical
  let P1 : (PatternVertex → Fin a ⊕ Fin b) → Prop := fun h =>
    (∀ x, (h (Sum.inl x)).isLeft) ∧ ∀ y, (h (Sum.inr y)).isRight
  let P2 : (PatternVertex → Fin a ⊕ Fin b) → Prop := fun h =>
    (∀ x, (h (Sum.inl x)).isRight) ∧ ∀ y, (h (Sum.inr y)).isLeft
  have hiff : ∀ h : PatternVertex → Fin a ⊕ Fin b,
      (∀ l r, H.Adj l r → (completeBipartite a b).Adj (h l) (h r)) ↔ P1 h ∨ P2 h := by
    intro h
    constructor
    · intro hh
      have := sdc89_conn (fun p => (h (Sum.inl p)).isLeft) (fun f => (h (Sum.inr f)).isLeft)
        (fun f p hp => (sdc89_cb_adj a b _ _).1 (hh (Sum.inl p) (Sum.inr f) hp))
      rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; exact ⟨h1, fun y => by simpa using h2 y⟩
      · right; exact ⟨fun x => by simpa using h1 x, h2⟩
    · have aux : ∀ x y : Fin a ⊕ Fin b, x.isLeft → y.isRight → x.isLeft ≠ y.isLeft := by
        intro x y; cases x <;> cases y <;> simp
      rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) l r hlr <;> rw [sdc89_cb_adj] <;>
        rcases l with p | f <;> rcases r with q | g
      · exact hlr.elim
      · exact aux _ _ (h1 p) (h2 g)
      · exact (aux _ _ (h1 q) (h2 f)).symm
      · exact hlr.elim
      · exact hlr.elim
      · exact (aux _ _ (h2 g) (h1 p)).symm
      · exact aux _ _ (h2 f) (h1 q)
      · exact hlr.elim
  have hdisj : ∀ h, ¬ (P1 h ∧ P2 h) := by
    rintro h ⟨⟨h1, -⟩, ⟨h2, -⟩⟩
    have a1 := h1 0; have a2 := h2 0
    revert a1 a2; cases h (Sum.inl 0) <;> simp
  unfold homCount
  rw [Nat.card_congr (Equiv.subtypeEquivRight hiff),
    Nat.card_congr (subtypeOrEquiv P1 P2 (fun r ha hb x hx => (hdisj x ⟨ha x hx, hb x hx⟩).elim)),
    Nat.card_sum]
  have c1 : Nat.card {h // P1 h} = a ^ 13 * b ^ 22 := by
    rw [sdc89_split]; simp
  have c2 : Nat.card {h // P2 h} = b ^ 13 * a ^ 22 := by
    rw [Nat.card_congr (Equiv.subtypeEquiv (p := P2)
      (q := fun h : PatternVertex → Fin b ⊕ Fin a =>
        (∀ x, (h (Sum.inl x)).isLeft) ∧ ∀ y, (h (Sum.inr y)).isRight)
      (Equiv.arrowCongr (Equiv.refl _) (Equiv.sumComm _ _)) (fun h => by simp [P2])),
      sdc89_split]
    simp
  rw [c1, c2]

theorem solution (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    edgeDensity (completeBipartite a b) =
      2 * (a : ℝ) * (b : ℝ) / ((a : ℝ) + (b : ℝ)) ^ 2 ∧
    homDensity H (completeBipartite a b) =
      ((a : ℝ) ^ 13 * (b : ℝ) ^ 22 + (b : ℝ) ^ 13 * (a : ℝ) ^ 22)
        / ((a : ℝ) + (b : ℝ)) ^ 35 := by
  constructor
  · unfold edgeDensity
    rw [sdc89_cb_edgeCard]
    simp [Nat.card_sum, mul_assoc]
  · unfold homDensity
    rw [sdc89_cb_homCount, sdc89_card_pattern]
    simp [Nat.card_sum]
