-- Prove2me | solution 1 for TradingNetFlow.ChainStable.contraction_mNaturalConcave
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T11:07:27.928796+00:00
-- url     : https://prove2.me/submissions/46b5f72c-810c-4c5f-83e7-ed9cfeaa1138

import Mathlib
import Definitions.Def_TradingNetFlow_ChainStable_Model

open Finset TradingNetFlow.ChainStable DiscreteConvex.EconomicEquilibrium
  DiscreteConvex.MConvexFunctions

namespace TNFContr

/-! ### Generic operations preserving M♮-concavity -/

lemma sup_add_const {ι : Type*} (s : Finset ι) (B : ι → WithBot ℝ) (C : ℝ) :
    s.sup (fun j => B j + (C : WithBot ℝ)) = s.sup B + (C : WithBot ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sup_insert, sup_insert, ih]
    exact (max_add_add_right _ _ _)

lemma lin_pair {K : Type*} [Fintype K] (d : K → ℝ) (a b x y : K → ℤ)
    (h : ∀ k, a k + b k = x k + y k) :
    (∑ k, d k * (a k : ℝ)) + (∑ k, d k * (b k : ℝ))
      = (∑ k, d k * (x k : ℝ)) + (∑ k, d k * (y k : ℝ)) := by
  rw [← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl (fun k _ => ?_)
  have := h k
  have : (a k : ℝ) + b k = x k + y k := by exact_mod_cast this
  linear_combination d k * this

/-- Adding a linear function preserves M♮-concavity. -/
lemma mnat_add_linear {K : Type*} [Fintype K] [DecidableEq K] (U : (K → ℤ) → WithBot ℝ)
    (d : K → ℝ) (hU : MNaturalConcave U) :
    MNaturalConcave (fun x => U x + ((∑ k, d k * (x k : ℝ) : ℝ) : WithBot ℝ)) := by
  set ℓ : (K → ℤ) → ℝ := fun x => ∑ k, d k * (x k : ℝ) with hℓ
  have hdom : ∀ x, x ∈ UDom (fun x => U x + ((ℓ x : ℝ) : WithBot ℝ)) ↔ x ∈ UDom U := by
    intro x
    simp [UDom, WithBot.add_eq_bot]
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hx⟩ := hU.1
    exact ⟨x, (hdom x).2 hx⟩
  intro x hx y hy i hi
  have hx' := (hdom x).1 hx
  have hy' := (hdom y).1 hy
  have key := hU.2 x hx' y hy' i hi
  set L := ℓ x + ℓ y with hL
  have h1 : ℓ (fun w => x w - CharVec i w) + ℓ (fun w => y w + CharVec i w) = L :=
    lin_pair d _ _ x y (fun k => by ring)
  have h2 : ∀ j, ℓ (fun w => x w - CharVec i w + CharVec j w)
      + ℓ (fun w => y w + CharVec i w - CharVec j w) = L :=
    fun j => lin_pair d _ _ x y (fun k => by ring)
  have hre : ∀ (a b : WithBot ℝ) (ra rb : ℝ), ra + rb = L →
      a + (ra : WithBot ℝ) + (b + (rb : WithBot ℝ)) = a + b + (L : WithBot ℝ) := by
    intro a b ra rb h
    rw [← h, WithBot.coe_add, add_add_add_comm]
  show U x + (ℓ x : WithBot ℝ) + (U y + (ℓ y : WithBot ℝ)) ≤
    max (U (fun w => x w - CharVec i w) + (ℓ (fun w => x w - CharVec i w) : WithBot ℝ)
        + (U (fun w => y w + CharVec i w) + (ℓ (fun w => y w + CharVec i w) : WithBot ℝ)))
      ((SuppNeg x y).sup (fun j =>
        U (fun w => x w - CharVec i w + CharVec j w)
          + (ℓ (fun w => x w - CharVec i w + CharVec j w) : WithBot ℝ)
        + (U (fun w => y w + CharVec i w - CharVec j w)
          + (ℓ (fun w => y w + CharVec i w - CharVec j w) : WithBot ℝ))))
  rw [hre _ _ _ _ rfl, hre _ _ _ _ h1]
  simp_rw [hre _ _ _ _ (h2 _)]
  rw [sup_add_const, max_add_add_right]
  exact add_le_add key le_rfl

/-- Reindexing coordinates along an equivalence preserves M♮-concavity. -/
lemma mnat_reindex {K K' : Type*} [Fintype K] [DecidableEq K] [Fintype K'] [DecidableEq K']
    (σ : K ≃ K') (U : (K → ℤ) → WithBot ℝ) (hU : MNaturalConcave U) :
    MNaturalConcave (fun z : K' → ℤ => U (z ∘ σ)) := by
  have hch : ∀ (u' : K') (w : K), CharVec (σ.symm u') w = CharVec u' (σ w) := by
    intro u' w
    simp only [CharVec]
    congr 1
    exact propext ⟨fun h => by rw [h]; simp, fun h => by rw [← h]; simp⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hx⟩ := hU.1
    exact ⟨x ∘ σ.symm, by simpa [UDom, Function.comp_def] using hx⟩
  intro z1 hz1 z2 hz2 u hu
  have hu' : σ.symm u ∈ SuppPos (z1 ∘ σ) (z2 ∘ σ) := by
    simp only [SuppPos, mem_filter, mem_univ, true_and, Function.comp_apply,
      Equiv.apply_symm_apply] at hu ⊢
    exact hu
  have key := hU.2 (z1 ∘ σ) hz1 (z2 ∘ σ) hz2 (σ.symm u) hu'
  have e1 : (fun w => (z1 ∘ σ) w - CharVec (σ.symm u) w) = (fun w => z1 w - CharVec u w) ∘ σ := by
    funext w; simp [hch]
  have e2 : (fun w => (z2 ∘ σ) w + CharVec (σ.symm u) w) = (fun w => z2 w + CharVec u w) ∘ σ := by
    funext w; simp [hch]
  have e3 : ∀ v', (fun w => (z1 ∘ σ) w - CharVec (σ.symm u) w + CharVec (σ.symm v') w)
      = (fun w => z1 w - CharVec u w + CharVec v' w) ∘ σ := by
    intro v'; funext w; simp [hch]
  have e4 : ∀ v', (fun w => (z2 ∘ σ) w + CharVec (σ.symm u) w - CharVec (σ.symm v') w)
      = (fun w => z2 w + CharVec u w - CharVec v' w) ∘ σ := by
    intro v'; funext w; simp [hch]
  have hS : SuppNeg (z1 ∘ σ) (z2 ∘ σ) = (SuppNeg z1 z2).map σ.symm.toEmbedding := by
    ext w
    simp only [SuppNeg, mem_filter, mem_univ, true_and, mem_map, Equiv.coe_toEmbedding,
      Function.comp_apply]
    constructor
    · intro h; exact ⟨σ w, h, by simp⟩
    · rintro ⟨v', hv', rfl⟩; simpa using hv'
  rw [e1, e2, hS, Finset.sup_map] at key
  have hsup : ∀ F : (K → ℤ) → (K → ℤ) → WithBot ℝ,
      (SuppNeg z1 z2).sup ((fun j => F (fun w => (z1 ∘ σ) w - CharVec (σ.symm u) w + CharVec j w)
        (fun w => (z2 ∘ σ) w + CharVec (σ.symm u) w - CharVec j w)) ∘ σ.symm.toEmbedding)
      = (SuppNeg z1 z2).sup (fun v' => F ((fun w => z1 w - CharVec u w + CharVec v' w) ∘ σ)
          ((fun w => z2 w + CharVec u w - CharVec v' w) ∘ σ)) := by
    intro F
    congr 1
    funext v'
    exact congrArg₂ F (e3 v') (e4 v')
  rw [hsup (fun a b => U a + U b)] at key
  exact key

/-- Maximizing out some coordinates (a projection) preserves M♮-concavity. -/
lemma mnat_proj {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (g : (A ⊕ B → ℤ) → WithBot ℝ) (hg : MNaturalConcave g) (Ybox : Finset (B → ℤ))
    (hY : ∀ x y, g (Sum.elim x y) ≠ ⊥ → y ∈ Ybox) :
    MNaturalConcave (fun x => Ybox.sup (fun y => g (Sum.elim x y))) := by
  set gh : (A → ℤ) → WithBot ℝ := fun x => Ybox.sup (fun y => g (Sum.elim x y)) with hgh
  have hle : ∀ x y, g (Sum.elim x y) ≤ gh x := by
    intro x y
    by_cases h : g (Sum.elim x y) = ⊥
    · rw [h]; exact bot_le
    · exact le_sup (f := fun y => g (Sum.elim x y)) (hY x y h)
  have hatt : ∀ x, gh x ≠ ⊥ → ∃ y, g (Sum.elim x y) ≠ ⊥ ∧ gh x = g (Sum.elim x y) := by
    intro x hx
    have hne : Ybox.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      exact hx (by rw [hgh]; simp [h])
    obtain ⟨y, -, hy⟩ := Finset.exists_mem_eq_sup Ybox hne (fun y => g (Sum.elim x y))
    exact ⟨y, by rw [← hy]; exact hx, hy⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨z, hz⟩ := hg.1
    refine ⟨z ∘ Sum.inl, ?_⟩
    have := hle (z ∘ Sum.inl) (z ∘ Sum.inr)
    rw [Sum.elim_comp_inl_inr] at this
    exact ne_bot_of_le_ne_bot hz this
  intro x1 hx1 x2 hx2 u hu
  obtain ⟨y1, hy1, hx1e⟩ := hatt x1 hx1
  obtain ⟨y2, hy2, hx2e⟩ := hatt x2 hx2
  have hu' : (Sum.inl u : A ⊕ B) ∈ SuppPos (Sum.elim x1 y1) (Sum.elim x2 y2) := by
    simp only [SuppPos, mem_filter, mem_univ, true_and, Sum.elim_inl] at hu ⊢
    exact hu
  have key := hg.2 _ hy1 _ hy2 _ hu'
  show gh x1 + gh x2 ≤ max (gh (fun w => x1 w - CharVec u w) + gh (fun w => x2 w + CharVec u w))
    ((SuppNeg x1 x2).sup fun v =>
      gh (fun w => x1 w - CharVec u w + CharVec v w) + gh (fun w => x2 w + CharVec u w - CharVec v w))
  rw [hx1e, hx2e]
  refine key.trans (max_le ?_ (Finset.sup_le ?_))
  · refine le_max_of_le_left (add_le_add ?_ ?_)
    · have : (fun w => Sum.elim x1 y1 w - CharVec (Sum.inl u) w)
          = Sum.elim (fun w => x1 w - CharVec u w) y1 := by
        funext w; cases w <;> simp [CharVec]
      rw [this]; exact hle _ _
    · have : (fun w => Sum.elim x2 y2 w + CharVec (Sum.inl u) w)
          = Sum.elim (fun w => x2 w + CharVec u w) y2 := by
        funext w; cases w <;> simp [CharVec]
      rw [this]; exact hle _ _
  · intro w hw
    simp only [SuppNeg, mem_filter, mem_univ, true_and] at hw
    cases w with
    | inl v =>
      have hv : v ∈ SuppNeg x1 x2 := by
        simp only [SuppNeg, mem_filter, mem_univ, true_and]; simpa using hw
      refine le_max_of_le_right (le_trans ?_ (Finset.le_sup (f := fun v =>
        gh (fun w => x1 w - CharVec u w + CharVec v w)
          + gh (fun w => x2 w + CharVec u w - CharVec v w)) hv))
      refine add_le_add ?_ ?_
      · have : (fun w => Sum.elim x1 y1 w - CharVec (Sum.inl u) w + CharVec (Sum.inl v) w)
            = Sum.elim (fun w => x1 w - CharVec u w + CharVec v w) y1 := by
          funext w; cases w <;> simp [CharVec]
        rw [this]; exact hle _ _
      · have : (fun w => Sum.elim x2 y2 w + CharVec (Sum.inl u) w - CharVec (Sum.inl v) w)
            = Sum.elim (fun w => x2 w + CharVec u w - CharVec v w) y2 := by
          funext w; cases w <;> simp [CharVec]
        rw [this]; exact hle _ _
    | inr b =>
      refine le_max_of_le_left (add_le_add ?_ ?_)
      · have : (fun w => Sum.elim x1 y1 w - CharVec (Sum.inl u) w + CharVec (Sum.inr b) w)
            = Sum.elim (fun w => x1 w - CharVec u w) (fun w => y1 w + CharVec b w) := by
          funext w; cases w <;> simp [CharVec]
        rw [this]; exact hle _ _
      · have : (fun w => Sum.elim x2 y2 w + CharVec (Sum.inl u) w - CharVec (Sum.inr b) w)
            = Sum.elim (fun w => x2 w + CharVec u w) (fun w => y2 w - CharVec b w) := by
          funext w; cases w <;> simp [CharVec]
        rw [this]; exact hle _ _

section Econ
variable {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E] [DecidableEq E]

lemma mem_cdelta (G : Economy N E) (X : Finset E) (pX : E → ℝ) (i : N) (e' : {e // e ∉ X}) :
    e' ∈ (G.contraction X pX).delta i ↔ e'.1 ∈ G.delta i := by
  simp [Economy.delta, Economy.deltaOut, Economy.deltaIn, Economy.contraction]

/-- `δ(i) ≃ δ_{G^X}(i) ⊕ (X ∩ δ(i))`. -/
def splitEquiv (G : Economy N E) (X : Finset E) (pX : E → ℝ) (i : N) :
    {e // e ∈ G.delta i} ≃
      ({e' : {e // e ∉ X} // e' ∈ (G.contraction X pX).delta i} ⊕ {e // e ∈ X ∩ G.delta i}) where
  toFun k := if h : k.1 ∈ X then Sum.inr ⟨k.1, mem_inter.2 ⟨h, k.2⟩⟩
    else Sum.inl ⟨⟨k.1, h⟩, (mem_cdelta G X pX i _).2 k.2⟩
  invFun c := match c with
    | Sum.inl a => ⟨a.1.1, (mem_cdelta G X pX i a.1).1 a.2⟩
    | Sum.inr b => ⟨b.1, (mem_inter.1 b.2).2⟩
  left_inv k := by
    by_cases h : k.1 ∈ X
    · simp only [h, dite_true]
    · simp only [h, dite_false]
  right_inv c := by
    rcases c with a | b
    · simp only [a.1.2, dite_false]
    · simp only [(mem_inter.1 b.2).1, dite_true]

lemma splitEquiv_mem (G : Economy N E) (X : Finset E) (pX : E → ℝ) (i : N)
    (k : {e // e ∈ G.delta i}) (h : k.1 ∈ X) :
    splitEquiv G X pX i k = Sum.inr ⟨k.1, mem_inter.2 ⟨h, k.2⟩⟩ := by
  simp [splitEquiv, h]

lemma splitEquiv_not_mem (G : Economy N E) (X : Finset E) (pX : E → ℝ) (i : N)
    (k : {e // e ∈ G.delta i}) (h : k.1 ∉ X) :
    splitEquiv G X pX i k = Sum.inl ⟨⟨k.1, h⟩, (mem_cdelta G X pX i _).2 k.2⟩ := by
  simp [splitEquiv, h]

end Econ

section Econ2
variable {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E] [DecidableEq E]

lemma sign_cases (G : Economy N E) (i : N) (e : E) : G.sign i e = 1 ∨ G.sign i e = -1 := by
  unfold Economy.sign; split_ifs <;> simp

/-- The signed vector on `X ∩ δ(i)` of a set `Y`. -/
def yOf (G : Economy N E) (X : Finset E) (i : N) (Y : Finset E) :
    {e // e ∈ X ∩ G.delta i} → ℤ := fun b => if b.1 ∈ Y then G.sign i b.1 else 0

/-- The signed vector on `δ(i)` combining `x` (outside `X`) and `y` (inside `X`). -/
def zOf (G : Economy N E) (X : Finset E) (pX : E → ℝ) (i : N)
    (x : {e' : {e // e ∉ X} // e' ∈ (G.contraction X pX).delta i} → ℤ)
    (y : {e // e ∈ X ∩ G.delta i} → ℤ) : {e // e ∈ G.delta i} → ℤ :=
  fun k => Sum.elim x y (splitEquiv G X pX i k)

/-- The set of trades of `x`, as a set of trades of `G^X`. -/
def Sx (G : Economy N E) (X : Finset E) (pX : E → ℝ) (i : N)
    (x : {e' : {e // e ∉ X} // e' ∈ (G.contraction X pX).delta i} → ℤ) :
    Finset {e // e ∉ X} :=
  (univ.filter (fun a => x a ≠ 0)).map (Function.Embedding.subtype _)

lemma zOf_box (G : Economy N E) (X : Finset E) (pX : E → ℝ) (i : N)
    (x : {e' : {e // e ∉ X} // e' ∈ (G.contraction X pX).delta i} → ℤ)
    (hx : ∀ a, x a = 0 ∨ x a = G.sign i a.1.1) (Y : Finset E) :
    ∀ k, zOf G X pX i x (yOf G X i Y) k = 0 ∨ zOf G X pX i x (yOf G X i Y) k = G.sign i k.1 := by
  intro k
  unfold zOf
  by_cases h : k.1 ∈ X
  · rw [splitEquiv_mem G X pX i k h]
    simp only [Sum.elim_inr, yOf]
    split_ifs <;> simp
  · rw [splitEquiv_not_mem G X pX i k h]
    exact hx _

lemma zOf_set (G : Economy N E) (X : Finset E) (pX : E → ℝ) (i : N)
    (x : {e' : {e // e ∉ X} // e' ∈ (G.contraction X pX).delta i} → ℤ)
    (Y : Finset E) (hY : Y ⊆ X ∩ G.delta i) :
    (univ.filter (fun k => zOf G X pX i x (yOf G X i Y) k ≠ 0)).map (Function.Embedding.subtype _)
      = (Sx G X pX i x).map (Function.Embedding.subtype _) ∪ Y := by
  ext e
  simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype, mem_union,
    Sx]
  constructor
  · rintro ⟨k, hk, rfl⟩
    unfold zOf at hk
    by_cases h : k.1 ∈ X
    · rw [splitEquiv_mem G X pX i k h] at hk
      simp only [Sum.elim_inr, yOf] at hk
      right
      by_contra hn
      exact hk (if_neg hn)
    · rw [splitEquiv_not_mem G X pX i k h] at hk
      left
      exact ⟨⟨k.1, h⟩, ⟨⟨⟨k.1, h⟩, (mem_cdelta G X pX i _).2 k.2⟩, hk, rfl⟩, rfl⟩
  · rintro (⟨e', ⟨a, ha, rfl⟩, rfl⟩ | he)
    · refine ⟨⟨a.1.1, (mem_cdelta G X pX i a.1).1 a.2⟩, ?_, rfl⟩
      unfold zOf
      rw [splitEquiv_not_mem G X pX i _ a.1.2]
      exact ha
    · have hm := hY he
      refine ⟨⟨e, (mem_inter.1 hm).2⟩, ?_, rfl⟩
      unfold zOf
      rw [splitEquiv_mem G X pX i _ (mem_inter.1 hm).1]
      simp only [Sum.elim_inr, yOf]
      rw [if_pos he]
      rcases sign_cases G i e with h | h <;> rw [h] <;> simp

lemma zOf_lin (G : Economy N E) (hsb : ∀ e, G.seller e ≠ G.buyer e) (X : Finset E)
    (pX : E → ℝ) (i : N)
    (x : {e' : {e // e ∉ X} // e' ∈ (G.contraction X pX).delta i} → ℤ)
    (Y : Finset E) (hY : Y ⊆ X ∩ G.delta i) :
    ∑ k : {e // e ∈ G.delta i}, (if k.1 ∈ X then pX k.1 else 0)
        * ((zOf G X pX i x (yOf G X i Y) k : ℤ) : ℝ)
      = ∑ e ∈ Y ∩ G.deltaOut i, pX e - ∑ e ∈ Y ∩ G.deltaIn i, pX e := by
  have hterm : ∀ k : {e // e ∈ G.delta i}, (if k.1 ∈ X then pX k.1 else 0)
      * ((zOf G X pX i x (yOf G X i Y) k : ℤ) : ℝ)
      = if k.1 ∈ Y then pX k.1 * (G.sign i k.1 : ℝ) else 0 := by
    intro k
    unfold zOf
    by_cases h : k.1 ∈ X
    · rw [splitEquiv_mem G X pX i k h, if_pos h]
      simp only [Sum.elim_inr, yOf]
      split_ifs <;> simp
    · rw [if_neg h, zero_mul]
      have : k.1 ∉ Y := fun hk => h (mem_inter.1 (hY hk)).1
      rw [if_neg this]
  rw [sum_congr rfl (fun k _ => hterm k)]
  rw [Finset.sum_coe_sort (G.delta i) (fun e => if e ∈ Y then pX e * (G.sign i e : ℝ) else 0)]
  rw [← Finset.sum_filter]
  have hYd : (G.delta i).filter (fun e => e ∈ Y) = Y := by
    ext e; simp only [mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨(mem_inter.1 (hY h)).2, h⟩⟩
  rw [hYd, ← Finset.sum_filter_add_sum_filter_not Y (fun e => G.seller e = i)]
  have hout : Y ∩ G.deltaOut i = Y.filter (fun e => G.seller e = i) := by
    ext e; simp [Economy.deltaOut]
  have hin : Y ∩ G.deltaIn i = Y.filter (fun e => ¬ G.seller e = i) := by
    ext e
    simp only [mem_inter, mem_filter, Economy.deltaIn, mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => hsb e (h.trans h2.symm)⟩
    · rintro ⟨h1, h2⟩
      have hd := (mem_inter.1 (hY h1)).2
      simp only [Economy.delta, Economy.deltaOut, Economy.deltaIn, mem_union, mem_filter,
        mem_univ, true_and] at hd
      exact ⟨h1, hd.resolve_left h2⟩
  rw [hout, hin]
  have h1 : ∑ e ∈ Y.filter (fun e => G.seller e = i), pX e * (G.sign i e : ℝ)
      = ∑ e ∈ Y.filter (fun e => G.seller e = i), pX e :=
    sum_congr rfl (fun e he => by
      rw [show G.sign i e = 1 by simp [Economy.sign, (mem_filter.1 he).2]]
      simp)
  have h2 : ∑ e ∈ Y.filter (fun e => ¬ G.seller e = i), pX e * (G.sign i e : ℝ)
      = -∑ e ∈ Y.filter (fun e => ¬ G.seller e = i), pX e := by
    rw [← sum_neg_distrib]
    exact sum_congr rfl (fun e he => by
      rw [show G.sign i e = -1 by simp [Economy.sign, (mem_filter.1 he).2]]
      simp)
  rw [h1, h2]
  ring

end Econ2

end TNFContr

open TNFContr in
theorem solution {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E] [DecidableEq E]
    (G : Economy N E) (hG : G.Standing) (X : Finset E)
    (pX : E → ℝ) (i : N) :
    DiscreteConvex.EconomicEquilibrium.MNaturalConcave ((G.contraction X pX).wSigned i) := by
  classical
  set σ := splitEquiv G X pX i with hσ
  set d : {e // e ∈ G.delta i} → ℝ := fun k => if k.1 ∈ X then pX k.1 else 0 with hd
  set U' : ({e // e ∈ G.delta i} → ℤ) → WithBot ℝ :=
    fun w => G.wSigned i w + ((∑ k, d k * (w k : ℝ) : ℝ) : WithBot ℝ) with hU'
  have hU'c : MNaturalConcave U' := mnat_add_linear _ d (hG.2 i)
  set g := fun z => U' (z ∘ σ) with hg
  have hgc : MNaturalConcave g := mnat_reindex σ U' hU'c
  set Ybox : Finset ({e // e ∈ X ∩ G.delta i} → ℤ) :=
    Fintype.piFinset (fun _ => Icc (-1 : ℤ) 1) with hYbox
  -- values of `g` on a combined vector
  have hgz : ∀ x y, g (Sum.elim x y) = G.wSigned i (zOf G X pX i x y)
      + ((∑ k, d k * (zOf G X pX i x y k : ℝ) : ℝ) : WithBot ℝ) := fun x y => rfl
  have hzinr : ∀ x y (b : {e // e ∈ X ∩ G.delta i}),
      zOf G X pX i x y (σ.symm (Sum.inr b)) = y b := by
    intro x y b; unfold zOf; rw [Equiv.apply_symm_apply]; rfl
  have hzinl : ∀ x y a, zOf G X pX i x y (σ.symm (Sum.inl a)) = x a := by
    intro x y a; unfold zOf; rw [Equiv.apply_symm_apply]; rfl
  have hsymm_inr : ∀ b : {e // e ∈ X ∩ G.delta i}, (σ.symm (Sum.inr b)).1 = b.1 := fun b => rfl
  have hsymm_inl : ∀ a : {e' : {e // e ∉ X} // e' ∈ (G.contraction X pX).delta i},
      (σ.symm (Sum.inl a)).1 = a.1.1 := fun a => rfl
  -- `g` is finite only on boxes
  have hbox_of : ∀ z, G.wSigned i z ≠ ⊥ → ∀ k, z k = 0 ∨ z k = G.sign i k.1 := by
    intro z hz
    unfold Economy.wSigned at hz
    by_contra hc
    exact hz (if_neg hc)
  have hY : ∀ x y, g (Sum.elim x y) ≠ ⊥ → y ∈ Ybox := by
    intro x y h
    rw [hgz, Ne, WithBot.add_eq_bot, not_or] at h
    have hb := hbox_of _ h.1
    rw [hYbox, Fintype.mem_piFinset]
    intro b
    have := hb (σ.symm (Sum.inr b))
    rw [hzinr, hsymm_inr] at this
    rw [mem_Icc]
    rcases this with h0 | h0
    · rw [h0]; omega
    · rw [h0]; rcases sign_cases G i b.1 with h1 | h1 <;> rw [h1] <;> omega
  -- the main identity: `ŵ_i` is the projection of `g`
  have heq : (G.contraction X pX).wSigned i = fun x => Ybox.sup (fun y => g (Sum.elim x y)) := by
    funext x
    by_cases hx : ∀ a, x a = 0 ∨ x a = (G.contraction X pX).sign i a.1
    · have hx' : ∀ a, x a = 0 ∨ x a = G.sign i a.1.1 := hx
      -- value of `g` at a lifted set `Y`
      have hT : ∀ Y, Y ⊆ X ∩ G.delta i → g (Sum.elim x (yOf G X i Y))
          = ((G.w i ((Sx G X pX i x).map (Function.Embedding.subtype _) ∪ Y)
              + ∑ e ∈ Y ∩ G.deltaOut i, pX e - ∑ e ∈ Y ∩ G.deltaIn i, pX e : ℝ) : WithBot ℝ) := by
        intro Y hYs
        rw [hgz]
        unfold Economy.wSigned
        rw [if_pos (zOf_box G X pX i x hx' Y), zOf_set G X pX i x Y hYs,
          zOf_lin G hG.1 X pX i x Y hYs, ← WithBot.coe_add]
        congr 1
        ring
      set F : Finset E → ℝ := fun Y =>
        G.w i ((Sx G X pX i x).map (Function.Embedding.subtype _) ∪ Y)
          + ∑ e ∈ Y ∩ G.deltaOut i, pX e - ∑ e ∈ Y ∩ G.deltaIn i, pX e with hF
      have hne : ((X ∩ G.delta i).powerset).Nonempty := ⟨∅, Finset.empty_mem_powerset _⟩
      have hlhs : (G.contraction X pX).wSigned i x = (((X ∩ G.delta i).powerset.sup' hne F : ℝ)
          : WithBot ℝ) := by
        unfold Economy.wSigned
        rw [if_pos hx]
        rfl
      rw [hlhs]
      apply le_antisymm
      · obtain ⟨Ys, hYs, hYeq⟩ := Finset.exists_mem_eq_sup' hne F
        rw [hYeq]
        have : g (Sum.elim x (yOf G X i Ys)) = ((F Ys : ℝ) : WithBot ℝ) :=
          hT Ys (mem_powerset.1 hYs)
        rw [← this]
        refine Finset.le_sup (f := fun y => g (Sum.elim x y)) ?_
        rw [hYbox, Fintype.mem_piFinset]
        intro b
        simp only [yOf, mem_Icc]
        split_ifs
        · rcases sign_cases G i b.1 with h1 | h1 <;> rw [h1] <;> omega
        · omega
      · refine Finset.sup_le (fun y _ => ?_)
        by_cases hfin : g (Sum.elim x y) = ⊥
        · exact (le_of_eq hfin).trans bot_le
        · have hw : G.wSigned i (zOf G X pX i x y) ≠ ⊥ := by
            intro h0
            apply hfin
            rw [hgz, h0]
            simp
          have hb := hbox_of _ hw
          set Yy : Finset E := (univ.filter (fun b => y b ≠ 0)).map (Function.Embedding.subtype _)
            with hYy
          have hYys : Yy ⊆ X ∩ G.delta i := by
            intro e he
            rw [hYy, mem_map] at he
            obtain ⟨b, -, rfl⟩ := he
            exact b.2
          have hyY : y = yOf G X i Yy := by
            funext b
            have := hb (σ.symm (Sum.inr b))
            rw [hzinr, hsymm_inr] at this
            simp only [yOf, hYy, mem_map, mem_filter, mem_univ, true_and,
              Function.Embedding.coe_subtype]
            by_cases h0 : y b = 0
            · rw [if_neg]; · exact h0
              rintro ⟨b', hb', hbb⟩
              exact hb' (by rw [Subtype.ext hbb]; exact h0)
            · rw [if_pos ⟨b, h0, rfl⟩]
              exact this.resolve_left h0
          have : g (Sum.elim x (yOf G X i Yy)) = ((F Yy : ℝ) : WithBot ℝ) := hT Yy hYys
          rw [hyY, this]
          exact WithBot.coe_le_coe.2 (Finset.le_sup' F (mem_powerset.2 hYys))
    · unfold Economy.wSigned
      rw [if_neg hx]
      symm
      rw [Finset.sup_eq_bot_iff]
      intro y _
      push Not at hx
      obtain ⟨a, ha1, ha2⟩ := hx
      rw [hgz]
      have hnb : ¬ ∀ k, zOf G X pX i x y k = 0 ∨ zOf G X pX i x y k = G.sign i k.1 := by
        intro hall
        have := hall (σ.symm (Sum.inl a))
        rw [hzinl, hsymm_inl] at this
        rcases this with h | h
        · exact ha1 h
        · exact ha2 h
      unfold Economy.wSigned
      rw [if_neg hnb]
      simp
  rw [heq]
  exact mnat_proj g hgc Ybox hY
