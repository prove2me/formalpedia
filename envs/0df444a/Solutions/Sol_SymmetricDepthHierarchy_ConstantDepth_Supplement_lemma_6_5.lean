-- Prove2me | solution 1 for SymmetricDepthHierarchy.ConstantDepth.Supplement.lemma_6_5
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T01:08:56.390318+00:00
-- url     : https://prove2.me/submissions/bccb80b9-a4c0-4fc6-ba7f-ff8a28381dba

import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Supplement_Branching

set_option autoImplicit false
open scoped Classical
noncomputable section

namespace SymmetricDepthHierarchy.ConstantDepth.Supplement

section Generic
variable {α β : Type} [Fintype α]

def rk (R : α → α → Prop) (a : α) : ℕ :=
  (Finset.univ.filter fun b => Relation.TransGen R b a).card

lemma rk_lt (R : α → α → Prop) (hac : ∀ a, ¬ Relation.TransGen R a a) {b a : α} (h : R b a) :
    rk R b < rk R a := by
  unfold rk
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨b, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact Relation.TransGen.single h
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hac b
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hx.trans (Relation.TransGen.single h)

lemma rk_lt_card (R : α → α → Prop) (hac : ∀ a, ¬ Relation.TransGen R a a) (a : α) :
    rk R a < Fintype.card α := by
  unfold rk
  calc _ < (Finset.univ : Finset α).card := by
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset (Finset.subset_univ _)]
        exact ⟨a, Finset.mem_univ _, by simp [hac a]⟩
    _ = _ := Finset.card_univ

lemma rank_stable (R : α → α → Prop) (hac : ∀ a, ¬ Relation.TransGen R a a)
    (step : (α → β) → α → β)
    (hloc : ∀ f f' a, (∀ b, R b a → f b = f' b) → step f a = step f' a)
    (F : ℕ → α → β) (z : α → β) (h0 : F 0 = step z) (hs : ∀ k, F (k+1) = step (F k)) :
    ∀ k a, rk R a ≤ k → F k a = F (k+1) a := by
  intro k
  induction k with
  | zero =>
    intro a ha
    rw [h0, hs 0]
    apply hloc
    intro b hb
    have := rk_lt R hac hb
    omega
  | succ k ih =>
    intro a ha
    refine (congrFun (hs k) a).trans ((hloc _ _ a ?_).trans (congrFun (hs (k+1)) a).symm)
    intro b hb
    have := rk_lt R hac hb
    exact ih b (by omega)

lemma rank_stable' (R : α → α → Prop) (hac : ∀ a, ¬ Relation.TransGen R a a)
    (step : (α → β) → α → β)
    (hloc : ∀ f f' a, (∀ b, R b a → f b = f' b) → step f a = step f' a)
    (F : ℕ → α → β) (z : α → β) (h0 : F 0 = step z) (hs : ∀ k, F (k+1) = step (F k))
    (a : α) {k : ℕ} (hk : Fintype.card α ≤ k) : F k a = F (Fintype.card α) a := by
  have key : ∀ j, F (Fintype.card α + j) a = F (Fintype.card α) a := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [← ih, ← add_assoc]
      exact (rank_stable R hac step hloc F z h0 hs _ a
        (by have := rk_lt_card R hac a; omega)).symm
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  exact key j

lemma fixed_unique (R : α → α → Prop) (hac : ∀ a, ¬ Relation.TransGen R a a)
    (step : (α → β) → α → β)
    (hloc : ∀ f f' a, (∀ b, R b a → f b = f' b) → step f a = step f' a)
    (f f' : α → β) (hf : ∀ a, f a = step f a) (hf' : ∀ a, f' a = step f' a) : f = f' := by
  have : ∀ n, ∀ a, rk R a = n → f a = f' a := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro a ha
      rw [hf a, hf' a]
      apply hloc
      intro b hb
      exact ih _ (ha ▸ rk_lt R hac hb) b rfl
  funext a
  exact this _ a rfl

lemma sum_subtype_dite {α M : Type} [Fintype α] [AddCommMonoid M] (P : α → Prop) (F : {a // P a} → M) :
    ∑ e : {a // P a}, F e = ∑ a : α, if h : P a then F ⟨a, h⟩ else 0 := by
  have h1 := Finset.sum_subtype (Finset.univ.filter P) (p := P) (F := inferInstance) (by simp)
    (fun a => if h : P a then F ⟨a, h⟩ else 0)
  have h2 : ∑ a : {a // P a}, (if h : P a.1 then F ⟨a.1, h⟩ else 0) = ∑ e : {a // P a}, F e := by
    apply Finset.sum_congr rfl
    intro a _
    simp [a.2]
  rw [← h2, ← h1, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : P a <;> simp [h]

end Generic

section CircuitLemmas
variable {K : Type} [Field K] {n : ℕ} {V : Type} [Fintype V]
open Circuit

lemma evalStep_loc (C : Circuit K n V) (f f' : V → MvPolynomial (Fin n × Fin n) K) (g : V)
    (h : ∀ h', C.Wire h' g → f h' = f' h') : C.evalStep f g = C.evalStep f' g := by
  unfold Circuit.evalStep
  have : ∀ h', C.mult g h' = 0 ∨ f h' = f' h' := by
    intro h'
    by_cases hm : C.mult g h' = 0
    · exact Or.inl hm
    · exact Or.inr (h h' (Nat.pos_of_ne_zero hm))
  split
  · rfl
  · rfl
  · apply Finset.sum_congr rfl
    intro h' _
    rcases this h' with hm | hm <;> simp [hm]
  · apply Finset.prod_congr rfl
    intro h' _
    rcases this h' with hm | hm <;> simp [hm]

lemma value_fixed (C : Circuit K n V) (hC : ∀ g, ¬ Relation.TransGen C.Wire g g) (g : V) :
    C.value g = C.evalStep C.value g := by
  have h := rank_stable' C.Wire hC C.evalStep (evalStep_loc C) C.valueAux (fun _ => 0)
    rfl (fun _ => rfl) g (k := Fintype.card V + 1) (by omega)
  exact h.symm

end CircuitLemmas

section ABPLemmas
variable {K X V : Type} [Field K] [Fintype X] [Fintype V]

def pathStep (G : ABP K X V) (f : V → MvPolynomial X K) (v : V) : MvPolynomial X K :=
  (if v = G.source then 1 else 0) +
      ∑ u, if G.edge u v then f u * (G.label u v).toPoly else 0

lemma pathStep_loc (G : ABP K X V) (f f' : V → MvPolynomial X K) (v : V)
    (h : ∀ u, G.edge u v → f u = f' u) : pathStep G f v = pathStep G f' v := by
  unfold pathStep
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  by_cases he : G.edge u v
  · simp [he, h u he]
  · simp [he]

lemma pathAux_fixed (G : ABP K X V) (hG : G.wellFormed) (v : V) :
    G.pathAux (Fintype.card V) v = pathStep G (G.pathAux (Fintype.card V)) v := by
  have h := rank_stable' G.edge hG.1 (pathStep G) (pathStep_loc G) G.pathAux (fun _ => 0)
    (by funext v; simp [pathStep, ABP.pathAux]) (fun _ => rfl) v (k := Fintype.card V + 1) (by omega)
  exact h.symm

end ABPLemmas


section ABPGeneric
variable {K X V : Type} [Field K] [Fintype X] [Fintype V]

lemma rk_lt_trans {α : Type} [Fintype α] (R : α → α → Prop) (hac : ∀ a, ¬ Relation.TransGen R a a)
    {b a : α} (h : Relation.TransGen R b a) : rk R b < rk R a := by
  unfold rk
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨b, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hac b
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hx.trans h

lemma acyclic_of_pot {α : Type} (R : α → α → Prop) (φ : α → ℕ) (h : ∀ a b, R a b → φ a < φ b)
    (a : α) : ¬ Relation.TransGen R a a := by
  have key : ∀ a b, Relation.TransGen R a b → φ a < φ b := by
    intro a b hab
    induction hab with
    | single hr => exact h _ _ hr
    | tail _ hr ih => exact lt_trans ih (h _ _ hr)
  intro hc
  exact lt_irrefl _ (key a a hc)

lemma poly_of_fixed (G : ABP K X V) (hG : G.wellFormed) (f : V → MvPolynomial X K)
    (hf : ∀ v, f v = pathStep G f v) : G.polynomial = f G.sink := by
  have := fixed_unique G.edge hG.1 (pathStep G) (pathStep_loc G) _ f (pathAux_fixed G hG) hf
  unfold ABP.polynomial
  rw [this]

lemma reach_sink' (G : ABP K X V) (hG : G.wellFormed) (v : V) :
    Relation.ReflTransGen G.edge v G.sink := by
  have : ∀ k, ∀ v, Fintype.card V - rk G.edge v = k → Relation.ReflTransGen G.edge v G.sink := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro v hk
      by_cases hv : v = G.sink
      · subst hv; exact Relation.ReflTransGen.refl
      · have h : ¬ (¬ ∃ w, G.edge v w) := fun h => hv ((hG.2.2 v).1 h)
        push_neg at h
        obtain ⟨w, hw⟩ := h
        have h1 := rk_lt G.edge hG.1 hw
        have h2 := rk_lt_card G.edge hG.1 w
        exact (Relation.ReflTransGen.single hw).trans (ih _ (by omega) w rfl)
  exact this _ v rfl

/-! ### Relabelling an ABP along an equivalence -/

def ABP.rl {W : Type} (G : ABP K X V) (e : V ≃ W) : ABP K X W where
  edge a b := G.edge (e.symm a) (e.symm b)
  label a b := G.label (e.symm a) (e.symm b)
  source := e G.source
  sink := e G.sink

variable {W : Type} [Fintype W]

lemma rl_pathAux (G : ABP K X V) (e : V ≃ W) (k : ℕ) (w : W) :
    (G.rl e).pathAux k w = G.pathAux k (e.symm w) := by
  induction k generalizing w with
  | zero =>
    simp only [ABP.pathAux, ABP.rl]
    congr 1
    exact propext ⟨fun h => by rw [h]; simp, fun h => by rw [← h]; simp⟩
  | succ k ih =>
    simp only [ABP.pathAux]
    congr 1
    · simp only [ABP.rl]
      congr 1
      exact propext ⟨fun h => by rw [h]; simp, fun h => by rw [← h]; simp⟩
    · rw [← Equiv.sum_comp e]
      apply Finset.sum_congr rfl
      intro u _
      rw [ih (e u)]
      simp only [ABP.rl, Equiv.symm_apply_apply]

lemma rl_polynomial (G : ABP K X V) (e : V ≃ W) : (G.rl e).polynomial = G.polynomial := by
  unfold ABP.polynomial
  rw [rl_pathAux, Fintype.card_congr e.symm]
  simp [ABP.rl]

lemma rl_wf (G : ABP K X V) (e : V ≃ W) (hG : G.wellFormed) : (G.rl e).wellFormed := by
  refine ⟨?_, ?_, ?_⟩
  · intro a h
    have key : ∀ a b, Relation.TransGen (G.rl e).edge a b →
        Relation.TransGen G.edge (e.symm a) (e.symm b) := by
      intro a b hab
      induction hab with
      | single hr => exact Relation.TransGen.single hr
      | tail _ hr ih => exact ih.tail hr
    exact hG.1 (e.symm a) (key a a h)
  · intro v
    have := hG.2.1 (e.symm v)
    simp only [ABP.rl]
    rw [show (v = e G.source) ↔ (e.symm v = G.source) from
      ⟨fun h => by rw [h]; simp, fun h => by rw [← h]; simp⟩, ← this]
    constructor
    · intro h ⟨u, hu⟩; exact h ⟨e u, by simpa using hu⟩
    · intro h ⟨u, hu⟩; exact h ⟨_, hu⟩
  · intro v
    have := hG.2.2 (e.symm v)
    simp only [ABP.rl]
    rw [show (v = e G.sink) ↔ (e.symm v = G.sink) from
      ⟨fun h => by rw [h]; simp, fun h => by rw [← h]; simp⟩, ← this]
    constructor
    · intro h ⟨u, hu⟩; exact h ⟨e u, by simpa using hu⟩
    · intro h ⟨u, hu⟩; exact h ⟨_, hu⟩

lemma rl_ext (G : ABP K X V) (e : V ≃ W) (f : Equiv.Perm X) (σ : Equiv.Perm V)
    (h : G.extension f σ) : (G.rl e).extension f (e.permCongr σ) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [ABP.rl, Equiv.permCongr_apply, h1]
  · simp [ABP.rl, Equiv.permCongr_apply, h2]
  · intro u v; simp [ABP.rl, Equiv.permCongr_apply, h3]
  · intro u v huv; simpa [ABP.rl, Equiv.permCongr_apply] using h4 _ _ huv

lemma rl_ext' (G : ABP K X V) (e : V ≃ W) (f : Equiv.Perm X) (σ : Equiv.Perm W)
    (h : (G.rl e).extension f σ) : G.extension f (e.symm.permCongr σ) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [ABP.rl] at h1 h2 h3 h4
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [Equiv.permCongr_apply, h1]
  · simp [Equiv.permCongr_apply, h2]
  · intro u v; have := h3 (e u) (e v); simpa [Equiv.permCongr_apply] using this
  · intro u v huv; have := h4 (e u) (e v) (by simpa using huv)
    simpa [Equiv.permCongr_apply] using this

lemma rl_symm (G : ABP K X V) (e : V ≃ W) {H : Type} [Group H] (ρ : H →* Equiv.Perm X)
    (h : G.symmetric ρ) : (G.rl e).symmetric ρ := by
  intro γ
  obtain ⟨σ, hσ⟩ := h γ
  exact ⟨_, rl_ext G e _ σ hσ⟩

lemma rl_maxOrb (G : ABP K X V) (e : V ≃ W) {H : Type} [Group H] (ρ : H →* Equiv.Perm X) :
    (G.rl e).maxOrb ρ ≤ G.maxOrb ρ := by
  unfold ABP.maxOrb
  apply Finset.sup_le
  intro w _
  refine le_trans ?_ (Finset.le_sup (f := fun v => (Finset.univ.filter fun w =>
    ∃ γ σ, G.extension (ρ γ) σ ∧ σ v = w).card) (Finset.mem_univ (e.symm w)))
  apply Finset.card_le_card_of_injOn e.symm
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx ⊢
    obtain ⟨γ, σ, hσ, rfl⟩ := hx
    exact ⟨γ, _, rl_ext' G e _ σ hσ, by simp [Equiv.permCongr_apply]⟩
  · intro x _ y _ hxy; exact e.symm.injective hxy

end ABPGeneric

section Tagging
variable {K X V T : Type} [Field K] [CharZero K] [Fintype X] [Fintype V] [Encodable T]

lemma toPoly_const (c : K) : (⟨c, 0⟩ : BorderDiffEq.AffineForm K X).toPoly = MvPolynomial.C c := by
  simp [BorderDiffEq.AffineForm.toPoly]

def tagN0 (G : ABP K X V) : ℕ := 1 + ∑ p : V × V,
  (if h : ∃ k : ℕ, (G.label p.1 p.2).toPoly = MvPolynomial.C (k : K) then Classical.choose h else 0)

lemma tag_avoid (G : ABP K X V) (u v : V) (t : ℕ) :
    (G.label u v).toPoly ≠ MvPolynomial.C (((tagN0 G + t : ℕ)) : K) := by
  intro heq
  have hex : ∃ k : ℕ, (G.label u v).toPoly = MvPolynomial.C (k : K) := ⟨_, heq⟩
  have h1 := Classical.choose_spec hex
  have h2 : Classical.choose hex = tagN0 G + t := by
    have := (MvPolynomial.C_inj K _ _).1 (h1.symm.trans heq)
    exact_mod_cast this
  have h3 := Finset.single_le_sum (f := fun p : V × V =>
    if h : ∃ k : ℕ, (G.label p.1 p.2).toPoly = MvPolynomial.C (k : K) then Classical.choose h else 0)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ (u, v))
  dsimp only at h3
  rw [dif_pos hex] at h3
  unfold tagN0 at h2
  omega

def tcode (G : ABP K X V) (t : T) : K := ((tagN0 G + Encodable.encode t : ℕ) : K)

lemma tcode_inj (G : ABP K X V) {t t' : T} (h : tcode G t = tcode G t') : t = t' := by
  unfold tcode at h
  have : tagN0 G + Encodable.encode t = tagN0 G + Encodable.encode t' := by exact_mod_cast h
  exact Encodable.encode_injective (by omega)

lemma tcode_ne_zero (G : ABP K X V) (t : T) : tcode G t ≠ 0 := by
  unfold tcode
  have : tagN0 G + Encodable.encode t ≠ 0 := by unfold tagN0; omega
  exact_mod_cast this

def tagged (G : ABP K X V) (tag : V → T) : ABP K X (V ⊕ {v // v ≠ G.sink}) where
  edge a b := match a, b with
    | .inl u, .inl v => G.edge u v
    | .inl u, .inr w => u = w.1
    | .inr _, .inl v => v = G.sink
    | .inr _, .inr _ => False
  label a b := match a, b with
    | .inl u, .inl v => G.label u v
    | .inl u, .inr _ => ⟨tcode G (tag u), 0⟩
    | _, _ => ⟨0, 0⟩
  source := .inl G.source
  sink := .inl G.sink

lemma tagged_wf (G : ABP K X V) (tag : V → T) (hG : G.wellFormed) (hss : G.source ≠ G.sink) :
    (tagged G tag).wellFormed := by
  refine ⟨?_, ?_, ?_⟩
  · apply acyclic_of_pot _ (fun a => match a with
      | .inl v => 2 * rk G.edge v
      | .inr w => 2 * rk G.edge w.1 + 1)
    intro a b hab
    rcases a with u | w <;> rcases b with v | w'
    · have := rk_lt G.edge hG.1 (show G.edge u v from hab)
      dsimp only; omega
    · have h : u = w'.1 := hab
      subst h; dsimp only; omega
    · have h : v = G.sink := hab
      subst h
      have hr := reach_sink' G hG w.1
      rcases Relation.reflTransGen_iff_eq_or_transGen.1 hr with h | h
      · exact absurd h.symm w.2
      · have := rk_lt_trans G.edge hG.1 h
        dsimp only; omega
    · exact absurd hab id
  · intro v'
    rcases v' with v | w
    · have := hG.2.1 v
      constructor
      · intro h
        have : v = G.source := this.1 (fun ⟨u, hu⟩ => h ⟨.inl u, hu⟩)
        simp [tagged, this]
      · intro h ⟨u', hu'⟩
        have hv : v = G.source := by simpa [tagged] using h
        rcases u' with u | w
        · exact this.2 hv ⟨u, hu'⟩
        · exact hss (hv.symm.trans hu')
    · constructor
      · intro h; exact absurd ⟨.inl w.1, rfl⟩ h
      · intro h; simp [tagged] at h
  · intro v'
    rcases v' with v | w
    · by_cases hv : v = G.sink
      · subst hv
        have := hG.2.2 G.sink
        constructor
        · intro _; rfl
        · intro _ ⟨u', hu'⟩
          rcases u' with u | w
          · exact this.2 rfl ⟨u, hu'⟩
          · exact w.2 hu'.symm
      · constructor
        · intro h; exact absurd ⟨.inr ⟨v, hv⟩, rfl⟩ h
        · intro h; simp [tagged] at h; exact absurd h hv
    · constructor
      · intro h; exact absurd ⟨.inl G.sink, rfl⟩ h
      · intro h; simp [tagged] at h

lemma tagged_poly (G : ABP K X V) (tag : V → T) (hG : G.wellFormed) (hss : G.source ≠ G.sink) :
    (tagged G tag).polynomial = G.polynomial := by
  set P := G.pathAux (Fintype.card V) with hP
  rw [poly_of_fixed _ (tagged_wf G tag hG hss) (fun a => match a with
      | .inl v => P v
      | .inr w => P w.1 * MvPolynomial.C (tcode G (tag w.1)))]
  · rfl
  · intro a
    rcases a with v | w
    · unfold pathStep
      rw [Fintype.sum_sum_type]
      simp only [tagged, toPoly_const, map_zero, mul_zero, ite_self, Finset.sum_const_zero,
        add_zero, Sum.inl.injEq]
      exact pathAux_fixed G hG v
    · unfold pathStep
      rw [Fintype.sum_sum_type]
      simp only [tagged, toPoly_const, reduceCtorEq, if_false, zero_add, Finset.sum_const_zero,
        add_zero]
      rw [Finset.sum_ite_eq']
      simp

lemma tagged_symm (G : ABP K X V) (tag : V → T) {H : Type} [Group H] (ρ : H →* Equiv.Perm X)
    (hs : ∀ γ, ∃ σ, G.extension (ρ γ) σ ∧ ∀ v, tag (σ v) = tag v) :
    (tagged G tag).symmetric ρ := by
  intro γ
  obtain ⟨σ, ⟨h1, h2, h3, h4⟩, ht⟩ := hs γ
  have hiff : ∀ x, σ x = G.sink ↔ x = G.sink := fun x =>
    ⟨fun h => σ.injective (h.trans h2.symm), fun h => h ▸ h2⟩
  refine ⟨Equiv.sumCongr σ (σ.subtypePerm (fun x => by simp only [ne_eq, hiff])), ?_, ?_, ?_, ?_⟩
  · simp [tagged, h1]
  · simp [tagged, h2]
  · intro u v
    rcases u with u | u <;> rcases v with v | v <;>
      simp [tagged, h3, hiff, Equiv.Perm.subtypePerm_apply]
  · intro u v huv
    rcases u with u | u <;> rcases v with v | v
    · simpa [tagged] using h4 u v huv
    · simp [tagged, toPoly_const, ht]
    · simp [tagged, toPoly_const]
    · exact absurd huv id

lemma tagged_core (G : ABP K X V) (tag : V → T) (f : Equiv.Perm X) (σ : Equiv.Perm _)
    (hσ : (tagged G tag).extension f σ) (v : V) (hv : v ≠ G.sink) :
    ∃ a, ∃ ha : a ≠ G.sink, σ (.inl v) = .inl a ∧ σ (.inr ⟨v, hv⟩) = .inr ⟨a, ha⟩ ∧
      tag a = tag v := by
  obtain ⟨h1, h2, h3, h4⟩ := hσ
  have he : (tagged G tag).edge (.inl v) (.inr ⟨v, hv⟩) := rfl
  have hl := h4 _ _ he
  have he' := (h3 _ _).2 he
  rcases hx : σ (.inl v) with a | w1 <;> rcases hy : σ (.inr ⟨v, hv⟩) with b | w2 <;>
    rw [hx, hy] at hl he' <;> simp only [tagged, toPoly_const, MvPolynomial.rename_C] at hl he'
  · exact absurd hl (tag_avoid G a b _)
  · subst he'
    refine ⟨w2.1, w2.2, rfl, rfl, ?_⟩
    exact tcode_inj G ((MvPolynomial.C_inj K _ _).1 hl)
  · exact absurd ((MvPolynomial.C_inj K _ _).1 hl).symm (tcode_ne_zero G _)

lemma tagged_maxOrb (G : ABP K X V) (tag : V → T) {H : Type} [Group H] (ρ : H →* Equiv.Perm X)
    (B : ℕ) (hB : ∀ v, (Finset.univ.filter fun w => tag w = tag v).card ≤ B) :
    (tagged G tag).maxOrb ρ ≤ B := by
  let tagx : V ⊕ {v // v ≠ G.sink} → Bool × T := fun a => match a with
    | .inl v => (false, tag v)
    | .inr w => (true, tag w.1)
  let base : V ⊕ {v // v ≠ G.sink} → V := fun a => match a with
    | .inl v => v
    | .inr w => w.1
  have key : ∀ f σ, (tagged G tag).extension f σ → ∀ x, tagx (σ x) = tagx x := by
    intro f σ hσ x
    rcases x with v | w
    · by_cases hv : v = G.sink
      · subst hv
        have : σ (.inl G.sink) = .inl G.sink := hσ.2.1
        rw [this]
      · obtain ⟨a, ha, hx, -, hat⟩ := tagged_core G tag f σ hσ v hv
        rw [hx]; simp [tagx, hat]
    · obtain ⟨a, ha, -, hy, hat⟩ := tagged_core G tag f σ hσ w.1 w.2
      rw [hy]; simp [tagx, hat]
  unfold ABP.maxOrb
  apply Finset.sup_le
  intro x _
  calc _ ≤ (Finset.univ.filter fun y => tagx y = tagx x).card := by
        apply Finset.card_le_card
        intro y hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
        obtain ⟨γ, σ, hσ, rfl⟩ := hy
        exact key _ σ hσ x
    _ ≤ (Finset.univ.filter fun w => tag w = tag (base x)).card := by
        apply Finset.card_le_card_of_injOn base
        · intro y hy
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hy ⊢
          rcases x with v | w <;> rcases y with u | u <;> simp_all [tagx, base]
        · intro y hy z hz hyz
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hy hz
          rcases y with u | u <;> rcases z with u' | u' <;> rcases x with v | w <;>
            simp_all [tagx, base, Subtype.ext_iff]
    _ ≤ B := hB _

theorem tag_fin (G : ABP K X V) (hG : G.wellFormed) (hss : G.source ≠ G.sink)
    {H : Type} [Group H] (ρ : H →* Equiv.Perm X) (tag : V → T)
    (hs : ∀ γ, ∃ σ, G.extension (ρ γ) σ ∧ ∀ v, tag (σ v) = tag v)
    (B : ℕ) (hB : ∀ v, (Finset.univ.filter fun w => tag w = tag v).card ≤ B) :
    ∃ m, ∃ G' : ABP K X (Fin m), G'.wellFormed ∧ G'.symmetric ρ ∧
      G'.polynomial = G.polynomial ∧ G'.maxOrb ρ ≤ B :=
  ⟨_, (tagged G tag).rl (Fintype.equivFin _), rl_wf _ _ (tagged_wf G tag hG hss),
    rl_symm _ _ ρ (tagged_symm G tag ρ hs),
    by rw [rl_polynomial, tagged_poly G tag hG hss],
    le_trans (rl_maxOrb _ _ ρ) (tagged_maxOrb G tag ρ B hB)⟩

end Tagging

section Construction
open Circuit MvPolynomial

inductive Vx (M D : ℕ)
  | src
  | snk
  | gt (g : Fin M)
  | ee (g : Fin M) (j : Fin (D+1))
  | ch (g : Fin M) (j i t : Fin (D+1)) (s : Fin M)
  deriving Fintype

def vxEquiv (M D : ℕ) : Vx M D ≃ Unit ⊕ Unit ⊕ Fin M ⊕ (Fin M × Fin (D+1)) ⊕
    (Fin M × Fin (D+1) × Fin (D+1) × Fin (D+1) × Fin M) where
  toFun
    | .src => .inl ()
    | .snk => .inr (.inl ())
    | .gt g => .inr (.inr (.inl g))
    | .ee g j => .inr (.inr (.inr (.inl (g, j))))
    | .ch g j i t s => .inr (.inr (.inr (.inr (g, j, i, t, s))))
  invFun
    | .inl () => .src
    | .inr (.inl ()) => .snk
    | .inr (.inr (.inl g)) => .gt g
    | .inr (.inr (.inr (.inl (g, j)))) => .ee g j
    | .inr (.inr (.inr (.inr (g, j, i, t, s)))) => .ch g j i t s
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with ⟨⟩ | ⟨⟩ | _ | ⟨_, _⟩ | ⟨_, _, _, _, _⟩ <;> rfl

lemma sum_Vx {M D : ℕ} {β : Type} [AddCommMonoid β] (f : Vx M D → β) :
    ∑ u, f u = f .src + f .snk + ∑ g, f (.gt g) + ∑ g, ∑ j, f (.ee g j) +
      ∑ g, ∑ j, ∑ i, ∑ t, ∑ s, f (.ch g j i t s) := by
  rw [← (vxEquiv M D).symm.sum_comp]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.univ_unit, Finset.sum_singleton]
  simp only [vxEquiv, Equiv.coe_fn_symm_mk, add_assoc]

variable {K : Type} [Field K] {n M : ℕ}

lemma pai {α : Type} (τ : Equiv.Perm α) (x : α) : τ (τ⁻¹ x) = x := τ.apply_symm_apply x
lemma pia {α : Type} (τ : Equiv.Perm α) (x : α) : τ⁻¹ (τ x) = x := τ.symm_apply_apply x

def vpoly (C : Circuit K n (Fin M)) (s : Fin M) : MvPolynomial (Fin n × Fin n) K :=
  match C.label s with
  | .var i j => X (i, j)
  | _ => 0

def xA (C : Circuit K n (Fin M)) (s : Fin M) : BorderDiffEq.AffineForm K (Fin n × Fin n) :=
  match C.label s with
  | .var i j => ⟨0, fun l => if l = (i, j) then 1 else 0⟩
  | _ => ⟨0, 0⟩

def isVarB (C : Circuit K n (Fin M)) (s : Fin M) : Prop :=
  match C.label s with
  | .var _ _ => True
  | _ => False

def constOf (C : Circuit K n (Fin M)) (s : Fin M) : K :=
  match C.label s with
  | .const c => c
  | _ => 1

def inPoly (C : Circuit K n (Fin M)) (g : Fin M) : MvPolynomial (Fin n × Fin n) K :=
  match C.label g with
  | .var i j => X (i, j)
  | .const c => MvPolynomial.C c
  | .op _ => 0

def inA (C : Circuit K n (Fin M)) (g : Fin M) : BorderDiffEq.AffineForm K (Fin n × Fin n) :=
  match C.label g with
  | .var i j => ⟨0, fun l => if l = (i, j) then 1 else 0⟩
  | .const c => ⟨c, 0⟩
  | .op _ => ⟨0, 0⟩

def mu (C : Circuit K n (Fin M)) (g s : Fin M) : ℕ := if isVarB C s then C.mult g s else 0

def mdeg (C : Circuit K n (Fin M)) (g : Fin M) : ℕ := ∑ s, mu C g s

def Dg (C : Circuit K n (Fin M)) : ℕ := Finset.univ.sup (mdeg C)

def kap (C : Circuit K n (Fin M)) (g : Fin M) : K := ∏ s, constOf C s ^ C.mult g s

def noInt (C : Circuit K n (Fin M)) (g : Fin M) : Prop := ∀ h, ¬ C.IsInput h → C.mult g h = 0

def base (C : Circuit K n (Fin M)) (g : Fin M) : MvPolynomial (Fin n × Fin n) K :=
  ∏ h, if C.IsInput h then 1 else C.value h ^ C.mult g h

abbrev Sl (C : Circuit K n (Fin M)) (g : Fin M) := Σ s : Fin M, Fin (mu C g s)

def eS (C : Circuit K n (Fin M)) (g : Fin M) (j : ℕ) : MvPolynomial (Fin n × Fin n) K :=
  aeval (fun x : Sl C g => vpoly C x.1) (esymm (Sl C g) K j)

def pS (C : Circuit K n (Fin M)) (g : Fin M) (k : ℕ) : MvPolynomial (Fin n × Fin n) K :=
  aeval (fun x : Sl C g => vpoly C x.1) (psum (Sl C g) K k)

def coef (j i : ℕ) : K := (-1) ^ (j + 1 + i) * (j : K)⁻¹

def cv (C : Circuit K n (Fin M)) (g : Fin M) (j i : ℕ) (s : Fin M) : Prop :=
  C.label g = .op .mul ∧ 0 < mu C g s ∧ i < j

def sc (a : K) (ℓ : BorderDiffEq.AffineForm K (Fin n × Fin n)) :
    BorderDiffEq.AffineForm K (Fin n × Fin n) := ⟨a * ℓ.c, fun l => a * ℓ.a l⟩

/-! ### Affine-form evaluations -/

lemma toPoly_c (c : K) :
    (⟨c, 0⟩ : BorderDiffEq.AffineForm K (Fin n × Fin n)).toPoly = MvPolynomial.C c := by
  simp [BorderDiffEq.AffineForm.toPoly]

lemma toPoly_single (l0 : Fin n × Fin n) :
    (⟨0, fun l => if l = l0 then 1 else 0⟩ : BorderDiffEq.AffineForm K (Fin n × Fin n)).toPoly
      = X l0 := by
  unfold BorderDiffEq.AffineForm.toPoly
  rw [Finset.sum_eq_single l0]
  · simp
  · intro b _ hb; simp [hb]
  · simp

lemma toPoly_sc (a : K) (ℓ : BorderDiffEq.AffineForm K (Fin n × Fin n)) :
    (sc a ℓ).toPoly = MvPolynomial.C a * ℓ.toPoly := by
  simp only [sc, BorderDiffEq.AffineForm.toPoly, map_mul, mul_add, Finset.mul_sum, mul_assoc]

lemma toPoly_xA (C : Circuit K n (Fin M)) (s : Fin M) : (xA C s).toPoly = vpoly C s := by
  unfold xA vpoly
  split
  · exact toPoly_single _
  · exact toPoly_c 0 |>.trans (by simp)

lemma toPoly_inA (C : Circuit K n (Fin M)) (g : Fin M) : (inA C g).toPoly = inPoly C g := by
  unfold inA inPoly
  split
  · exact toPoly_single _
  · exact toPoly_c _
  · exact toPoly_c 0 |>.trans (by simp)

/-! ### Newton identities for the slot polynomials -/

lemma pS_eq (C : Circuit K n (Fin M)) (g : Fin M) (k : ℕ) :
    pS C g k = ∑ s, (mu C g s : MvPolynomial (Fin n × Fin n) K) * vpoly C s ^ k := by
  unfold pS
  simp [psum, map_sum, Fintype.sum_sigma]

lemma eS_top (C : Circuit K n (Fin M)) (g : Fin M) :
    eS C g (mdeg C g) = ∏ s, vpoly C s ^ mu C g s := by
  have hc : (Finset.univ : Finset (Sl C g)).card = mdeg C g := by
    simp [Finset.card_univ, Fintype.card_sigma, mdeg]
  unfold eS
  rw [← hc, esymm, Finset.powersetCard_self, Finset.sum_singleton, map_prod]
  simp [Fintype.prod_sigma]

lemma eS_newton (C : Circuit K n (Fin M)) [CharZero K] (g : Fin M) (j : ℕ) (hj : 1 ≤ j) :
    eS C g j = ∑ i ∈ Finset.range j,
      MvPolynomial.C (coef j i) * eS C g i * pS C g (j - i) := by
  have h := congrArg (aeval (fun x : Sl C g => vpoly C x.1))
    (MvPolynomial.mul_esymm_eq_sum (Sl C g) K j)
  simp only [map_mul, map_sum, map_pow, map_neg, map_one, map_natCast] at h
  rw [Finset.sum_filter, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ] at h
  simp only [lt_irrefl, if_false, add_zero] at h
  have h' : ((j : MvPolynomial (Fin n × Fin n) K)) * eS C g j =
      (-1) ^ (j + 1) * ∑ i ∈ Finset.range j, (-1) ^ i * eS C g i * pS C g (j - i) := by
    unfold eS pS
    rw [h]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [if_pos (Finset.mem_range.1 hi)]
  have hj0 : (j : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  calc eS C g j = MvPolynomial.C (j : K)⁻¹ * ((j : MvPolynomial (Fin n × Fin n) K) * eS C g j) := by
        rw [← mul_assoc, ← map_natCast (MvPolynomial.C (σ := Fin n × Fin n) (R := K)) j, ← map_mul,
          inv_mul_cancel₀ hj0, map_one, one_mul]
    _ = _ := by
        rw [h', Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        simp only [coef, map_mul, map_pow, map_neg, map_one, pow_add]
        ring

/-! ### Circuit facts -/

lemma value_eq (C : Circuit K n (Fin M)) (hwf : C.WellFormed) (g : Fin M) :
    C.value g = C.evalStep C.value g := value_fixed C hwf.acyclic g

lemma value_var (C : Circuit K n (Fin M)) (hwf : C.WellFormed) {g : Fin M} {i j : Fin n}
    (hl : C.label g = .var i j) : C.value g = X (i, j) := by
  rw [value_eq C hwf]; simp only [Circuit.evalStep, hl]

lemma value_const (C : Circuit K n (Fin M)) (hwf : C.WellFormed) {g : Fin M} {c : K}
    (hl : C.label g = .const c) : C.value g = MvPolynomial.C c := by
  rw [value_eq C hwf]; simp only [Circuit.evalStep, hl]

lemma value_add (C : Circuit K n (Fin M)) (hwf : C.WellFormed) {g : Fin M}
    (hl : C.label g = .op .add) :
    C.value g = ∑ h, (C.mult g h : MvPolynomial (Fin n × Fin n) K) * C.value h := by
  rw [value_eq C hwf]; simp only [Circuit.evalStep, hl]

lemma value_mul (C : Circuit K n (Fin M)) (hwf : C.WellFormed) {g : Fin M}
    (hl : C.label g = .op .mul) :
    C.value g = base C g * (∏ s, vpoly C s ^ mu C g s) * MvPolynomial.C (kap C g) := by
  rw [value_eq C hwf]
  simp only [Circuit.evalStep, hl]
  rw [kap, map_prod, base, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro h _
  cases hh : C.label h with
  | var i j =>
    simp [Circuit.IsInput, hh, mu, isVarB, vpoly, constOf, value_var C hwf hh]
  | const c =>
    simp [Circuit.IsInput, hh, mu, isVarB, vpoly, constOf, value_const C hwf hh]
  | op o =>
    simp [Circuit.IsInput, hh, mu, isVarB, vpoly, constOf]

lemma base_eq (C : Circuit K n (Fin M)) (hskew : isSkew C) {g : Fin M}
    (hl : C.label g = .op .mul) :
    base C g = (if noInt C g then 1 else 0) +
      ∑ h, if ¬ C.IsInput h ∧ 0 < C.mult g h then C.value h else 0 := by
  have hs := hskew g hl
  by_cases hni : noInt C g
  · rw [if_pos hni, base, Finset.sum_eq_zero, Finset.prod_eq_one]
    · simp
    · intro h _
      by_cases hi : C.IsInput h
      · simp [hi]
      · simp [hi, hni h hi]
    · intro h _
      by_cases hi : C.IsInput h
      · simp [hi]
      · simp [hi, hni h hi]
  · rw [if_neg hni, zero_add]
    unfold noInt at hni
    push_neg at hni
    obtain ⟨h0, hi0, hm0⟩ := hni
    have hle : ∀ h, (if C.IsInput h then 0 else C.mult g h) ≤
        ∑ h', (if C.IsInput h' then 0 else C.mult g h') := fun h =>
      Finset.single_le_sum (f := fun h' => if C.IsInput h' then 0 else C.mult g h')
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ h)
    have h01 : C.mult g h0 = 1 := by
      have := hle h0; rw [if_neg hi0] at this; omega
    have hoth : ∀ h, h ≠ h0 → ¬ C.IsInput h → C.mult g h = 0 := by
      intro h hne hi
      have hp := Finset.sum_le_sum_of_subset (f := fun h' => if C.IsInput h' then 0 else C.mult g h')
        (Finset.subset_univ {h0, h})
      rw [Finset.sum_pair (Ne.symm hne)] at hp
      simp only [if_neg hi0, if_neg hi] at hp
      omega
    rw [base, Finset.prod_eq_single h0, Finset.sum_eq_single h0]
    · simp [hi0, h01]
    · intro h _ hne
      by_cases hi : C.IsInput h
      · simp [hi]
      · simp [hi, hoth h hne hi]
    · simp
    · intro h _ hne
      by_cases hi : C.IsInput h
      · simp [hi]
      · simp [hi, hoth h hne hi]
    · simp

lemma mdeg_le (C : Circuit K n (Fin M)) (g : Fin M) : mdeg C g ≤ Dg C :=
  Finset.le_sup (f := mdeg C) (Finset.mem_univ g)

end Construction

section ABPBuild
open Circuit MvPolynomial
variable {K : Type} [Field K] {n M : ℕ}

def reg (C : Circuit K n (Fin M)) : Vx M (Dg C) → Vx M (Dg C) → Prop
  | .src, .gt g => C.IsInput g
  | .gt h, .gt g => C.label g = .op .add ∧ 0 < C.mult g h
  | .gt h, .ee g j => C.label g = .op .mul ∧ j.val = 0 ∧ ¬ C.IsInput h ∧ 0 < C.mult g h
  | .ee g j, .gt g' => g = g' ∧ C.label g = .op .mul ∧ j.val = mdeg C g
  | .ee g i, .ch g' j i' t s => g = g' ∧ i = i' ∧ cv C g j.val i.val s ∧ t.val = 0
  | .ch g j i t s, .ch g' j' i' t' s' => g = g' ∧ j = j' ∧ i = i' ∧ s = s' ∧
      cv C g j.val i.val s ∧ t'.val = t.val + 1 ∧ t'.val < j.val - i.val
  | .ch g j i t s, .ee g' j' => g = g' ∧ j = j' ∧ cv C g j.val i.val s ∧
      t.val + 1 = j.val - i.val
  | .gt g, .snk => g = C.out
  | _, _ => False

def lab (C : Circuit K n (Fin M)) :
    Vx M (Dg C) → Vx M (Dg C) → BorderDiffEq.AffineForm K (Fin n × Fin n)
  | .src, .gt g => inA C g
  | .src, .ee g j => ⟨if C.label g = .op .mul ∧ j.val = 0 ∧ noInt C g then 1 else 0, 0⟩
  | .gt h, .gt g => ⟨(C.mult g h : K), 0⟩
  | .gt _, .ee _ _ => ⟨1, 0⟩
  | .ee g _, .gt _ => ⟨kap C g, 0⟩
  | .ee _ _, .ch _ _ _ _ _ => ⟨1, 0⟩
  | .ch _ _ _ _ s, .ch _ _ _ _ _ => xA C s
  | .ch g j i _ s, .ee _ _ => sc (coef j.val i.val * mu C g s) (xA C s)
  | .gt g, .snk => ⟨if g = C.out then 1 else 0, 0⟩
  | _, _ => ⟨0, 0⟩

def abp (C : Circuit K n (Fin M)) : ABP K (Fin n × Fin n) (Vx M (Dg C)) where
  edge u v := reg C u v ∨ (u = .src ∧ v ≠ .src) ∨ (v = .snk ∧ u ≠ .snk)
  label := lab C
  source := .src
  sink := .snk

def Pv (C : Circuit K n (Fin M)) : Vx M (Dg C) → MvPolynomial (Fin n × Fin n) K
  | .src => 1
  | .snk => C.value C.out
  | .gt g => C.value g
  | .ee g j => if C.label g = .op .mul then base C g * eS C g j.val else 0
  | .ch g j i t s => if cv C g j.val i.val s ∧ t.val < j.val - i.val then
      base C g * eS C g i.val * vpoly C s ^ t.val else 0

def term (C : Circuit K n (Fin M)) (v u : Vx M (Dg C)) : MvPolynomial (Fin n × Fin n) K :=
  if (abp C).edge u v then Pv C u * ((abp C).label u v).toPoly else 0

lemma pathStep_term (C : Circuit K n (Fin M)) (v : Vx M (Dg C)) :
    pathStep (abp C) (Pv C) v = (if v = .src then 1 else 0) + ∑ u, term C v u := rfl

/-! ### Well-formedness -/

lemma abp_wf (C : Circuit K n (Fin M)) (hwf : C.WellFormed) : (abp C).wellFormed := by
  set D := Dg C
  have hD2 : (D + 2) * (D + 2) = (D + 2) * D + 2 * D + 4 := by ring
  let r := fun g => rk C.Wire g
  have hr : ∀ g, r g < M := fun g => by
    have := rk_lt_card C.Wire hwf.acyclic g; simpa using this
  have hrl : ∀ h g, 0 < C.mult g h → r h < r g := fun h g hw => rk_lt C.Wire hwf.acyclic hw
  have hjD : ∀ j : Fin (D + 1), (D + 2) * j.val ≤ (D + 2) * D := fun j =>
    Nat.mul_le_mul_left _ (by omega)
  refine ⟨?_, ?_, ?_⟩
  · apply acyclic_of_pot _ (fun a => match a with
      | .src => 0
      | .snk => (D + 2) * (D + 2) * M + (D + 2) * (D + 2)
      | .gt g => (D + 2) * (D + 2) * r g + (D + 2) * (D + 2) - 1
      | .ee g j => (D + 2) * (D + 2) * r g + 1 + (D + 2) * j.val
      | .ch g _ i t _ => (D + 2) * (D + 2) * r g + 2 + (D + 2) * i.val + t.val)
    intro a b hab
    have hLr : ∀ g, (D + 2) * (D + 2) * r g + (D + 2) * (D + 2) ≤ (D + 2) * (D + 2) * M := by
      intro g
      have := Nat.mul_le_mul_left ((D + 2) * (D + 2)) (hr g)
      rw [Nat.mul_succ] at this; exact this
    rcases hab with hab | ⟨rfl, hb⟩ | ⟨rfl, ha⟩
    · have hL4 : 4 ≤ (D + 2) * (D + 2) := by nlinarith
      rcases a with _ | _ | h | ⟨h, j⟩ | ⟨h, j, i, t, s⟩ <;>
        rcases b with _ | _ | g | ⟨g, j'⟩ | ⟨g, j', i', t', s'⟩ <;>
        simp only [reg] at hab <;> dsimp only
      · omega
      · have := hLr h; omega
      · have := hrl h g hab.2
        have := Nat.mul_lt_mul_of_pos_left this (show 0 < (D + 2) * (D + 2) by positivity)
        omega
      · have := hrl h g hab.2.2.2
        have := Nat.mul_le_mul_left ((D + 2) * (D + 2)) (Nat.succ_le_of_lt this)
        rw [Nat.mul_succ] at this
        have h0 : (D + 2) * j'.val = 0 := by rw [hab.2.1, mul_zero]
        omega
      · obtain ⟨rfl, -, -⟩ := hab
        have := hjD j
        omega
      · obtain ⟨rfl, rfl, -, -⟩ := hab
        omega
      · obtain ⟨rfl, rfl, hcv0, ht⟩ := hab
        have hcv := hcv0.2.2
        have hj : j.val = i.val + (t.val + 1) := by omega
        have : (D + 2) * j.val = (D + 2) * i.val + (D + 2) * (t.val + 1) := by rw [hj, mul_add]
        have : 2 * (t.val + 1) ≤ (D + 2) * (t.val + 1) := Nat.mul_le_mul_right _ (by omega)
        omega
      · obtain ⟨rfl, rfl, rfl, rfl, -, ht, -⟩ := hab
        omega
    · rcases b with _ | _ | g | ⟨g, j'⟩ | ⟨g, j', i', t', s'⟩
      · exact absurd rfl hb
      · dsimp only; positivity
      · dsimp only; have : 4 ≤ (D + 2) * (D + 2) := by nlinarith
        omega
      · dsimp only; omega
      · dsimp only; omega
    · rcases a with _ | _ | g | ⟨g, j⟩ | ⟨g, j, i, t, s⟩
      · dsimp only; positivity
      · exact absurd rfl ha
      · dsimp only; have := hLr g; have : 4 ≤ (D + 2) * (D + 2) := by nlinarith
        omega
      · dsimp only; have := hLr g; have := hjD j; omega
      · dsimp only; have := hLr g
        have := Nat.mul_le_mul_left (D + 2) (show i.val ≤ D by omega)
        have := t.isLt
        omega
  · intro v
    constructor
    · intro h
      by_contra hv
      exact h ⟨.src, Or.inr (Or.inl ⟨rfl, hv⟩)⟩
    · rintro rfl ⟨u, hu⟩
      rcases hu with hu | ⟨-, hu⟩ | ⟨hu, -⟩
      · rcases u with _ | _ | _ | _ | _ <;> simp [abp, reg] at hu
      · exact hu rfl
      · simp [abp] at hu
  · intro v
    constructor
    · intro h
      by_contra hv
      exact h ⟨.snk, Or.inr (Or.inr ⟨rfl, hv⟩)⟩
    · rintro rfl ⟨u, hu⟩
      rcases hu with hu | ⟨hu, -⟩ | ⟨-, hu⟩
      · rcases u with _ | _ | _ | _ | _ <;> simp [abp, reg] at hu
      · simp [abp] at hu
      · exact hu rfl

/-! ### The path polynomials -/

lemma term_zero_label (C : Circuit K n (Fin M)) (v u : Vx M (Dg C))
    (h : (lab C u v).toPoly = 0) : term C v u = 0 := by
  unfold term; simp [abp, h]

lemma term_noedge (C : Circuit K n (Fin M)) (v u : Vx M (Dg C))
    (h : ¬ (abp C).edge u v) : term C v u = 0 := by
  unfold term; rw [if_neg h]

lemma fix_src (C : Circuit K n (Fin M)) : Pv C .src = pathStep (abp C) (Pv C) .src := by
  rw [pathStep_term, Finset.sum_eq_zero]
  · simp [Pv]
  · intro u _
    apply term_noedge
    rcases u with _ | _ | _ | _ | _ <;> simp [abp, reg]

lemma fix_snk (C : Circuit K n (Fin M)) : Pv C .snk = pathStep (abp C) (Pv C) .snk := by
  rw [pathStep_term, Finset.sum_eq_single (Vx.gt C.out)]
  · simp [term, abp, reg, lab, Pv, toPoly_c]
  · intro u _ hu
    rcases u with _ | _ | g | _ | _
    · exact term_zero_label _ _ _ (by simp [lab, toPoly_c])
    · exact term_noedge _ _ _ (by simp [abp, reg])
    · have : g ≠ C.out := fun h => hu (by rw [h])
      exact term_zero_label _ _ _ (by simp [lab, toPoly_c, this])
    · exact term_zero_label _ _ _ (by simp [lab, toPoly_c])
    · exact term_zero_label _ _ _ (by simp [lab, toPoly_c])
  · simp

lemma fix_gt (C : Circuit K n (Fin M)) (hwf : C.WellFormed) (g : Fin M) :
    Pv C (.gt g) = pathStep (abp C) (Pv C) (.gt g) := by
  rw [pathStep_term, sum_Vx]
  have e1 : term C (.gt g) .src = inPoly C g := by
    simp [term, abp, lab, Pv, toPoly_inA]
  have e2 : term C (.gt g) .snk = 0 := term_noedge _ _ _ (by simp [abp, reg])
  have e3 : ∀ h, term C (.gt g) (.gt h) =
      if C.label g = .op .add ∧ 0 < C.mult g h then C.value h * MvPolynomial.C (C.mult g h : K)
      else 0 := by
    intro h; simp [term, abp, reg, lab, Pv, toPoly_c]
  have e4 : ∀ g' j, term C (.gt g) (.ee g' j) =
      if g' = g ∧ C.label g = .op .mul ∧ j.val = mdeg C g then
        base C g * eS C g j.val * MvPolynomial.C (kap C g) else 0 := by
    intro g' j
    by_cases hg : g' = g
    · subst hg
      by_cases hm : C.label g' = .op .mul <;> simp [term, abp, reg, lab, Pv, toPoly_c, hm]
    · simp [term, abp, reg, lab, Pv, hg]
  have e5 : ∀ g' j i t s, term C (.gt g) (.ch g' j i t s) = 0 := by
    intro g' j i t s; exact term_noedge _ _ _ (by simp [abp, reg])
  simp only [e1, e2, e3, e4, e5, Finset.sum_const_zero, add_zero, reduceCtorEq, if_false, zero_add]
  have e4' : ∑ g' : Fin M, ∑ j : Fin (Dg C + 1), (if g' = g ∧ C.label g = .op .mul ∧
      j.val = mdeg C g then base C g * eS C g j.val * MvPolynomial.C (kap C g) else 0) =
      if C.label g = .op .mul then base C g * eS C g (mdeg C g) * MvPolynomial.C (kap C g)
      else 0 := by
    rw [Finset.sum_eq_single g, Finset.sum_eq_single ⟨mdeg C g, by have := mdeg_le C g; omega⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      rintro ⟨-, -, h⟩
      exact hb (Fin.ext h)
    · simp
    · intro b _ hb
      apply Finset.sum_eq_zero
      intro j _
      rw [if_neg]
      exact fun h => hb h.1
    · simp
  rw [e4']
  simp only [Pv]
  cases hl : C.label g with
  | var i j =>
    rw [value_var C hwf hl]; simp [inPoly, hl]
  | const c =>
    rw [value_const C hwf hl]; simp [inPoly, hl]
  | op o =>
    cases o with
    | add =>
      rw [value_add C hwf hl]
      simp only [inPoly, hl, true_and, zero_add]
      rw [if_neg (by simp), add_zero]
      apply Finset.sum_congr rfl
      intro h _
      by_cases hm : 0 < C.mult g h
      · rw [if_pos hm, mul_comm]; simp
      · have : C.mult g h = 0 := by omega
        simp [this]
    | mul =>
      rw [value_mul C hwf hl, eS_top]
      simp [inPoly, hl]

lemma fix_ch (C : Circuit K n (Fin M)) (g : Fin M) (j i t : Fin (Dg C + 1)) (s : Fin M) :
    Pv C (.ch g j i t s) = pathStep (abp C) (Pv C) (.ch g j i t s) := by
  rw [pathStep_term]
  simp only [reduceCtorEq, if_false, zero_add]
  by_cases ht : t.val = 0
  · have ht' : t = 0 := Fin.ext (by simpa using ht)
    subst ht'
    rw [Finset.sum_eq_single (Vx.ee g i)]
    · by_cases hcv : cv C g j.val i.val s
      · have hm : C.label g = .op .mul := hcv.1
        have hij : i.val < j.val := hcv.2.2
        have hedge : (abp C).edge (.ee g i) (.ch g j i 0 s) := Or.inl ⟨rfl, rfl, hcv, rfl⟩
        unfold term
        rw [if_pos hedge]
        simp only [abp, lab, Pv, toPoly_c, map_one, mul_one]
        rw [if_pos hm, if_pos ⟨hcv, by simp only [Fin.val_zero]; omega⟩]
        simp
      · simp [term, abp, reg, lab, Pv, hcv]
    · intro u _ hu
      rcases u with _ | _ | _ | ⟨g', i'⟩ | ⟨g', j', i', t', s'⟩
      · exact term_zero_label _ _ _ (by simp [lab, toPoly_c])
      · exact term_noedge _ _ _ (by simp [abp, reg])
      · exact term_noedge _ _ _ (by simp [abp, reg])
      · apply term_noedge
        simp only [abp, reg, reduceCtorEq, false_and, or_false, ne_eq, not_false_eq_true,
          and_true, not_and]
        intro h1 h2
        subst h1; subst h2; exact absurd rfl hu
      · apply term_noedge
        simp only [abp, reg, reduceCtorEq, false_and, or_false, not_and]
        intro _ _ _ _ _ h; simp at h
    · simp
  · have ht1 : t.val - 1 < Dg C + 1 := by omega
    rw [Finset.sum_eq_single (Vx.ch g j i ⟨t.val - 1, ht1⟩ s)]
    · by_cases hc : cv C g j.val i.val s ∧ t.val < j.val - i.val
      · have : t.val - 1 + 1 = t.val := by omega
        have hedge : (abp C).edge (.ch g j i ⟨t.val - 1, ht1⟩ s) (.ch g j i t s) :=
          Or.inl ⟨rfl, rfl, rfl, rfl, hc.1, by first | omega | (simp only [Fin.val_mk]; omega), hc.2⟩
        unfold term
        rw [if_pos hedge]
        simp only [abp, lab, Pv, toPoly_xA]
        rw [if_pos hc, if_pos ⟨hc.1, by first | omega | (simp only [Fin.val_mk]; omega)⟩]
        rw [mul_assoc (base C g * eS C g i.val), ← pow_succ, this]
      · simp only [term, abp, reg, Pv, hc, if_false]
        rw [if_neg]
        rintro (⟨-, -, -, -, h1, h2, h3⟩ | ⟨h, -⟩ | ⟨h, -⟩)
        · exact hc ⟨h1, h3⟩
        · exact absurd h (by simp)
        · exact absurd h (by simp)
    · intro u _ hu
      rcases u with _ | _ | _ | ⟨g', i'⟩ | ⟨g', j', i', t', s'⟩
      · exact term_zero_label _ _ _ (by simp [lab, toPoly_c])
      · exact term_noedge _ _ _ (by simp [abp, reg])
      · exact term_noedge _ _ _ (by simp [abp, reg])
      · apply term_noedge
        simp [abp, reg]; intro _ _ _ h; exact ht (by rw [h]; rfl)
      · apply term_noedge
        simp only [abp, reg, reduceCtorEq, false_and, or_false, not_and]
        intro h1 h2 h3 h4 _ h5 _
        subst h1; subst h2; subst h3; subst h4
        apply hu
        congr 1
        ext; simp only; omega
    · simp

end ABPBuild

section ABPEval
open Circuit MvPolynomial
variable {K : Type} [Field K] {n M : ℕ}

lemma eS_zero (C : Circuit K n (Fin M)) (g : Fin M) : eS C g 0 = 1 := by simp [eS]

lemma fix_ee (C : Circuit K n (Fin M)) [CharZero K] (hwf : C.WellFormed) (hskew : isSkew C)
    (g : Fin M) (j : Fin (Dg C + 1)) :
    Pv C (.ee g j) = pathStep (abp C) (Pv C) (.ee g j) := by
  rw [pathStep_term, sum_Vx]
  simp only [reduceCtorEq, if_false, zero_add]
  have t_src : term C (.ee g j) .src =
      if C.label g = .op .mul ∧ j.val = 0 ∧ noInt C g then 1 else 0 := by
    unfold term
    rw [if_pos (show (abp C).edge .src (.ee g j) from Or.inr (Or.inl ⟨rfl, by simp⟩))]
    simp only [abp, lab, Pv, one_mul, toPoly_c]
    split_ifs <;> simp
  have t_snk : term C (.ee g j) .snk = 0 := term_noedge _ _ _ (by simp [abp, reg])
  have t_gt : ∀ h, term C (.ee g j) (.gt h) =
      if C.label g = .op .mul ∧ j.val = 0 ∧ ¬ C.IsInput h ∧ 0 < C.mult g h then C.value h
      else 0 := by
    intro h
    by_cases hc : C.label g = .op .mul ∧ j.val = 0 ∧ ¬ C.IsInput h ∧ 0 < C.mult g h
    · unfold term
      rw [if_pos (show (abp C).edge (.gt h) (.ee g j) from Or.inl hc), if_pos hc]
      simp [abp, lab, Pv, toPoly_c]
    · rw [if_neg hc]
      apply term_noedge
      simp only [abp, reg, reduceCtorEq, false_and, or_false, and_false]
      exact hc
  have t_ee : ∀ g' j', term C (.ee g j) (.ee g' j') = 0 := fun g' j' =>
    term_noedge _ _ _ (by simp [abp, reg])
  have t_ch : ∀ g' j' i t s, term C (.ee g j) (.ch g' j' i t s) =
      if g' = g ∧ j' = j then
        (if cv C g j.val i.val s ∧ t.val + 1 = j.val - i.val then
          base C g * eS C g i.val * vpoly C s ^ t.val *
            (MvPolynomial.C (coef j.val i.val * (mu C g s : K)) * vpoly C s) else 0)
      else 0 := by
    intro g' j' i t s
    by_cases h : g' = g ∧ j' = j
    · obtain ⟨rfl, rfl⟩ := h
      rw [if_pos ⟨rfl, rfl⟩]
      by_cases hc : cv C g' j'.val i.val s ∧ t.val + 1 = j'.val - i.val
      · unfold term
        rw [if_pos (show (abp C).edge (.ch g' j' i t s) (.ee g' j') from
          Or.inl ⟨rfl, rfl, hc.1, hc.2⟩), if_pos hc]
        simp only [abp, lab, Pv, toPoly_sc, toPoly_xA]
        rw [if_pos ⟨hc.1, by omega⟩]
      · rw [if_neg hc]
        apply term_noedge
        simp only [abp, reg, reduceCtorEq, false_and, or_false, and_false, true_and]
        exact hc
    · rw [if_neg h]
      apply term_noedge
      simp only [abp, reg, reduceCtorEq, false_and, or_false, and_false]
      rintro ⟨h1, h2, -⟩
      exact h ⟨h1, h2⟩
  simp only [t_src, t_snk, t_gt, t_ee, t_ch, Finset.sum_const_zero, add_zero]
  have hcol : ∀ F : Fin (Dg C + 1) → Fin (Dg C + 1) → Fin M → MvPolynomial (Fin n × Fin n) K,
      (∑ g' : Fin M, ∑ j' : Fin (Dg C + 1), ∑ i : Fin (Dg C + 1), ∑ t : Fin (Dg C + 1),
        ∑ s : Fin M, if g' = g ∧ j' = j then F i t s else 0) = ∑ i, ∑ t, ∑ s, F i t s := by
    intro F
    rw [Finset.sum_eq_single g, Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [hb]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  rw [hcol]
  by_cases hm : C.label g = .op .mul
  · simp only [Pv, hm, if_true, true_and]
    rcases Nat.eq_zero_or_pos j.val with hj | hj
    · have hz : ∀ (i t : Fin (Dg C + 1)) (s : Fin M), (if cv C g j.val i.val s ∧ t.val + 1 = j.val - i.val then
          base C g * eS C g i.val * vpoly C s ^ t.val *
            (MvPolynomial.C (coef j.val i.val * (mu C g s : K)) * vpoly C s) else 0) = 0 := by
        intro i t s; rw [if_neg]; rintro ⟨⟨-, -, h⟩, -⟩; omega
      simp only [hz, Finset.sum_const_zero, add_zero]
      simp only [hj, true_and, eS_zero, mul_one]
      exact base_eq C hskew hm
    · have hj0 : j.val ≠ 0 := by omega
      simp only [hj0, false_and, and_false, if_false, Finset.sum_const_zero, zero_add]
      have hi : ∀ i : Fin (Dg C + 1), (∑ t : Fin (Dg C + 1), ∑ s : Fin M,
          if cv C g j.val i.val s ∧ t.val + 1 = j.val - i.val then
            base C g * eS C g i.val * vpoly C s ^ t.val *
              (MvPolynomial.C (coef j.val i.val * (mu C g s : K)) * vpoly C s) else 0) =
          if i.val < j.val then base C g * (MvPolynomial.C (coef j.val i.val) * eS C g i.val *
            pS C g (j.val - i.val)) else 0 := by
        intro i
        by_cases hij : i.val < j.val
        · rw [if_pos hij, Finset.sum_eq_single ⟨j.val - i.val - 1, by omega⟩]
          · have h' : j.val - i.val - 1 + 1 = j.val - i.val := by omega
            simp only [cv, hm, hij, true_and, and_true, h']
            rw [pS_eq, Finset.mul_sum, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro s _
            by_cases hmu : 0 < mu C g s
            · rw [if_pos hmu]
              have hp : vpoly C s ^ (j.val - i.val) = vpoly C s ^ (j.val - i.val - 1) * vpoly C s := by
                rw [← pow_succ, h']
              rw [hp, map_mul, map_natCast]
              ring
            · have : mu C g s = 0 := by omega
              rw [if_neg hmu, this]; simp
          · intro b _ hb
            apply Finset.sum_eq_zero
            intro s _
            rw [if_neg]
            rintro ⟨-, h⟩
            exact hb (Fin.ext (by simp only; omega))
          · simp
        · rw [if_neg hij]
          apply Finset.sum_eq_zero; intro t _
          apply Finset.sum_eq_zero; intro s _
          rw [if_neg]
          rintro ⟨⟨-, -, h⟩, -⟩
          exact hij h
      rw [Finset.sum_congr rfl (fun i _ => hi i)]
      rw [Fin.sum_univ_eq_sum_range (fun k => if k < j.val then base C g *
        (MvPolynomial.C (coef j.val k) * eS C g k * pS C g (j.val - k)) else 0) (Dg C + 1)]
      rw [← Finset.sum_filter]
      have hf : (Finset.range (Dg C + 1)).filter (fun k => k < j.val) = Finset.range j.val := by
        ext k; simp only [Finset.mem_filter, Finset.mem_range]; omega
      rw [hf, ← Finset.mul_sum, ← eS_newton C g j.val (by omega)]
  · have hz : ∀ (i t : Fin (Dg C + 1)) (s : Fin M), (if cv C g j.val i.val s ∧ t.val + 1 = j.val - i.val then
        base C g * eS C g i.val * vpoly C s ^ t.val *
          (MvPolynomial.C (coef j.val i.val * (mu C g s : K)) * vpoly C s) else 0) = 0 := by
      intro i t s; rw [if_neg]; rintro ⟨⟨h, -, -⟩, -⟩; exact hm h
    simp only [hz, Finset.sum_const_zero, add_zero]
    simp [Pv, hm]

lemma abp_poly (C : Circuit K n (Fin M)) [CharZero K] (hwf : C.WellFormed) (hskew : isSkew C) :
    (abp C).polynomial = C.value C.out := by
  rw [poly_of_fixed (abp C) (abp_wf C hwf) (Pv C)]
  · rfl
  · intro v
    rcases v with _ | _ | g | ⟨g, j⟩ | ⟨g, j, i, t, s⟩
    · exact fix_src C
    · exact fix_snk C
    · exact fix_gt C hwf g
    · exact fix_ee C hwf hskew g j
    · exact fix_ch C g j i t s

end ABPEval

/-! ### Symmetry -/

section ABPSym
open Circuit MvPolynomial
variable {K : Type} [Field K] {n M : ℕ}

lemma actLabel_mul (γ γ' : Gamma n) (l : GateLabel K n) :
    actLabel (γ * γ') l = actLabel γ (actLabel γ' l) := by cases l <;> rfl

lemma actLabel_one (l : GateLabel K n) : actLabel (1 : Gamma n) l = l := by cases l <;> rfl

lemma ext_one (C : Circuit K n (Fin M)) : C.IsExtension 1 1 :=
  ⟨fun _ _ => rfl, fun g => (actLabel_one _).symm⟩

lemma ext_mul (C : Circuit K n (Fin M)) {γ γ' : Gamma n} {τ τ' : Equiv.Perm (Fin M)}
    (h : C.IsExtension γ τ) (h' : C.IsExtension γ' τ') : C.IsExtension (γ * γ') (τ * τ') := by
  refine ⟨fun g k => ?_, fun g => ?_⟩
  · simp only [Equiv.Perm.mul_apply]; rw [h.1, h'.1]
  · simp only [Equiv.Perm.mul_apply]; rw [h.2, h'.2, actLabel_mul]

lemma ext_inv (C : Circuit K n (Fin M)) {γ : Gamma n} {τ : Equiv.Perm (Fin M)}
    (h : C.IsExtension γ τ) : C.IsExtension γ⁻¹ τ⁻¹ := by
  refine ⟨fun g k => ?_, fun g => ?_⟩
  · have := h.1 (τ⁻¹ g) (τ⁻¹ k); simp only [pai] at this; exact this.symm
  · have := h.2 (τ⁻¹ g)
    simp only [pai] at this
    rw [this, ← actLabel_mul, inv_mul_cancel, actLabel_one]

lemma orbit_ext (C : Circuit K n (Fin M)) {γ : Gamma n} {τ : Equiv.Perm (Fin M)}
    (h : C.IsExtension γ τ) (g : Fin M) : C.orbit (τ g) = C.orbit g := by
  ext y
  simp only [Circuit.orbit, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨γ', σ', h', rfl⟩
    exact ⟨γ' * γ, σ' * τ, ext_mul C h' h, rfl⟩
  · rintro ⟨γ', σ', h', rfl⟩
    exact ⟨γ' * γ⁻¹, σ' * τ⁻¹, ext_mul C h' (ext_inv C h), by simp⟩

lemma mem_orbit_self (C : Circuit K n (Fin M)) (g : Fin M) : g ∈ C.orbit g := by
  simp only [Circuit.orbit, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨1, 1, ext_one C, rfl⟩

lemma out_fixed (C : Circuit K n (Fin M)) (hwf : C.WellFormed) {γ : Gamma n}
    {τ : Equiv.Perm (Fin M)} (h : C.IsExtension γ τ) : τ C.out = C.out := by
  have hno : ∀ g, C.mult g C.out = 0 := by
    intro g
    by_contra hne
    have hw : C.Wire C.out g := Nat.pos_of_ne_zero hne
    exact hwf.acyclic _ (Relation.TransGen.head' hw (hwf.reach_out g))
  have huniq : ∀ g, (∀ g', C.mult g' g = 0) → g = C.out := by
    intro g hg
    rcases Relation.ReflTransGen.cases_head (hwf.reach_out g) with h | ⟨c, hc, -⟩
    · exact h
    · exact absurd (hg c) (Nat.pos_iff_ne_zero.1 hc)
  apply huniq
  intro g'
  have := h.1 (τ⁻¹ g') C.out
  simp only [pai] at this
  rw [this, hno]

def vmap (τ : Equiv.Perm (Fin M)) {D : ℕ} : Vx M D → Vx M D
  | .src => .src
  | .snk => .snk
  | .gt g => .gt (τ g)
  | .ee g j => .ee (τ g) j
  | .ch g j i t s => .ch (τ g) j i t (τ s)

def vperm (τ : Equiv.Perm (Fin M)) (D : ℕ) : Equiv.Perm (Vx M D) where
  toFun := vmap τ
  invFun := vmap τ⁻¹
  left_inv x := by cases x <;> simp [vmap]
  right_inv x := by cases x <;> simp [vmap]

section Inv
variable (C : Circuit K n (Fin M)) {γ : Gamma n} {τ : Equiv.Perm (Fin M)}
  (h : C.IsExtension γ τ)
include h

lemma inv_input (g : Fin M) : C.IsInput (τ g) ↔ C.IsInput g := by
  unfold Circuit.IsInput; rw [h.2 g]; cases C.label g <;> simp [actLabel]

lemma inv_op (g : Fin M) (o : Op) : C.label (τ g) = .op o ↔ C.label g = .op o := by
  rw [h.2 g]; cases C.label g <;> simp [actLabel]

lemma inv_isVar (s : Fin M) : isVarB C (τ s) ↔ isVarB C s := by
  unfold isVarB; rw [h.2 s]; cases C.label s <;> simp [actLabel]

lemma inv_mu (g s : Fin M) : mu C (τ g) (τ s) = mu C g s := by
  unfold mu; rw [h.1, propext (inv_isVar C h s)]

lemma inv_mdeg (g : Fin M) : mdeg C (τ g) = mdeg C g := by
  unfold mdeg; rw [← Equiv.sum_comp τ]; simp only [inv_mu C h]

lemma inv_constOf (s : Fin M) : constOf C (τ s) = constOf C s := by
  unfold constOf; rw [h.2 s]; cases C.label s <;> simp [actLabel]

lemma inv_kap (g : Fin M) : kap C (τ g) = kap C g := by
  unfold kap; rw [← Equiv.prod_comp τ]; simp only [inv_constOf C h, h.1]

lemma inv_noInt (g : Fin M) : noInt C (τ g) ↔ noInt C g := by
  unfold noInt
  constructor
  · intro hn k hk
    have := hn (τ k) (by rwa [inv_input C h]); rwa [h.1] at this
  · intro hn k hk
    have := hn (τ⁻¹ k) (by rwa [← inv_input C h, pai])
    rw [← pai τ k, h.1]; exact this

lemma inv_cv (g : Fin M) (j i : ℕ) (s : Fin M) : cv C (τ g) j i (τ s) ↔ cv C g j i s := by
  unfold cv; rw [inv_op C h, inv_mu C h]

lemma inv_vpoly (s : Fin M) :
    vpoly C (τ s) = MvPolynomial.rename (matrixAction n γ) (vpoly C s) := by
  unfold vpoly; rw [h.2 s]; cases C.label s <;> simp [actLabel] <;> rfl

lemma inv_inPoly (g : Fin M) :
    inPoly C (τ g) = MvPolynomial.rename (matrixAction n γ) (inPoly C g) := by
  unfold inPoly; rw [h.2 g]; cases C.label g <;> simp [actLabel] <;> rfl

lemma inv_out (hwf : C.WellFormed) (g : Fin M) : τ g = C.out ↔ g = C.out := by
  conv_lhs => rw [← out_fixed C hwf h]
  exact τ.injective.eq_iff

lemma inv_reg (hwf : C.WellFormed) (u v : Vx M (Dg C)) :
    reg C (vmap τ u) (vmap τ v) ↔ reg C u v := by
  rcases u with _ | _ | k | ⟨k, j⟩ | ⟨k, j, i, t, s⟩ <;>
    rcases v with _ | _ | g | ⟨g, j'⟩ | ⟨g, j', i', t', s'⟩ <;>
    simp only [reg, vmap, inv_input C h, inv_op C h, h.1, inv_mdeg C h, inv_cv C h,
      τ.injective.eq_iff, inv_out C h hwf]

lemma inv_lab (hwf : C.WellFormed) (u v : Vx M (Dg C)) :
    (lab C (vmap τ u) (vmap τ v)).toPoly =
      MvPolynomial.rename (matrixAction n γ) (lab C u v).toPoly := by
  rcases u with _ | _ | k | ⟨k, j⟩ | ⟨k, j, i, t, s⟩ <;>
    rcases v with _ | _ | g | ⟨g, j'⟩ | ⟨g, j', i', t', s'⟩ <;>
    simp only [lab, vmap, toPoly_c, toPoly_inA, toPoly_xA, toPoly_sc, MvPolynomial.rename_C,
      inv_inPoly C h, inv_vpoly C h, inv_op C h, inv_noInt C h, h.1, inv_kap C h, inv_mu C h,
      map_mul, inv_out C h hwf]

end Inv
end ABPSym

section Final
open Circuit MvPolynomial
variable {K : Type} [Field K] {n M : ℕ}

lemma abp_ext (C : Circuit K n (Fin M)) (hwf : C.WellFormed) {γ : Gamma n}
    {τ : Equiv.Perm (Fin M)} (h : C.IsExtension γ τ) :
    (abp C).extension (matrixAction n γ) (vperm τ (Dg C)) := by
  have hsrc : ∀ u : Vx M (Dg C), vmap τ u = .src ↔ u = .src := by
    intro u; cases u <;> simp [vmap]
  have hsnk : ∀ u : Vx M (Dg C), vmap τ u = .snk ↔ u = .snk := by
    intro u; cases u <;> simp [vmap]
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro u v
    show (reg C (vmap τ u) (vmap τ v) ∨ (vmap τ u = .src ∧ vmap τ v ≠ .src) ∨
      (vmap τ v = .snk ∧ vmap τ u ≠ .snk)) ↔ _
    rw [inv_reg C h hwf]
    simp only [hsrc, hsnk, ne_eq]
    exact Iff.rfl
  · intro u v _
    exact inv_lab C h hwf u v

def tg (C : Circuit K n (Fin M)) : Vx M (Dg C) → ℕ × Finset (Fin M) × ℕ × ℕ × ℕ × Finset (Fin M)
  | .src => (0, ∅, 0, 0, 0, ∅)
  | .snk => (1, ∅, 0, 0, 0, ∅)
  | .gt g => (2, C.orbit g, 0, 0, 0, ∅)
  | .ee g j => (3, C.orbit g, j.val, 0, 0, ∅)
  | .ch g j i t s => (4, C.orbit g, j.val, i.val, t.val, C.orbit s)

lemma tg_inv (C : Circuit K n (Fin M)) {γ : Gamma n} {τ : Equiv.Perm (Fin M)}
    (h : C.IsExtension γ τ) (v : Vx M (Dg C)) : tg C (vperm τ (Dg C) v) = tg C v := by
  cases v <;> simp [tg, vperm, vmap, orbit_ext C h]

lemma orb_le (C : Circuit K n (Fin M)) (g : Fin M) : (C.orbit g).card ≤ C.maxOrb :=
  Finset.le_sup (f := fun g => (C.orbit g).card) (Finset.mem_univ g)

lemma mem_of_orbit_eq (C : Circuit K n (Fin M)) {g g' : Fin M} (h : C.orbit g' = C.orbit g) :
    g' ∈ C.orbit g := h ▸ mem_orbit_self C g'

lemma tg_fibre (C : Circuit K n (Fin M)) (B : ℕ) (hB1 : 1 ≤ B) (hB : C.maxOrb * C.maxOrb ≤ B)
    (v : Vx M (Dg C)) : (Finset.univ.filter fun w => tg C w = tg C v).card ≤ B := by
  have hm1 : C.maxOrb ≤ B := by
    rcases Nat.eq_zero_or_pos C.maxOrb with h0 | hpos
    · omega
    · exact le_trans (Nat.le_mul_of_pos_right _ hpos) hB
  rcases v with _ | _ | g | ⟨g, j⟩ | ⟨g, j, i, t, s⟩
  · refine le_trans (Finset.card_le_card (t := {Vx.src}) ?_) (by simpa using hB1)
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    cases w <;> simp_all [tg]
  · refine le_trans (Finset.card_le_card (t := {Vx.snk}) ?_) (by simpa using hB1)
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    cases w <;> simp_all [tg]
  · refine le_trans (Finset.card_le_card (t := (C.orbit g).image Vx.gt) ?_)
      (le_trans Finset.card_image_le (le_trans (orb_le C g) hm1))
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    rcases w with _ | _ | g' | _ | _ <;> simp [tg] at hw
    exact Finset.mem_image.2 ⟨g', mem_of_orbit_eq C hw, rfl⟩
  · refine le_trans (Finset.card_le_card (t := (C.orbit g).image (fun g' => Vx.ee g' j)) ?_)
      (le_trans Finset.card_image_le (le_trans (orb_le C g) hm1))
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    rcases w with _ | _ | _ | ⟨g', j'⟩ | _ <;> simp [tg] at hw
    exact Finset.mem_image.2 ⟨g', mem_of_orbit_eq C hw.1, by rw [Fin.ext hw.2]⟩
  · refine le_trans (Finset.card_le_card (t := (C.orbit g ×ˢ C.orbit s).image
      (fun p => Vx.ch p.1 j i t p.2)) ?_) (le_trans Finset.card_image_le ?_)
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      rcases w with _ | _ | _ | _ | ⟨g', j', i', t', s'⟩ <;> simp [tg] at hw
      obtain ⟨h1, h2, h3, h4, h5⟩ := hw
      refine Finset.mem_image.2 ⟨(g', s'), Finset.mem_product.2
        ⟨mem_of_orbit_eq C h1, mem_of_orbit_eq C h5⟩, ?_⟩
      simp only [Fin.ext h2, Fin.ext h3, Fin.ext h4]
    · rw [Finset.card_product]
      exact le_trans (Nat.mul_le_mul (orb_le C g) (orb_le C s)) hB

end Final

theorem skew_to_abp (K : Type) [Field K] [CharZero K] (c n : ℕ) (hn : 1 ≤ n)
    (p : MvPolynomial (Fin n × Fin n) K)
    (h : hasCircuit n p (fun C => isSkew C ∧ C.maxOrb ≤ n ^ c)) :
    ∃ m, ∃ G : ABP K (Fin n × Fin n) (Fin m),
      G.wellFormed ∧ G.symmetric (matrixAction n) ∧ G.polynomial = p ∧
      G.maxOrb (matrixAction n) ≤ n ^ (2 * c) := by
  obtain ⟨M, C, hwf, hsym, hcomp, hskew, horb⟩ := h
  have hB : C.maxOrb * C.maxOrb ≤ n ^ (2 * c) := by
    rw [two_mul, pow_add]; exact Nat.mul_le_mul horb horb
  have hB1 : 1 ≤ n ^ (2 * c) := Nat.one_le_pow _ _ (by omega)
  obtain ⟨m, G, h1, h2, h3, h4⟩ := tag_fin (abp C) (abp_wf C hwf) (by simp [abp])
    (matrixAction n) (tg C)
    (fun γ => by
      obtain ⟨τ, hτ⟩ := hsym γ
      exact ⟨vperm τ (Dg C), abp_ext C hwf hτ, tg_inv C hτ⟩)
    (n ^ (2 * c)) (fun v => by convert tg_fibre C _ hB1 hB v)
  refine ⟨m, G, h1, h2, ?_, h4⟩
  rw [h3, abp_poly C hwf hskew]
  exact hcomp

theorem lemma_6_5_main (K : Type) [Field K] [CharZero K] : symVS K ⊆ symVBP K := by
  rintro p ⟨hinv, c, N, hc⟩
  refine ⟨hinv, 2 * c, N, fun n hn hN => ?_⟩
  exact skew_to_abp K c n hn (p n) (hc n hn hN)

end SymmetricDepthHierarchy.ConstantDepth.Supplement

theorem solution (K : Type) [Field K] [CharZero K] :
    SymmetricDepthHierarchy.ConstantDepth.Supplement.symVS K ⊆
      SymmetricDepthHierarchy.ConstantDepth.Supplement.symVBP K :=
  SymmetricDepthHierarchy.ConstantDepth.Supplement.lemma_6_5_main K
