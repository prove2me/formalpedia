-- Prove2me | solution 1 for SymmetricDepthHierarchy.ConstantDepth.Supplement.lemma_6_4
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-23T14:18:43.149911+00:00
-- url     : https://prove2.me/submissions/ef5582da-2ec1-4ad9-87c4-9db44f8806fa

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

section AffineLemmas
variable {K : Type} [Field K] {X : Type} [Fintype X]

lemma toPoly_coeff_zero (ℓ : BorderDiffEq.AffineForm K X) :
    MvPolynomial.coeff 0 ℓ.toPoly = ℓ.c := by
  simp [BorderDiffEq.AffineForm.toPoly, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_X']

lemma toPoly_coeff_single (ℓ : BorderDiffEq.AffineForm K X) (l : X) :
    MvPolynomial.coeff (Finsupp.single l 1) ℓ.toPoly = ℓ.a l := by
  simp [BorderDiffEq.AffineForm.toPoly, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_X', Finsupp.single_left_inj, Finsupp.single_eq_zero]
  try (intro h; exact absurd h.symm (Finsupp.single_ne_zero.2 one_ne_zero))
  
lemma affine_rename (ℓ ℓ' : BorderDiffEq.AffineForm K X) (f : Equiv.Perm X)
    (h : ℓ'.toPoly = MvPolynomial.rename f ℓ.toPoly) :
    ℓ'.c = ℓ.c ∧ ∀ l, ℓ'.a (f l) = ℓ.a l := by
  constructor
  · have := congrArg (MvPolynomial.coeff 0) h
    have h2 := MvPolynomial.coeff_rename_mapDomain f f.injective ℓ.toPoly 0
    rw [Finsupp.mapDomain_zero] at h2
    rw [← toPoly_coeff_zero, this, h2, toPoly_coeff_zero]
  · intro l
    have := congrArg (MvPolynomial.coeff (Finsupp.single (f l) 1)) h
    have h2 := MvPolynomial.coeff_rename_mapDomain f f.injective ℓ.toPoly (Finsupp.single l 1)
    rw [Finsupp.mapDomain_single] at h2
    rw [← toPoly_coeff_single, this, h2, toPoly_coeff_single]

lemma affine_rename_conv (ℓ ℓ' : BorderDiffEq.AffineForm K X) (f : Equiv.Perm X)
    (hc : ℓ'.c = ℓ.c) (ha : ∀ l, ℓ'.a (f l) = ℓ.a l) :
    ℓ'.toPoly = MvPolynomial.rename f ℓ.toPoly := by
  unfold BorderDiffEq.AffineForm.toPoly
  simp only [map_add, map_sum, map_mul, MvPolynomial.rename_C, MvPolynomial.rename_X, hc]
  congr 1
  rw [← Equiv.sum_comp f]
  apply Finset.sum_congr rfl
  intro l _
  rw [ha]

end AffineLemmas

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

section Relabel
variable {K : Type} [Field K] {n : ℕ} {V W : Type} [Fintype V] [Fintype W]

def relabelC (C : Circuit K n V) (e : V ≃ W) : Circuit K n W where
  label w := C.label (e.symm w)
  mult w w' := C.mult (e.symm w) (e.symm w')
  out := e C.out

lemma relabel_evalStep (C : Circuit K n V) (e : V ≃ W) (f : W → MvPolynomial (Fin n × Fin n) K)
    (w : W) : (relabelC C e).evalStep f w = C.evalStep (fun v => f (e v)) (e.symm w) := by
  simp only [Circuit.evalStep, relabelC]
  split
  · rfl
  · rfl
  · refine (Equiv.sum_comp e (fun h' : W => ((C.mult (e.symm w) (e.symm h') : ℕ) :
      MvPolynomial (Fin n × Fin n) K) * f h')).symm.trans ?_
    simp
  · refine (Equiv.prod_comp e (fun h' : W => f h' ^ C.mult (e.symm w) (e.symm h'))).symm.trans ?_
    simp

lemma relabel_valueAux (C : Circuit K n V) (e : V ≃ W) (k : ℕ) (w : W) :
    (relabelC C e).valueAux k w = C.valueAux k (e.symm w) := by
  induction k generalizing w with
  | zero => rw [Circuit.valueAux, Circuit.valueAux, relabel_evalStep]
  | succ k ih =>
    rw [Circuit.valueAux, Circuit.valueAux, relabel_evalStep]
    congr 1
    funext v
    rw [ih, Equiv.symm_apply_apply]

lemma relabel_computes (C : Circuit K n V) (e : V ≃ W) (p : MvPolynomial (Fin n × Fin n) K)
    (h : C.Computes p) : (relabelC C e).Computes p := by
  unfold Circuit.Computes Circuit.value at h ⊢
  rw [← h, show (relabelC C e).out = e C.out from rfl, relabel_valueAux,
    Equiv.symm_apply_apply, Fintype.card_congr e]

lemma relabel_wf (C : Circuit K n V) (e : V ≃ W) (h : C.WellFormed) : (relabelC C e).WellFormed where
  input_no_wire g g' hg := h.input_no_wire _ _ hg
  acyclic g hg := by
    refine h.acyclic (e.symm g) ?_
    exact Relation.TransGen.lift (fun x => e.symm x) (fun a b hab => hab) _ _ hg
  input_inj g g' hg hg' hl := by
    have := h.input_inj _ _ hg hg' hl
    exact e.symm.injective this
  reach_out g := by
    have := Relation.ReflTransGen.lift' (fun x : V => e x) (r := C.Wire) (p := (relabelC C e).Wire)
      (by
        intro a b hab
        have : (relabelC C e).Wire (e a) (e b) := by
          simpa [Circuit.Wire, relabelC] using hab
        exact Relation.ReflTransGen.single this) _ _ (h.reach_out (e.symm g))
    simpa [Function.onFun, relabelC] using this

lemma relabel_skew (C : Circuit K n V) (e : V ≃ W) (h : isSkew C) : isSkew (relabelC C e) := by
  intro g hg
  have := h (e.symm g) hg
  refine le_trans (le_of_eq ?_) this
  refine (Equiv.sum_comp e (fun h' : W => if (relabelC C e).IsInput h' then 0 else
    (relabelC C e).mult g h')).symm.trans ?_
  apply Finset.sum_congr rfl
  intro x _
  have hi : (relabelC C e).IsInput (e x) ↔ C.IsInput x := by
    simp [Circuit.IsInput, relabelC]
  by_cases hx : C.IsInput x
  · rw [if_pos (hi.2 hx), if_pos hx]
  · rw [if_neg (fun h => hx (hi.1 h)), if_neg hx]
    simp [relabelC]

lemma relabel_ext (C : Circuit K n V) (e : V ≃ W) (γ : Circuit.Gamma n) (σ : Equiv.Perm V)
    (h : C.IsExtension γ σ) : (relabelC C e).IsExtension γ (e.permCongr σ) := by
  constructor
  · intro g g'
    simp [relabelC, h.1]
  · intro g
    simp [relabelC, h.2]

lemma relabel_ext' (C : Circuit K n V) (e : V ≃ W) (γ : Circuit.Gamma n) (σ : Equiv.Perm W)
    (h : (relabelC C e).IsExtension γ σ) : C.IsExtension γ (e.symm.permCongr σ) := by
  constructor
  · intro g g'
    have := h.1 (e g) (e g')
    simpa [relabelC] using this
  · intro g
    have := h.2 (e g)
    simpa [relabelC] using this

lemma relabel_sym (C : Circuit K n V) (e : V ≃ W) (h : C.MatrixSymmetric) :
    (relabelC C e).MatrixSymmetric := by
  intro γ
  obtain ⟨σ, hσ⟩ := h γ
  exact ⟨e.permCongr σ, relabel_ext C e γ σ hσ⟩

lemma relabel_maxOrb (C : Circuit K n V) (e : V ≃ W) : (relabelC C e).maxOrb ≤ C.maxOrb := by
  apply Finset.sup_le
  intro w _
  have hsub : (relabelC C e).orbit w ⊆ (C.orbit (e.symm w)).image e := by
    intro g' hg'
    simp only [Circuit.orbit, Finset.mem_filter, Finset.mem_univ, true_and] at hg'
    obtain ⟨γ, σ, hσ, rfl⟩ := hg'
    refine Finset.mem_image.2 ⟨e.symm (σ w), ?_, by simp⟩
    simp only [Circuit.orbit, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨γ, e.symm.permCongr σ, relabel_ext' C e γ σ hσ, by simp⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans
    (Finset.le_sup (f := fun g => (C.orbit g).card) (Finset.mem_univ _)))

lemma fin_transfer (C : Circuit K n V) (p : MvPolynomial (Fin n × Fin n) K) (hwf : C.WellFormed)
    (hs : C.MatrixSymmetric) (hc : C.Computes p) :
    ∃ m : ℕ, ∃ C' : Circuit K n (Fin m), C'.WellFormed ∧ C'.MatrixSymmetric ∧ C'.Computes p ∧
      (isSkew C → isSkew C') ∧ C'.maxOrb ≤ C.maxOrb :=
  ⟨Fintype.card V, relabelC C (Fintype.equivFin V), relabel_wf C _ hwf, relabel_sym C _ hs,
    relabel_computes C _ p hc, relabel_skew C _, relabel_maxOrb C _⟩
end Relabel

section Build
open SymmetricDepthHierarchy.ConstantDepth
variable {K : Type} [Field K] {n : ℕ} {V : Type} [Fintype V] (G : ABP K (Fin n × Fin n) V)

abbrev EdgeT := {p : V × V // G.edge p.1 p.2}

def coef (e : EdgeT G) : Option (Fin n × Fin n) → K
  | none => (G.label e.1.1 e.1.2).c
  | some l => (G.label e.1.1 e.1.2).a l

def cset : Finset K :=
  insert 1 (Finset.univ.image fun x : EdgeT G × Option (Fin n × Fin n) => coef G x.1 x.2)

abbrev Gate := V ⊕ ((EdgeT G × Option (Fin n × Fin n)) ⊕ ((Fin n × Fin n) ⊕ {c // c ∈ cset G}))

def gLabel : Gate G → GateLabel K n
  | .inl _ => .op .add
  | .inr (.inl _) => .op .mul
  | .inr (.inr (.inl l)) => .var l.1 l.2
  | .inr (.inr (.inr c)) => .const c.1

def gMult : Gate G → Gate G → ℕ
  | .inl v, .inr (.inl m) => if m.1.1.2 = v then 1 else 0
  | .inl v, .inr (.inr (.inr c)) => if v = G.source ∧ c.1 = 1 then 1 else 0
  | .inr (.inl m), .inl u => if m.1.1.1 = u then 1 else 0
  | .inr (.inl m), .inr (.inr (.inl l)) => if m.2 = some l then 1 else 0
  | .inr (.inl m), .inr (.inr (.inr c)) => if c.1 = coef G m.1 m.2 then 1 else 0
  | _, _ => 0

def bigC : Circuit K n (Gate G) where
  label := gLabel G
  mult := gMult G
  out := .inl G.sink

variable {G}

lemma bigC_input_no_wire (g h : Gate G) (hg : (bigC G).IsInput g) : (bigC G).mult g h = 0 := by
  rcases g with v | m | l | c <;> rcases h with u | m' | l' | c' <;>
    simp_all [Circuit.IsInput, bigC, gLabel, gMult]

lemma reach_sink (hG : G.wellFormed) (v : V) : Relation.ReflTransGen G.edge v G.sink := by
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

lemma wire_up (e : EdgeT G) (o : Option (Fin n × Fin n)) :
    (bigC G).Wire (.inl e.1.1) (.inr (.inl (e, o))) ∧ (bigC G).Wire (.inr (.inl (e, o))) (.inl e.1.2) := by
  simp [Circuit.Wire, bigC, gMult]

lemma reach_P (hG : G.wellFormed) (v : V) :
    Relation.ReflTransGen (bigC G).Wire (.inl v) (.inl G.sink) := by
  refine Relation.ReflTransGen.lift' (fun v : V => (Sum.inl v : Gate G)) ?_ _ _ (reach_sink hG v)
  intro a b hab
  have := wire_up (G := G) ⟨(a, b), hab⟩ none
  exact (Relation.ReflTransGen.single this.1).trans (Relation.ReflTransGen.single this.2)

def phi (g : Gate G) : ℕ :=
  match g with
  | .inl v => 2 * rk G.edge v + 2
  | .inr (.inl m) => 2 * rk G.edge m.1.1.1 + 3
  | .inr (.inr _) => 0

lemma phi_lt (hG : G.wellFormed) {h g : Gate G} (hw : (bigC G).Wire h g) : phi h < phi g := by
  rcases g with v | m | l | c <;> rcases h with u | m' | l' | c' <;>
    simp only [Circuit.Wire, bigC, gMult, phi] at hw ⊢ <;>
    first
    | omega
    | (simp at hw; done)
    | skip
  · obtain ⟨⟨⟨a, b⟩, he⟩, o⟩ := m'
    by_cases hb : b = v
    · subst hb
      have : rk G.edge a < rk G.edge b := rk_lt G.edge hG.1 he
      show 2 * rk G.edge a + 3 < 2 * rk G.edge b + 2
      omega
    · simp [hb] at hw
  · by_cases hb : (m.1 : V × V).1 = u
    · subst hb
      omega
    · simp [hb] at hw

lemma bigC_acyclic (hG : G.wellFormed) (g : Gate G) : ¬ Relation.TransGen (bigC G).Wire g g := by
  intro h
  have : ∀ a b, Relation.TransGen (bigC G).Wire a b → phi a < phi b := by
    intro a b hab
    induction hab with
    | single h => exact phi_lt hG h
    | tail _ h ih => exact lt_trans ih (phi_lt hG h)
  exact lt_irrefl _ (this _ _ h)


lemma bigC_reach (hG : G.wellFormed) (hne : Nonempty (EdgeT G)) (g : Gate G) :
    Relation.ReflTransGen (bigC G).Wire g (bigC G).out := by
  show Relation.ReflTransGen (bigC G).Wire g (.inl G.sink)
  have hM : ∀ m : EdgeT G × Option (Fin n × Fin n),
      Relation.ReflTransGen (bigC G).Wire (.inr (.inl m)) (.inl G.sink) := fun m =>
    (Relation.ReflTransGen.single (wire_up m.1 m.2).2).trans (reach_P hG _)
  rcases g with v | m | l | c
  · exact reach_P hG v
  · exact hM m
  · obtain ⟨e⟩ := hne
    refine Relation.ReflTransGen.head ?_ (hM (e, some l))
    simp [Circuit.Wire, bigC, gMult]
  · have hc := c.2
    unfold cset at hc
    rcases Finset.mem_insert.1 hc with h1 | h2
    · refine Relation.ReflTransGen.head ?_ (reach_P hG G.source)
      simp [Circuit.Wire, bigC, gMult, h1]
    · obtain ⟨x, _, hx⟩ := Finset.mem_image.1 h2
      refine Relation.ReflTransGen.head ?_ (hM x)
      simp [Circuit.Wire, bigC, gMult, hx]

lemma bigC_input_inj (g g' : Gate G) (hg : (bigC G).IsInput g) (hg' : (bigC G).IsInput g')
    (h : (bigC G).label g = (bigC G).label g') : g = g' := by
  rcases g with v | m | l | c <;> rcases g' with u | m' | l' | c' <;>
    simp_all [Circuit.IsInput, bigC, gLabel]
  · exact Prod.ext h.1 h.2
  
lemma bigC_wf (hG : G.wellFormed) (hne : Nonempty (EdgeT G)) : (bigC G).WellFormed where
  input_no_wire := bigC_input_no_wire
  acyclic := bigC_acyclic hG
  input_inj := bigC_input_inj
  reach_out := bigC_reach hG hne

lemma bigC_skew : isSkew (bigC G) := by
  intro g hg
  rcases g with v | m | l | c
  · simp [bigC, gLabel] at hg
  · simp [Fintype.sum_sum_type, Circuit.IsInput, bigC, gMult, gLabel]
  · simp [bigC, gLabel] at hg
  · simp [bigC, gLabel] at hg

def optPoly : Option (Fin n × Fin n) → MvPolynomial (Fin n × Fin n) K
  | none => 1
  | some l => MvPolynomial.X l

def fval (g : Gate G) : MvPolynomial (Fin n × Fin n) K :=
  match g with
  | .inl v => G.pathAux (Fintype.card V) v
  | .inr (.inl m) => G.pathAux (Fintype.card V) m.1.1.1 *
      (MvPolynomial.C (coef G m.1 m.2) * optPoly m.2)
  | .inr (.inr (.inl l)) => MvPolynomial.X l
  | .inr (.inr (.inr c)) => MvPolynomial.C c.1

lemma toPoly_eq (ℓ : BorderDiffEq.AffineForm K (Fin n × Fin n)) :
    ℓ.toPoly = MvPolynomial.C ℓ.c + ∑ l, MvPolynomial.C (ℓ.a l) * MvPolynomial.X l := rfl

lemma fval_P (hG : G.wellFormed) (v : V) :
    fval (G := G) (.inl v) = (bigC G).evalStep fval (.inl v) := by
  have h := pathAux_fixed G hG v
  simp only [Circuit.evalStep, bigC, gLabel, Fintype.sum_sum_type]
  simp only [fval, gMult]
  rw [h]
  unfold pathStep
  simp only [Nat.cast_zero, zero_mul, Finset.sum_const_zero, zero_add]
  have hS : ∑ c : {c // c ∈ cset G},
      ((if v = G.source ∧ c.1 = 1 then 1 else 0 : ℕ) : MvPolynomial (Fin n × Fin n) K) *
        MvPolynomial.C c.1 = if v = G.source then 1 else 0 := by
    have h1 : (1 : K) ∈ cset G := Finset.mem_insert_self _ _
    have := Finset.sum_coe_sort (cset G) (fun c : K =>
      ((if v = G.source ∧ c = 1 then 1 else 0 : ℕ) : MvPolynomial (Fin n × Fin n) K) *
        MvPolynomial.C c)
    rw [this]
    by_cases hv : v = G.source
    · simp [hv, h1]
    · simp [hv]
  rw [hS, add_comm]
  congr 1
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_option]
  rw [sum_subtype_dite (fun p : V × V => G.edge p.1 p.2), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.sum_eq_single v]
  · by_cases he : G.edge u v
    · simp only [he, dif_pos, if_true, Nat.cast_one, one_mul, toPoly_eq, optPoly, coef, mul_one,
        mul_add, Finset.mul_sum, mul_assoc]
    · simp [he]
  · intro w _ hw
    by_cases he : G.edge u w
    · simp [he, hw]
    · simp [he]
  · simp

lemma fval_M (m : EdgeT G × Option (Fin n × Fin n)) :
    fval (G := G) (.inr (.inl m)) = (bigC G).evalStep fval (.inr (.inl m)) := by
  simp only [Circuit.evalStep, bigC, gLabel, Fintype.prod_sum_type]
  simp only [gMult, pow_zero, Finset.prod_const_one, mul_one, one_mul, fval, pow_ite, pow_one]
  rw [Finset.prod_ite_eq]
  have hc : ∏ c : {c // c ∈ cset G}, (if c.1 = coef G m.1 m.2 then MvPolynomial.C c.1
      else (1 : MvPolynomial (Fin n × Fin n) K)) = MvPolynomial.C (coef G m.1 m.2) := by
    have := Finset.prod_coe_sort (cset G) (fun c : K =>
      if c = coef G m.1 m.2 then MvPolynomial.C c else (1 : MvPolynomial (Fin n × Fin n) K))
    rw [this, Finset.prod_ite_eq']
    have : coef G m.1 m.2 ∈ cset G := by
      unfold cset
      exact Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨(m.1, m.2), Finset.mem_univ _, rfl⟩)
    simp [this]
  have hv : ∏ l : Fin n × Fin n, (if m.2 = some l then MvPolynomial.X l
      else (1 : MvPolynomial (Fin n × Fin n) K)) = optPoly m.2 := by
    rcases m.2 with _ | l0
    · simp [optPoly]
    · simp [optPoly]
  rw [hc, hv]
  simp only [Finset.mem_univ, if_true]
  ring

lemma fval_fixed (hG : G.wellFormed) (g : Gate G) :
    fval (G := G) g = (bigC G).evalStep fval g := by
  rcases g with v | m | l | c
  · exact fval_P hG v
  · exact fval_M m
  · simp [Circuit.evalStep, bigC, gLabel, fval]
  · simp [Circuit.evalStep, bigC, gLabel, fval]


lemma bigC_computes (hG : G.wellFormed) : (bigC G).Computes G.polynomial := by
  have heq := fixed_unique (bigC G).Wire (bigC_acyclic hG) (bigC G).evalStep
    (evalStep_loc (bigC G)) fval (bigC G).value (fval_fixed hG) (value_fixed (bigC G) (bigC_acyclic hG))
  show (bigC G).value (.inl G.sink) = _
  rw [← congrFun heq]
  rfl

section Symm
variable {f : Equiv.Perm (Fin n × Fin n)} {σ : Equiv.Perm V}

lemma ext_coef (hext : G.extension f σ) (e : EdgeT G) (he : G.edge (σ e.1.1) (σ e.1.2))
    (o : Option (Fin n × Fin n)) :
    coef G ⟨(σ e.1.1, σ e.1.2), he⟩ (o.map f) = coef G e o := by
  obtain ⟨hc, ha⟩ := affine_rename _ _ f (hext.2.2.2 _ _ e.2)
  cases o <;> simp [coef, hc, ha]

def emapEdge (hext : G.extension f σ) (e : EdgeT G) : EdgeT G :=
  ⟨(σ e.1.1, σ e.1.2), (hext.2.2.1 _ _).2 e.2⟩

def emap (hext : G.extension f σ) : Gate G → Gate G
  | .inl v => .inl (σ v)
  | .inr (.inl m) => .inr (.inl (emapEdge hext m.1, m.2.map f))
  | .inr (.inr (.inl l)) => .inr (.inr (.inl (f l)))
  | .inr (.inr (.inr c)) => .inr (.inr (.inr c))

lemma emap_inj (hext : G.extension f σ) : Function.Injective (emap hext) := by
  intro a b h
  rcases a with v | m | l | c <;> rcases b with u | m' | l' | c' <;>
    simp [emap] at h
  · rw [h]
  · obtain ⟨h1, h2⟩ := h
    have h1' := congrArg Subtype.val h1
    simp [emapEdge] at h1'
    have : m.1 = m'.1 := Subtype.ext (Prod.ext h1'.1 h1'.2)
    have h3 : m.2 = m'.2 := Option.map_injective f.injective h2
    rw [Prod.ext this h3]
  · rw [h]
  · rw [h]

lemma emap_mult (hext : G.extension f σ) (g h : Gate G) :
    gMult G (emap hext g) (emap hext h) = gMult G g h := by
  rcases g with v | m | l | c <;> rcases h with u | m' | l' | c' <;>
    simp [emap, gMult, emapEdge]
  · have h1 : σ v = G.source ↔ v = G.source := by
      constructor
      · intro h; apply σ.injective; rw [h, hext.1]
      · intro h; rw [h, hext.1]
    simp [h1]
  · rw [ext_coef hext m.1 ((hext.2.2.1 _ _).2 m.1.2) m.2]

def emapPerm (hext : G.extension f σ) : Equiv.Perm (Gate G) :=
  Equiv.ofBijective (emap hext) (Finite.injective_iff_bijective.1 (emap_inj hext))

lemma emap_label (γ : Circuit.Gamma n) (hf : f = matrixAction n γ) (hext : G.extension f σ)
    (g : Gate G) : gLabel G (emap hext g) = Circuit.actLabel γ (gLabel G g) := by
  rcases g with v | m | l | c
  · rfl
  · rfl
  · subst hf
    simp [emap, gLabel, Circuit.actLabel, matrixAction]
    exact ⟨rfl, rfl⟩
  · rfl

lemma emapPerm_ext (γ : Circuit.Gamma n) (hf : f = matrixAction n γ) (hext : G.extension f σ) :
    (bigC G).IsExtension γ (emapPerm hext) :=
  ⟨fun g h => emap_mult hext g h, fun g => emap_label γ hf hext g⟩

lemma bigC_symm (hsym : G.symmetric (matrixAction n)) : (bigC G).MatrixSymmetric := by
  intro γ
  obtain ⟨σ, hσ⟩ := hsym γ
  exact ⟨emapPerm hσ, emapPerm_ext γ rfl hσ⟩

lemma inj_fwd_iff {W : Type} [Fintype W] (R : W → W → Prop) (s : W → W) (hs : Function.Injective s)
    (h : ∀ u v, R u v → R (s u) (s v)) : ∀ u v, R (s u) (s v) → R u v := by
  let F : {p : W × W // R p.1 p.2} → {p : W × W // R p.1 p.2} :=
    fun p => ⟨(s p.1.1, s p.1.2), h _ _ p.2⟩
  have hF : Function.Injective F := by
    intro p q hpq
    have := congrArg Subtype.val hpq
    simp only [F, Prod.mk.injEq] at this
    exact Subtype.ext (Prod.ext (hs this.1) (hs this.2))
  have hS : Function.Surjective F := Finite.injective_iff_surjective.1 hF
  intro u v huv
  obtain ⟨p, hp⟩ := hS ⟨(s u, s v), huv⟩
  have := congrArg Subtype.val hp
  simp only [F, Prod.mk.injEq] at this
  have e1 := hs this.1
  have e2 := hs this.2
  have := p.2
  rw [e1, e2] at this
  exact this

section Orbit
variable {γ : Circuit.Gamma n} {σ' : Equiv.Perm (Gate G)}

lemma ext_inl (hσ' : (bigC G).IsExtension γ σ') (v : V) : ∃ w, σ' (.inl v) = .inl w := by
  have h := hσ'.2 (.inl v)
  generalize σ' (.inl v) = g' at h ⊢
  rcases g' with w | m | l | c
  · exact ⟨w, rfl⟩
  all_goals simp [bigC, gLabel, Circuit.actLabel] at h

lemma ext_var (hσ' : (bigC G).IsExtension γ σ') (l : Fin n × Fin n) :
    σ' (.inr (.inr (.inl l))) = .inr (.inr (.inl (matrixAction n γ l))) := by
  have h := hσ'.2 (.inr (.inr (.inl l)))
  generalize σ' (.inr (.inr (.inl l))) = g' at h ⊢
  rcases g' with w | m | l' | c
  all_goals simp [bigC, gLabel, Circuit.actLabel] at h
  obtain ⟨h1, h2⟩ := h
  have e : l' = (γ.1 l.1, γ.2 l.2) := Prod.ext h1 h2
  rw [e]
  rfl

lemma ext_const (hσ' : (bigC G).IsExtension γ σ') (c : {c // c ∈ cset G}) :
    σ' (.inr (.inr (.inr c))) = .inr (.inr (.inr c)) := by
  have h := hσ'.2 (.inr (.inr (.inr c)))
  generalize σ' (.inr (.inr (.inr c))) = g' at h ⊢
  rcases g' with w | m | l' | c'
  all_goals simp [bigC, gLabel, Circuit.actLabel] at h
  have e : c' = c := by first | exact h | exact Subtype.ext h
  rw [e]

lemma ext_M (hσ' : (bigC G).IsExtension γ σ') (m : EdgeT G × Option (Fin n × Fin n)) :
    ∃ m', σ' (.inr (.inl m)) = .inr (.inl m') := by
  have h := hσ'.2 (.inr (.inl m))
  generalize σ' (.inr (.inl m)) = g' at h ⊢
  rcases g' with w | m' | l' | c'
  · simp [bigC, gLabel, Circuit.actLabel] at h
  · exact ⟨m', rfl⟩
  all_goals simp [bigC, gLabel, Circuit.actLabel] at h

lemma const_mem (e : EdgeT G) (o : Option (Fin n × Fin n)) : coef G e o ∈ cset G := by
  unfold cset
  exact Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨(e, o), Finset.mem_univ _, rfl⟩)

lemma ext_M_data (hσ' : (bigC G).IsExtension γ σ') (ς : V → V)
    (hς : ∀ v, σ' (.inl v) = .inl (ς v)) (e : EdgeT G) (o : Option (Fin n × Fin n)) :
    ∃ m' : EdgeT G × Option (Fin n × Fin n), σ' (.inr (.inl (e, o))) = .inr (.inl m') ∧
      m'.1.1.1 = ς e.1.1 ∧ m'.1.1.2 = ς e.1.2 ∧ m'.2 = o.map (matrixAction n γ) ∧
      coef G m'.1 m'.2 = coef G e o := by
  obtain ⟨m', hm'⟩ := ext_M hσ' (e, o)
  have hm := hσ'.1
  have e1 := hm (.inr (.inl (e, o))) (.inl e.1.1)
  rw [hm', hς] at e1
  have e2 := hm (.inl e.1.2) (.inr (.inl (e, o)))
  rw [hm', hς] at e2
  have e4 := hm (.inr (.inl (e, o))) (.inr (.inr (.inr ⟨coef G e o, const_mem e o⟩)))
  rw [hm', ext_const hσ'] at e4
  simp [bigC, gMult] at e1 e2 e4
  refine ⟨m', hm', e1, e2, ?_, e4.symm⟩
  rcases o with _ | l
  · rcases h : m'.2 with _ | l'
    · rfl
    · exfalso
      have e5 := hm (.inr (.inl (e, none))) (.inr (.inr (.inl ((matrixAction n γ).symm l'))))
      rw [hm', ext_var hσ'] at e5
      simp [bigC, gMult, h] at e5
  · have e5 := hm (.inr (.inl (e, some l))) (.inr (.inr (.inl l)))
    rw [hm', ext_var hσ'] at e5
    simp [bigC, gMult] at e5
    simp [e5]

lemma ext_induced (hG : G.wellFormed) (hσ' : (bigC G).IsExtension γ σ') :
    ∃ σ : Equiv.Perm V, G.extension (matrixAction n γ) σ ∧ (∀ v, σ' (.inl v) = .inl (σ v)) := by
  choose ς hς using ext_inl hσ'
  have hinj : Function.Injective ς := by
    intro a b h
    have := σ'.injective ((hς a).trans ((congrArg Sum.inl h).trans (hς b).symm))
    exact Sum.inl_injective this
  let σ : Equiv.Perm V := Equiv.ofBijective ς (Finite.injective_iff_bijective.1 hinj)
  have hσ : ∀ v, σ v = ς v := fun v => rfl
  have hm := hσ'.1
  have hsrc : ς G.source = G.source := by
    have e := hm (.inl G.source) (.inr (.inr (.inr ⟨1, Finset.mem_insert_self _ _⟩)))
    rw [hς, ext_const hσ'] at e
    simpa [bigC, gMult] using e
  have hfwd : ∀ u v, G.edge u v → G.edge (ς u) (ς v) := by
    intro u v h
    obtain ⟨m', _, h1, h2, _, _⟩ := ext_M_data hσ' ς hς ⟨(u, v), h⟩ none
    have := m'.1.2
    rw [h1, h2] at this
    exact this
  have hiff := inj_fwd_iff G.edge ς hinj hfwd
  have hsink : ς G.sink = G.sink := by
    apply (hG.2.2 (ς G.sink)).1
    rintro ⟨w, hw⟩
    obtain ⟨w', rfl⟩ := σ.surjective w
    have : G.edge G.sink w' := hiff _ _ hw
    exact ((hG.2.2 G.sink).2 rfl) ⟨w', this⟩
  have hlab : ∀ u v, G.edge u v →
      (G.label (ς u) (ς v)).c = (G.label u v).c ∧
      ∀ l, (G.label (ς u) (ς v)).a (matrixAction n γ l) = (G.label u v).a l := by
    intro u v h
    constructor
    · obtain ⟨m', _, h1, h2, h3, h4⟩ := ext_M_data hσ' ς hς ⟨(u, v), h⟩ none
      obtain ⟨⟨⟨a, b⟩, hab⟩, o⟩ := m'
      simp only at h1 h2 h3
      subst h3
      simp only [coef] at h4
      subst h1 h2
      exact h4
    · intro l
      obtain ⟨m', _, h1, h2, h3, h4⟩ := ext_M_data hσ' ς hς ⟨(u, v), h⟩ (some l)
      obtain ⟨⟨⟨a, b⟩, hab⟩, o⟩ := m'
      simp only at h1 h2 h3
      simp only [Option.map_some] at h3
      subst h3
      simp only [coef] at h4
      subst h1 h2
      exact h4
  refine ⟨σ, ⟨hsrc, hsink, fun u v => ?_, fun u v h => ?_⟩, hς⟩
  · rw [hσ, hσ]
    exact ⟨hiff u v, hfwd u v⟩
  · rw [hσ, hσ]
    exact affine_rename_conv _ _ (matrixAction n γ) (hlab u v h).1 (hlab u v h).2
end Orbit

def aorbG (G : ABP K (Fin n × Fin n) V) {H : Type} [Group H]
    (ρ : H →* Equiv.Perm (Fin n × Fin n)) (v : V) : Finset V :=
  Finset.univ.filter fun w => ∃ γ σ, G.extension (ρ γ) σ ∧ σ v = w

lemma aorbG_card_le (G : ABP K (Fin n × Fin n) V) {H : Type} [Group H]
    (ρ : H →* Equiv.Perm (Fin n × Fin n)) (v : V) :
    (aorbG G ρ v).card ≤ G.maxOrb ρ := by
  unfold ABP.maxOrb
  exact Finset.le_sup (f := fun v => (aorbG G ρ v).card) (Finset.mem_univ v)

def aorb (G : ABP K (Fin n × Fin n) V) (v : V) : Finset V := aorbG G (matrixAction n) v

lemma aorb_card_le (v : V) : (aorb G v).card ≤ G.maxOrb (matrixAction n) :=
  aorbG_card_le G _ v

def projM : Gate G → V × V × Option (Fin n × Fin n)
  | .inr (.inl m) => (m.1.1.1, m.1.1.2, m.2)
  | _ => (G.source, G.source, none)

lemma orbit_card_le (hG : G.wellFormed) (g : Gate G) :
    ((bigC G).orbit g).card ≤ G.maxOrb (matrixAction n) * G.maxOrb (matrixAction n) * (n * n + 1)
      + G.maxOrb (matrixAction n) + n * n + 1 := by
  have hA : ∀ v, (aorb G v).card ≤ G.maxOrb (matrixAction n) := aorb_card_le
  generalize G.maxOrb (matrixAction n) = B at hA ⊢
  rcases g with v | m | l | c
  · have hsub : (bigC G).orbit (.inl v) ⊆ (aorb G v).image Sum.inl := by
      intro g' hg'
      simp only [Circuit.orbit, Finset.mem_filter, Finset.mem_univ, true_and] at hg'
      obtain ⟨γ, σ', hext, rfl⟩ := hg'
      obtain ⟨σ, hσ, hς⟩ := ext_induced hG hext
      rw [hς]
      have hmem : σ v ∈ aorb G v := by
        simp only [aorb, aorbG, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨γ, σ, hσ, rfl⟩
      exact Finset.mem_image.2 ⟨σ v, hmem, rfl⟩
    have h1 := Finset.card_le_card hsub
    have h2 : (Finset.image (Sum.inl : V → Gate G) (aorb G v)).card ≤ (aorb G v).card :=
      Finset.card_image_le
    have h4 := hA v
    have h3 : B ≤ B * B * (n * n + 1) + B + n * n + 1 := by omega
    exact le_trans h1 (le_trans h2 (le_trans h4 h3))
  · obtain ⟨e, o⟩ := m
    have hsub : ∀ g' ∈ (bigC G).orbit (.inr (.inl (e, o))),
        projM g' ∈ (aorb G e.1.1) ×ˢ (aorb G e.1.2) ×ˢ (Finset.univ : Finset (Option (Fin n × Fin n))) := by
      intro g' hg'
      simp only [Circuit.orbit, Finset.mem_filter, Finset.mem_univ, true_and] at hg'
      obtain ⟨γ, σ', hext, rfl⟩ := hg'
      obtain ⟨σ, hσ, hς⟩ := ext_induced hG hext
      obtain ⟨m', hm', h1, h2, h3, _⟩ := ext_M_data hext σ hς e o
      rw [hm']
      simp only [projM, Finset.mem_product, Finset.mem_univ, and_true, h1, h2, aorb, aorbG,
        Finset.mem_filter, true_and]
      exact ⟨⟨γ, σ, hσ, rfl⟩, ⟨γ, σ, hσ, rfl⟩⟩
    have hinj : Set.InjOn projM (((bigC G).orbit (.inr (.inl (e, o))) : Finset (Gate G)) : Set (Gate G)) := by
      intro a ha b hb hab
      have ha := Finset.mem_coe.1 ha
      have hb := Finset.mem_coe.1 hb
      simp only [Circuit.orbit, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      obtain ⟨γ, σ', hext, ha'⟩ := ha
      obtain ⟨γ2, σ2, hext2, hb'⟩ := hb
      obtain ⟨m', hm'⟩ := ext_M hext (e, o)
      obtain ⟨m2, hm2⟩ := ext_M hext2 (e, o)
      rw [← ha', ← hb', hm', hm2] at hab ⊢
      simp only [projM, Prod.mk.injEq] at hab
      obtain ⟨h1, h2, h3⟩ := hab
      have : m' = m2 := Prod.ext (Subtype.ext (Prod.ext h1 h2)) h3
      rw [this]
    have := Finset.card_le_card_of_injOn projM hsub hinj
    rw [Finset.card_product, Finset.card_product, Finset.card_univ, Fintype.card_option,
      Fintype.card_prod, Fintype.card_fin] at this
    have h1 := hA e.1.1
    have h2 := hA e.1.2
    have h3 : B * (B * (n * n + 1)) = B * B * (n * n + 1) := (Nat.mul_assoc _ _ _).symm
    have h6 := Nat.mul_le_mul h1 (Nat.mul_le_mul h2 (le_refl (n * n + 1)))
    have h7 : B * B * (n * n + 1) ≤ B * B * (n * n + 1) + B + n * n + 1 := by omega
    exact le_trans this (le_trans h6 (h3 ▸ h7))
  · have hsub : (bigC G).orbit (.inr (.inr (.inl l))) ⊆
        (Finset.univ : Finset (Fin n × Fin n)).image (fun l => (Sum.inr (Sum.inr (Sum.inl l)) : Gate G)) := by
      intro g' hg'
      simp only [Circuit.orbit, Finset.mem_filter, Finset.mem_univ, true_and] at hg'
      obtain ⟨γ, σ', hext, rfl⟩ := hg'
      rw [ext_var hext]
      exact Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩
    have h5 := (Finset.card_le_card hsub).trans (Finset.card_image_le)
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at h5
    have h8 : n * n ≤ B * B * (n * n + 1) + B + n * n + 1 := by omega
    exact le_trans h5 h8
  · have hsub : (bigC G).orbit (.inr (.inr (.inr c))) ⊆ {.inr (.inr (.inr c))} := by
      intro g' hg'
      simp only [Circuit.orbit, Finset.mem_filter, Finset.mem_univ, true_and] at hg'
      obtain ⟨γ, σ', hext, rfl⟩ := hg'
      rw [ext_const hext]
      simp
    have h5 := Finset.card_le_card hsub
    rw [Finset.card_singleton] at h5
    have h8 : 1 ≤ B * B * (n * n + 1) + B + n * n + 1 := by omega
    exact le_trans h5 h8

lemma bigC_maxOrb (hG : G.wellFormed) :
    (bigC G).maxOrb ≤ G.maxOrb (matrixAction n) * G.maxOrb (matrixAction n) * (n * n + 1)
      + G.maxOrb (matrixAction n) + n * n + 1 :=
  Finset.sup_le fun g _ => orbit_card_le hG g

lemma noEdge_poly (hG : G.wellFormed) (hne : ¬ Nonempty (EdgeT G)) : G.polynomial = 1 := by
  have h := pathAux_fixed G hG G.sink
  unfold ABP.polynomial
  rw [h]
  unfold pathStep
  have h1 : ∀ u, ¬ G.edge u G.sink := fun u hu => hne ⟨⟨(u, G.sink), hu⟩⟩
  have h2 : G.sink = G.source := (hG.2.1 G.sink).1 (fun ⟨u, hu⟩ => h1 u hu)
  have h3 : ∑ u, (if G.edge u G.sink then G.pathAux (Fintype.card V) u * (G.label u G.sink).toPoly
      else 0) = 0 := Finset.sum_eq_zero (fun u _ => by simp [h1 u])
  rw [h3, h2]
  simp

def unitC : Circuit K n Unit where
  label _ := .const 1
  mult _ _ := 0
  out := ()

lemma unitC_all : ∃ m : ℕ, ∃ C : Circuit K n (Fin m), C.WellFormed ∧ C.MatrixSymmetric ∧
    C.Computes 1 ∧ isSkew C ∧ C.maxOrb ≤ 1 := by
  have hwf : (unitC (K := K) (n := n)).WellFormed := by
    refine ⟨fun g h _ => rfl, ?_, fun g g' _ _ _ => rfl, fun g => ?_⟩
    · intro g hg
      induction hg with
      | single h => simp [Circuit.Wire, unitC] at h
      | tail _ h _ => simp [Circuit.Wire, unitC] at h
    · cases g
      exact Relation.ReflTransGen.refl
  have hsym : (unitC (K := K) (n := n)).MatrixSymmetric := by
    intro γ
    exact ⟨1, fun g h => rfl, fun g => rfl⟩
  have hc : (unitC (K := K) (n := n)).Computes 1 := by
    simp [Circuit.Computes, Circuit.value, Circuit.valueAux, Circuit.evalStep, unitC]
  have hsk : isSkew (unitC (K := K) (n := n)) := by
    intro g hg
    simp [unitC] at hg
  have hor : (unitC (K := K) (n := n)).maxOrb ≤ 1 := by
    apply Finset.sup_le
    intro g _
    calc ((unitC (K := K) (n := n)).orbit g).card ≤ (Finset.univ : Finset Unit).card :=
          Finset.card_le_card (Finset.subset_univ _)
      _ = 1 := by simp
  obtain ⟨m, C', h1, h2, h3, h4, h5⟩ := fin_transfer _ _ hwf hsym hc
  exact ⟨m, C', h1, h2, h3, h4 hsk, h5.trans hor⟩

lemma abp_to_circuit (hG : G.wellFormed) (hsym : G.symmetric (matrixAction n)) :
    ∃ m : ℕ, ∃ C : Circuit K n (Fin m), C.WellFormed ∧ C.MatrixSymmetric ∧
      C.Computes G.polynomial ∧ isSkew C ∧
      C.maxOrb ≤ G.maxOrb (matrixAction n) * G.maxOrb (matrixAction n) * (n * n + 1)
        + G.maxOrb (matrixAction n) + n * n + 1 := by
  by_cases hne : Nonempty (EdgeT G)
  · obtain ⟨m, C', h1, h2, h3, h4, h5⟩ := fin_transfer (bigC G) G.polynomial (bigC_wf hG hne)
      (bigC_symm hsym) (bigC_computes hG)
    exact ⟨m, C', h1, h2, h3, h4 bigC_skew, h5.trans (bigC_maxOrb hG)⟩
  · rw [noEdge_poly hG hne]
    obtain ⟨m, C, h1, h2, h3, h4, h5⟩ := unitC_all (K := K) (n := n)
    exact ⟨m, C, h1, h2, h3, h4, h5.trans (by omega)⟩

lemma bound_arith (B t n : ℕ) (hB : B ≤ t) (ht : 1 ≤ t) (hn : 2 ≤ n) :
    B * B * (n * n + 1) + B + n * n + 1 ≤ t * t * n ^ 4 := by
  have h1 : B * B ≤ t * t := Nat.mul_le_mul hB hB
  have h2 : B * B * (n * n + 1) ≤ t * t * (n * n + 1) := Nat.mul_le_mul h1 le_rfl
  have h3 : t ≤ t * t := Nat.le_mul_self t
  have h4 : 1 ≤ t * t := Nat.one_le_iff_ne_zero.2 (by positivity)
  have h5 : n * n ≤ t * t * (n * n) := Nat.le_mul_of_pos_left _ h4
  have h8 : 4 ≤ n * n := by nlinarith
  have h9 : n ^ 4 = n * n * (n * n) := by ring
  have h6 : 2 * n * n + 3 ≤ n ^ 4 := by rw [h9]; nlinarith
  have h7 : t * t * (2 * n * n + 3) ≤ t * t * n ^ 4 := Nat.mul_le_mul le_rfl h6
  nlinarith

end Symm
end Build

theorem lemma_6_4_aux (K : Type) [Field K] [CharZero K] : symVBP K ⊆ symVS K := by
  rintro p ⟨hinv, c, N, h⟩
  refine ⟨hinv, 2 * c + 4, max N 2, fun n hn hNn => ?_⟩
  obtain ⟨m, G, hwf, hsym, hpoly, horb⟩ := h n hn (le_trans (le_max_left _ _) hNn)
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hNn
  obtain ⟨m', C, h1, h2, h3, h4, h5⟩ := abp_to_circuit hwf hsym
  refine ⟨m', C, h1, h2, by rw [← hpoly]; exact h3, h4, ?_⟩
  have ht : 1 ≤ n ^ c := Nat.one_le_pow _ _ (by omega)
  have := bound_arith _ _ n horb ht hn2
  refine h5.trans (this.trans (le_of_eq ?_))
  rw [← pow_add, show 2 * c + 4 = c + c + 4 by ring, pow_add, pow_add]
  ring

end SymmetricDepthHierarchy.ConstantDepth.Supplement

theorem solution (K : Type) [Field K] [CharZero K] :
    SymmetricDepthHierarchy.ConstantDepth.Supplement.symVBP K ⊆
      SymmetricDepthHierarchy.ConstantDepth.Supplement.symVS K :=
  SymmetricDepthHierarchy.ConstantDepth.Supplement.lemma_6_4_aux K
