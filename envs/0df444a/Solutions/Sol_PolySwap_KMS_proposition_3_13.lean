-- Prove2me | solution 1 for PolySwap.KMS.proposition_3_13
-- status  : ACCEPTED   (prove)
-- author  : @typh
-- created : 2026-11-16T21:53:07.634605+00:00
-- url     : https://prove2.me/submissions/a4be457c-545e-4edc-88f0-90c92fff685e

import Mathlib
import Definitions.Def_PolySwap_KMS_Complex
import Definitions.Def_PolySwap_KMS_Cohomology
import Definitions.Def_PolySwap_KMS_Cone
import Definitions.Def_PolySwap_KMS_Dehn
import Definitions.Def_PolySwap_KMS_KMSComplex
import Theorems.Thm_PolySwap_KMS_theorem_3_19
import Theorems.Thm_PolySwap_KMS_lemma_3_17
import Theorems.Thm_PolySwap_KMS_proposition_7_1
import Theorems.Thm_PolySwap_KMS_lemma_6_1
import Theorems.Thm_PolySwap_KMS_lemma_7_2

section Part_ConeAux

set_option autoImplicit false

open Classical

noncomputable section

set_option linter.unusedSectionVars false

namespace PolySwap.KMS.P313.ConeAux

open PolySwap.KMS WComplex

section General

variable {V : Type*} (X : WComplex V) (v₀ : V) {Λ : Type*} [Group Λ]

lemma face_sub {s t : Finset V} (h : X.IsFace t) (hst : s ⊆ t) : X.IsFace s := by
  obtain ⟨τ, hτ, hs⟩ := h
  exact ⟨τ, hτ, hst.trans hs⟩

lemma vert_of_face {s : Finset V} (h : X.IsFace s) {x : V} (hx : x ∈ s) : x ∈ X.vertices := by
  obtain ⟨τ, hτ, hs⟩ := h
  simp only [vertices, Finset.mem_biUnion, id]
  exact ⟨τ, hτ, hs hx⟩

/-- The product of `φ` along a path, latest edge leftmost. -/
def pp (φ : V → V → Λ) : List V → Λ
  | [] => 1
  | [_] => 1
  | a :: b :: l => pp φ (b :: l) * φ a b

lemma pp_split (φ : V → V → Λ) (x : V) (B : List V) :
    ∀ A : List V, pp φ (A ++ x :: B) = pp φ (x :: B) * pp φ (A ++ [x])
  | [] => by simp [pp]
  | [a] => by simp [pp]
  | a :: c :: A => by
    have := pp_split φ x B (c :: A)
    simp only [List.cons_append] at this ⊢
    simp only [pp, this, mul_assoc]

variable {X}

lemma pp_rev {φ : V → V → Λ} (hC : X.IsC1 φ) :
    ∀ l : List V, l.IsChain (fun u v => u ≠ v ∧ X.IsFace {u, v}) →
      pp φ l.reverse = (pp φ l)⁻¹
  | [], _ => by simp [pp]
  | [a], _ => by simp [pp]
  | a :: b :: l, h => by
    rw [List.isChain_cons_cons] at h
    have ih := pp_rev hC (b :: l) h.2
    have hba : φ b a = (φ a b)⁻¹ :=
      hC b a ⟨h.1.1.symm, by rw [Finset.pair_comm]; exact h.1.2⟩
    have e : (a :: b :: l).reverse = l.reverse ++ b :: [a] := by simp
    have e' : l.reverse ++ [b] = (b :: l).reverse := by simp
    rw [e, pp_split, e', ih]
    simp [pp, hba]

variable (X)

/-- A `(TR)` step `P → P'` across the triangle `t`. -/
def TRvia (P P' : List V) (t : Finset V) : Prop :=
  ∃ u v w Q₀ Q₁, t = {u, v, w} ∧ u ≠ v ∧ v ≠ w ∧ u ≠ w ∧ X.IsFace {u, v, w} ∧
    X.IsPathFrom v₀ u Q₀ ∧ X.IsPathFrom v₀ w Q₁ ∧
    P = pcat (pcat Q₀ [u, v, w]) Q₁.reverse ∧ P' = pcat (pcat Q₀ [u, w]) Q₁.reverse

/-- `t` is an (oriented somehow) triangle on which `d₁φ` is nontrivial. -/
def SuppTri (φ : V → V → Λ) (t : Finset V) : Prop :=
  ∃ u v w, t = {u, v, w} ∧ u ≠ v ∧ v ≠ w ∧ u ≠ w ∧ X.IsFace {u, v, w} ∧ d1 φ u v w ≠ 1

lemma trStep_iff {P P' : List V} : X.TRstep v₀ P P' ↔ ∃ t, TRvia X v₀ P P' t := by
  constructor
  · rintro ⟨u, v, w, Q₀, Q₁, h⟩
    exact ⟨_, u, v, w, Q₀, Q₁, rfl, h⟩
  · rintro ⟨_, u, v, w, Q₀, Q₁, -, h⟩
    exact ⟨u, v, w, Q₀, Q₁, h⟩

/-- A chosen triangle of a `(TR)` pair. -/
def triOf (A B : List V) : Finset V :=
  if h : ∃ t, TRvia X v₀ A B t ∨ TRvia X v₀ B A t then h.choose else ∅

lemma triOf_spec {A B : List V} (h : X.TR v₀ A B) :
    TRvia X v₀ A B (triOf X v₀ A B) ∨ TRvia X v₀ B A (triOf X v₀ A B) := by
  have h' : ∃ t, TRvia X v₀ A B t ∨ TRvia X v₀ B A t := by
    rcases h with h | h
    · obtain ⟨t, ht⟩ := (trStep_iff X v₀).1 h; exact ⟨t, Or.inl ht⟩
    · obtain ⟨t, ht⟩ := (trStep_iff X v₀).1 h; exact ⟨t, Or.inr ht⟩
  simp only [triOf, dif_pos h']
  exact h'.choose_spec

lemma TRvia.face {A B : List V} {t : Finset V} (h : TRvia X v₀ A B t) : X.IsFace t := by
  obtain ⟨u, v, w, -, -, rfl, -, -, -, hf, -⟩ := h
  exact hf

lemma triOf_face {A B : List V} (h : X.TR v₀ A B) : X.IsFace (triOf X v₀ A B) := by
  rcases triOf_spec X v₀ h with h | h <;> exact h.face

/-- The triangles crossed by the `(TR)` steps of a contraction. -/
def crossings : List (List V) → List (Finset V)
  | A :: B :: l => (if X.TR v₀ A B then [triOf X v₀ A B] else []) ++ crossings (B :: l)
  | _ => []

lemma trCount_cons_cons (A B : List V) (l : List (List V)) :
    X.trCount v₀ (A :: B :: l) = (if X.TR v₀ A B then 1 else 0) + X.trCount v₀ (B :: l) := by
  simp only [trCount, List.tail_cons, List.zip_cons_cons, List.countP_cons, decide_eq_true_eq]
  split_ifs <;> omega

lemma crossings_length : ∀ T : List (List V), (crossings X v₀ T).length = X.trCount v₀ T
  | [] => by simp [crossings, trCount]
  | [A] => by simp [crossings, trCount]
  | A :: B :: l => by
    rw [crossings, List.length_append, crossings_length (B :: l), trCount_cons_cons]
    split_ifs <;> simp

lemma crossings_face : ∀ (T : List (List V)) t, t ∈ crossings X v₀ T → X.IsFace t
  | [], _, h => by simp [crossings] at h
  | [A], _, h => by simp [crossings] at h
  | A :: B :: l, t, h => by
    rw [crossings, List.mem_append] at h
    rcases h with h | h
    · split_ifs at h with hAB
      · rw [List.mem_singleton] at h; subst h; exact triOf_face X v₀ hAB
      · simp at h
    · exact crossings_face (B :: l) t h

variable {X v₀}

lemma pp_bt {φ : V → V → Λ} (hC : X.IsC1 φ) {P P' : List V} (h : X.BTstep v₀ P P') :
    pp φ P = pp φ P' := by
  obtain ⟨u, v, Q₀, Q₁, hQ₀, hQ₁, huv, hf, rfl, rfl⟩ := h
  obtain ⟨Q, rfl⟩ := List.getLast?_eq_some_iff.1 hQ₀.2.2
  obtain ⟨R, hR⟩ := List.getLast?_eq_some_iff.1 hQ₁.2.2
  have e1 : pcat (pcat (Q ++ [u]) [u, v, u]) Q₁.reverse = Q ++ u :: (v :: u :: R.reverse) := by
    simp [pcat, hR]
  have e2 : pcat (pcat (Q ++ [u]) [u]) Q₁.reverse = Q ++ u :: R.reverse := by
    simp [pcat, hR]
  rw [e1, e2, pp_split φ u (v :: u :: R.reverse) Q, pp_split φ u R.reverse Q]
  congr 1
  have huv' : φ u v = (φ v u)⁻¹ := hC u v ⟨huv, hf⟩
  simp [pp, huv', mul_assoc]

lemma pp_tr {φ : V → V → Λ} (hC : X.IsC1 φ) {P P' : List V} {t : Finset V}
    (h : TRvia X v₀ P P' t) (hne : pp φ P ≠ pp φ P') : SuppTri X φ t := by
  obtain ⟨u, v, w, Q₀, Q₁, rfl, huv, hvw, huw, hf, hQ₀, hQ₁, rfl, rfl⟩ := h
  refine ⟨u, v, w, rfl, huv, hvw, huw, hf, fun hc => hne ?_⟩
  obtain ⟨Q, rfl⟩ := List.getLast?_eq_some_iff.1 hQ₀.2.2
  obtain ⟨R, hR⟩ := List.getLast?_eq_some_iff.1 hQ₁.2.2
  have e1 : pcat (pcat (Q ++ [u]) [u, v, w]) Q₁.reverse = Q ++ u :: (v :: w :: R.reverse) := by
    simp [pcat, hR]
  have e2 : pcat (pcat (Q ++ [u]) [u, w]) Q₁.reverse = Q ++ u :: (w :: R.reverse) := by
    simp [pcat, hR]
  rw [e1, e2, pp_split φ u (v :: w :: R.reverse) Q, pp_split φ u (w :: R.reverse) Q]
  congr 1
  have hwu : φ w u = (φ u w)⁻¹ :=
    hC w u ⟨huw.symm, face_sub X hf (by intro x; simp; tauto)⟩
  simp only [d1, hwu] at hc
  have hb := eq_inv_of_mul_eq_one_right hc
  simp only [pp, mul_assoc]
  rw [hb]; group

lemma cone_chain {φ : V → V → Λ} (hC : X.IsC1 φ) :
    ∀ (T : List (List V)) (A B : List V), T.IsChain (fun A B => X.TR v₀ A B ∨ X.BT v₀ A B) →
      T.head? = some A → T.getLast? = some B → pp φ A ≠ pp φ B →
      ∃ t ∈ crossings X v₀ T, SuppTri X φ t
  | [], _, _, _, h, _, _ => by simp at h
  | [C], A, B, _, hA, hB, hne => by
    simp at hA hB; subst hA; subst hB; exact absurd rfl hne
  | C :: D :: l, A, B, hch, hA, hB, hne => by
    simp only [List.head?_cons, Option.some.injEq] at hA
    subst hA
    rw [List.isChain_cons_cons] at hch
    have hB' : (D :: l).getLast? = some B := by simpa using hB
    by_cases hCD : pp φ C = pp φ D
    · obtain ⟨t, ht, hs⟩ := cone_chain hC (D :: l) D B hch.2 rfl hB' (hCD ▸ hne)
      exact ⟨t, by rw [crossings, List.mem_append]; exact Or.inr ht, hs⟩
    · rcases hch.1 with htr | hbt
      · refine ⟨triOf X v₀ C D, ?_, ?_⟩
        · rw [crossings, List.mem_append, if_pos htr]; simp
        · rcases triOf_spec X v₀ htr with h | h
          · exact pp_tr hC h hCD
          · exact pp_tr hC h (Ne.symm hCD)
      · rcases hbt with h | h
        · exact absurd (pp_bt hC h) hCD
        · exact absurd (pp_bt hC h).symm hCD

lemma loop_bound {C : OneCone V} (hCone : X.IsOneCone C) {φ : V → V → Λ} (hC : X.IsC1 φ)
    {a b : V} (hab : a ≠ b) (hf : X.IsFace {a, b})
    (hne : (pp φ (C.P b))⁻¹ * φ a b * pp φ (C.P a) ≠ 1) :
    ∃ t ∈ crossings X C.apex (C.T a b), SuppTri X φ t := by
  have hP : ∀ x ∈ X.vertices, (∃ Q, C.P x = Q ++ [x]) ∧
      (C.P x).IsChain (fun u v => u ≠ v ∧ X.IsFace {u, v}) := by
    intro x hx
    by_cases h : x = C.apex
    · subst h; rw [hCone.2.1]; exact ⟨⟨[], rfl⟩, List.isChain_singleton _⟩
    · have hp := hCone.2.2.1 x hx h
      exact ⟨List.getLast?_eq_some_iff.1 hp.2.2, hp.1.2.2⟩
  obtain ⟨⟨Q, hQ⟩, -⟩ := hP a (vert_of_face X hf (by simp))
  obtain ⟨⟨R, hR⟩, hRc⟩ := hP b (vert_of_face X hf (by simp))
  obtain ⟨hh, hch, hl⟩ := hCone.2.2.2 a b hab hf
  refine cone_chain hC _ _ _ hch hh hl ?_
  have e : pcat (pcat (C.P a) [a, b]) (C.P b).reverse = Q ++ a :: (b :: R.reverse) := by
    simp [pcat, hQ, hR]
  have e' : (C.P b).reverse = b :: R.reverse := by simp [hR]
  rw [e, pp_split, ← hQ]
  have hrev := pp_rev hC _ hRc
  rw [e'] at hrev
  have : pp φ (a :: b :: R.reverse) = pp φ (b :: R.reverse) * φ a b := rfl
  rw [this, hrev]
  exact hne

lemma pair_cases {u v x y : V} (h : ({u, v} : Finset V) = {x, y}) (hxy : x ≠ y) :
    (u = x ∧ v = y) ∨ (u = y ∧ v = x) := by
  have hu : u ∈ ({x, y} : Finset V) := h ▸ by simp
  have hv : v ∈ ({x, y} : Finset V) := h ▸ by simp
  have hx : x ∈ ({u, v} : Finset V) := h.symm ▸ by simp
  have hy : y ∈ ({u, v} : Finset V) := h.symm ▸ by simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv hx hy
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> simp_all

lemma alg1 {x p q : Λ} (h : q⁻¹ * x * p = 1) : x * (q * p⁻¹)⁻¹ = 1 := by
  have : x = q * p⁻¹ := by
    calc x = q * (q⁻¹ * x * p) * p⁻¹ := by group
      _ = q * p⁻¹ := by rw [h]; group
  rw [this]; group

lemma alg2 {x p q : Λ} (h : q⁻¹ * x * p = 1) : x⁻¹ * (p * q⁻¹)⁻¹ = 1 := by
  have : x = q * p⁻¹ := by
    calc x = q * (q⁻¹ * x * p) * p⁻¹ := by group
      _ = q * p⁻¹ := by rw [h]; group
  rw [this]; group

lemma sum_list_swap {α β : Type*} (s : Finset α) (f : α → β → ℝ) :
    ∀ l : List β, ∑ g ∈ s, (l.map (f g)).sum = (l.map (fun t => ∑ g ∈ s, f g t)).sum
  | [] => by simp
  | t :: l => by simp [Finset.sum_add_distrib, sum_list_swap s f l]

end General

section Coset

variable {G : Type*} [Group G] [Fintype G] {ι : Type*} [Fintype ι] (H : ι → Subgroup G)

local notation "VV" => Σ i, G ⧸ H i

local instance (priority := 2000) instDecSig : DecidableEq VV :=
  fun a b => Classical.propDecidable (a = b)

/-- The chamber `{yH_i : i}`. -/
def ch (y : G) : Finset VV := Finset.univ.image (fun i => (⟨i, (y : G ⧸ H i)⟩ : VV))

variable {H}

/-- Left translation on vertices. -/
def act (g : G) (x : VV) : VV := ⟨x.1, g • x.2⟩

lemma act_mul (g h : G) (x : VV) : act g (act h x) = act (g * h) x := by
  obtain ⟨i, q⟩ := x
  show (⟨i, g • h • q⟩ : VV) = ⟨i, (g * h) • q⟩
  rw [mul_smul]

lemma act_one (x : VV) : act 1 x = x := by simp [act]

lemma act_inv_act (g : G) (x : VV) : act g⁻¹ (act g x) = x := by
  rw [act_mul, inv_mul_cancel, act_one]

lemma act_act_inv (g : G) (x : VV) : act g (act g⁻¹ x) = x := by
  rw [act_mul, mul_inv_cancel, act_one]

lemma act_injective (g : G) : Function.Injective (act (H := H) g) := by
  intro x y h
  have := congrArg (act g⁻¹) h
  rwa [act_inv_act, act_inv_act] at this

lemma image_act_image (g h : G) (s : Finset VV) :
    (s.image (act h)).image (act g) = s.image (act (g * h)) := by
  rw [Finset.image_image]; congr 1; funext x; exact act_mul g h x

lemma image_act_one (s : Finset VV) : s.image (act 1) = s := by
  have : act (H := H) 1 = id := funext act_one
  rw [this, Finset.image_id]

lemma image_act_ch (g y : G) : (ch H y).image (act g) = ch H (g * y) := by
  unfold ch; rw [Finset.image_image]; rfl

lemma card_ch (y : G) : (ch H y).card = Fintype.card ι := by
  rw [ch, Finset.card_image_of_injective _ (fun i j h => (Sigma.mk.inj_iff.1 h).1)]
  rfl

lemma mem_tops {τ : Finset VV} : τ ∈ (cosetComplex G H).tops ↔ ∃ y, ch H y = τ := by
  unfold cosetComplex
  simp only
  rw [dif_pos (Finite.of_fintype G)]
  simp only [ch, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨fun ⟨y, hy⟩ => ⟨y, by convert hy using 2⟩, fun ⟨y, hy⟩ => ⟨y, by convert hy using 2⟩⟩

lemma tops_eq : (cosetComplex G H).tops = Finset.univ.image (ch H) := by
  ext τ; rw [mem_tops]; simp

lemma isFace_iff {σ : Finset VV} : (cosetComplex G H).IsFace σ ↔ ∃ y, σ ⊆ ch H y := by
  constructor
  · rintro ⟨τ, hτ, hs⟩
    obtain ⟨y, rfl⟩ := mem_tops.1 hτ
    exact ⟨y, hs⟩
  · rintro ⟨y, hy⟩
    exact ⟨ch H y, mem_tops.2 ⟨y, rfl⟩, hy⟩

lemma isFace_act (g : G) {σ : Finset VV} (h : (cosetComplex G H).IsFace σ) :
    (cosetComplex G H).IsFace (σ.image (act g)) := by
  obtain ⟨y, hy⟩ := isFace_iff.1 h
  exact isFace_iff.2 ⟨g * y, by rw [← image_act_ch]; exact Finset.image_subset_image hy⟩

lemma mem_facesCard {σ : Finset VV} {k : ℕ} :
    σ ∈ (cosetComplex G H).facesCard k ↔ (cosetComplex G H).IsFace σ ∧ σ.card = k := by
  simp [facesCard, faces, IsFace, Finset.mem_biUnion]

lemma subset_act_iff (g y : G) (σ : Finset VV) :
    σ.image (act g) ⊆ ch H y ↔ σ ⊆ ch H (g⁻¹ * y) := by
  constructor
  · intro h
    have := Finset.image_subset_image (f := act g⁻¹) h
    rwa [image_act_image, inv_mul_cancel, image_act_one, image_act_ch] at this
  · intro h
    have := Finset.image_subset_image (f := act g) h
    rwa [image_act_ch, mul_inv_cancel_left] at this

lemma ch_eq_iff (y z : G) : ch H y = ch H z ↔ ∀ i, z⁻¹ * y ∈ H i := by
  constructor
  · intro h i
    have hm : (⟨i, (y : G ⧸ H i)⟩ : VV) ∈ ch H z := h ▸ Finset.mem_image.2 ⟨i, by simp, rfl⟩
    obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hm
    obtain ⟨rfl, hj⟩ := Sigma.mk.inj_iff.1 hj
    exact QuotientGroup.eq.1 (eq_of_heq hj)
  · intro h
    simp only [ch]
    congr 1; funext i
    rw [QuotientGroup.eq.2 (h i)]

/-- The size of every fibre of `y ↦ ch y`. -/
def cB (H : ι → Subgroup G) : ℕ := (Finset.univ.filter (fun b : G => ∀ i, b ∈ H i)).card

lemma cB_pos : 0 < cB H := Finset.card_pos.2 ⟨1, by simp⟩

lemma fibre_card (z : G) : (Finset.univ.filter (fun y => ch H y = ch H z)).card = cB H := by
  refine Finset.card_nbij' (fun y => z⁻¹ * y) (fun b => z * b) ?_ ?_ ?_ ?_
  · intro y hy; simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hy ⊢
    exact (ch_eq_iff y z).1 hy
  · intro b hb; simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hb ⊢
    exact (ch_eq_iff _ z).2 (by simpa using hb)
  · intro y _; simp
  · intro b _; simp

lemma sum_ch (f : Finset VV → ℝ) :
    ∑ y : G, f (ch H y) = cB H * ∑ τ ∈ (cosetComplex G H).tops, f τ := by
  rw [Finset.sum_comp, tops_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ hτ => ?_
  obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 hτ
  rw [fibre_card, nsmul_eq_mul]

lemma gw_eq (σ : Finset VV) :
    (cosetComplex G H).gw σ = ((Finset.univ.filter (fun y => σ ⊆ ch H y)).card : ℝ) /
      ((Fintype.card ι).choose σ.card : ℕ) / Fintype.card G := by
  have hc : (0 : ℝ) < cB H := by exact_mod_cast cB_pos
  have h1 := sum_ch (H := H) (fun τ => if σ ⊆ τ then 1 / ((τ.card.choose σ.card : ℕ) : ℝ) else 0)
  have h2 := sum_ch (H := H) (fun _ => (1 : ℝ))
  simp only [card_ch, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h1 h2
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul] at h1
  have hwt : ∀ τ, (cosetComplex G H).wt τ = 1 := fun _ => rfl
  rw [gw, Finset.sum_filter, Finset.sum_congr rfl (fun τ _ => by rw [hwt]), Finset.sum_congr rfl (fun τ _ => hwt τ)]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  set Xs := ∑ τ ∈ (cosetComplex G H).tops, if σ ⊆ τ then 1 / ((τ.card.choose σ.card : ℕ) : ℝ) else 0
  have hX : Xs = ((Finset.univ.filter (fun y => σ ⊆ ch H y)).card : ℝ) /
      ((Fintype.card ι).choose σ.card : ℕ) / cB H := by
    rw [eq_div_iff hc.ne', mul_comm, ← h1]; ring
  have hT : ((cosetComplex G H).tops.card : ℝ) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at h2
    exact (Fintype.card_pos (α := G)).ne' (by exact_mod_cast h2)
  rw [show ((Finset.univ.filter (fun y => σ ⊆ ch H y)).card : ℝ) /
      ((Fintype.card ι).choose σ.card : ℕ) / Fintype.card G =
      Xs / ((cosetComplex G H).tops.card : ℝ) by
    rw [hX, h2]; field_simp]

lemma gw_act (g : G) (σ : Finset VV) :
    (cosetComplex G H).gw (σ.image (act g)) = (cosetComplex G H).gw σ := by
  rw [gw_eq, gw_eq, Finset.card_image_of_injective _ (act_injective g)]
  congr 3
  refine Finset.card_nbij' (fun y => g⁻¹ * y) (fun y => g * y) ?_ ?_ ?_ ?_
  · intro y hy
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hy ⊢
    exact (subset_act_iff g y σ).1 hy
  · intro y hy
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hy ⊢
    rw [subset_act_iff, inv_mul_cancel_left]; exact hy
  · intro y _; simp
  · intro y _; simp

lemma gw_nonneg (σ : Finset VV) : 0 ≤ (cosetComplex G H).gw σ := by
  rw [gw_eq]; positivity

lemma sum_gw_le (k : ℕ) : ∑ σ ∈ (cosetComplex G H).facesCard k, (cosetComplex G H).gw σ ≤ 1 := by
  set F := (cosetComplex G H).facesCard k
  have hnat : ∑ σ ∈ F, (Finset.univ.filter (fun y => σ ⊆ ch H y)).card ≤
      Fintype.card G * (Fintype.card ι).choose k := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm, ← Finset.card_univ, Finset.card_eq_sum_ones, Finset.sum_mul, one_mul]
    refine Finset.sum_le_sum fun y _ => ?_
    rw [← Finset.card_filter, ← card_ch (H := H) y, ← Finset.card_powersetCard]
    refine Finset.card_le_card fun σ hσ => ?_
    rw [Finset.mem_filter] at hσ
    exact Finset.mem_powersetCard.2 ⟨hσ.2, (mem_facesCard.1 hσ.1).2⟩
  calc ∑ σ ∈ F, (cosetComplex G H).gw σ
      = ∑ σ ∈ F, ((Finset.univ.filter (fun y => σ ⊆ ch H y)).card : ℝ) /
          ((Fintype.card ι).choose k : ℕ) / Fintype.card G := by
        refine Finset.sum_congr rfl fun σ hσ => ?_
        rw [gw_eq, (mem_facesCard.1 hσ).2]
    _ = ((∑ σ ∈ F, (Finset.univ.filter (fun y => σ ⊆ ch H y)).card : ℕ) : ℝ) /
          ((Fintype.card ι).choose k : ℕ) / Fintype.card G := by
        rw [Nat.cast_sum, Finset.sum_div, Finset.sum_div]
    _ ≤ 1 := by
        rcases Nat.eq_zero_or_pos ((Fintype.card ι).choose k) with h0 | hpos
        · simp [h0]
        · have hG : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
          rw [div_div, div_le_one (by positivity)]
          have : ((∑ σ ∈ F, (Finset.univ.filter (fun y => σ ⊆ ch H y)).card : ℕ) : ℝ) ≤
              ((Fintype.card G * (Fintype.card ι).choose k : ℕ) : ℝ) := by exact_mod_cast hnat
          push_cast at this ⊢; linarith

lemma tri_count (S : Finset (Finset VV)) (hS : S ⊆ (cosetComplex G H).facesCard 3)
    {t : Finset VV} {x : G} (ht : t ⊆ ch H x) :
    ∑ g : G, (if t.image (act g) ∈ S then (1 : ℝ) else 0) ≤
      ((Fintype.card ι).choose 3 : ℕ) * Fintype.card G * ∑ s ∈ S, (cosetComplex G H).gw s := by
  rw [Finset.sum_boole]
  have h1 : (Finset.univ.filter (fun g : G => t.image (act g) ∈ S)).card ≤
      ∑ s ∈ S, (Finset.univ.filter (fun y => s ⊆ ch H y)).card := by
    refine (Finset.card_le_card (t := S.biUnion
      (fun s => Finset.univ.filter (fun g : G => t.image (act g) = s))) ?_).trans
      (Finset.card_biUnion_le.trans (Finset.sum_le_sum fun s _ => ?_))
    · intro g hg
      rw [Finset.mem_filter] at hg
      exact Finset.mem_biUnion.2 ⟨_, hg.2, by simp⟩
    · refine Finset.card_le_card_of_injOn (fun g => g * x) ?_ ?_
      · intro g hg
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hg ⊢
        rw [← hg, ← image_act_ch]; exact Finset.image_subset_image ht
      · intro a _ b _ h; exact mul_right_cancel h
  calc (((Finset.univ.filter (fun g : G => t.image (act g) ∈ S)).card : ℕ) : ℝ)
      ≤ ((∑ s ∈ S, (Finset.univ.filter (fun y => s ⊆ ch H y)).card : ℕ) : ℝ) := by
        exact_mod_cast h1
    _ = ∑ s ∈ S, ((Fintype.card ι).choose 3 : ℕ) * (Fintype.card G : ℝ) *
          (cosetComplex G H).gw s := by
        push_cast
        refine Finset.sum_congr rfl fun s hs => ?_
        obtain ⟨hf, hc⟩ := mem_facesCard.1 (hS hs)
        obtain ⟨y, hy⟩ := isFace_iff.1 hf
        have h3 : 3 ≤ Fintype.card ι := by
          rw [← hc, ← card_ch (H := H) y]; exact Finset.card_le_card hy
        have hC : (0 : ℝ) < ((Fintype.card ι).choose 3 : ℕ) := by
          exact_mod_cast Nat.choose_pos h3
        have hG : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
        rw [gw_eq, hc]; field_simp
    _ = _ := by rw [Finset.mul_sum]

end Coset

end PolySwap.KMS.P313.ConeAux
end
end Part_ConeAux

section Part_Cone

open Classical

noncomputable section

namespace PolySwap.KMS.P313

open PolySwap.KMS WComplex ConeAux

local instance (priority := 2000) instDecSig {G : Type*} [Group G] {ι : Type*}
    {H : ι → Subgroup G} : DecidableEq (Σ i, G ⧸ H i) :=
  fun a b => Classical.propDecidable (a = b)

/-- Proposition 3.14 for coset complexes: a 1-cone with `Rad₁ ≤ R` gives
`h¹ ≥ 1 / (binom(n, 3) (R + 1))`, `n` the number of subgroups. -/
theorem cone_h1 {G : Type*} [Group G] [Finite G] {ι : Type*} [Fintype ι]
    (H : ι → Subgroup G) (C : WComplex.OneCone (Σ i, G ⧸ H i))
    (hC : (cosetComplex G H).IsOneCone C) (R : ℕ) (hR : (cosetComplex G H).rad1 C ≤ R)
    (Λ : Type*) [Group Λ] :
    (cosetComplex G H).HOneGe Λ (1 / (((Fintype.card ι).choose 3 : ℕ) * (R + 1) : ℝ)) := by
  let := Fintype.ofFinite G
  intro ϕ hϕ
  set X := cosetComplex G H with hXdef
  set E := X.facesCard 2 with hEdef
  set S := (X.facesCard 3).filter (fun t => ∃ u v w, t = {u, v, w} ∧ d1 ϕ u v w ≠ 1) with hSdef
  have hN : X.normD1 ϕ = ∑ s ∈ S, X.gw s := by
    unfold WComplex.normD1; rw [hSdef]; congr 1; ext t; simp only [Finset.mem_filter]
  have hN0 : 0 ≤ X.normD1 ϕ := Finset.sum_nonneg fun s _ => gw_nonneg s
  set C3 : ℝ := (((Fintype.card ι).choose 3 : ℕ) : ℝ) with hC3
  have hC30 : 0 ≤ C3 := by positivity
  have hfin : ∀ ψ : (Σ i, G ⧸ H i) → (Σ i, G ⧸ H i) → Λ,
      X.dist1 ϕ ψ ≤ R * C3 * X.normD1 ϕ →
      1 / (C3 * (R + 1)) * X.dist1 ϕ ψ ≤ X.normD1 ϕ := by
    intro ψ hψ
    rcases eq_or_lt_of_le hC30 with h0 | hpos
    · rw [← h0]; simpa using hN0
    · rw [one_div, inv_mul_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg hC30 hN0]
  by_cases hV : Nonempty (Σ i, G ⧸ H i)
  swap
  · refine ⟨fun _ _ => 1, ⟨fun _ _ _ => by simp, fun _ _ _ _ => by simp [d1]⟩, hfin _ ?_⟩
    have hE : E = ∅ := Finset.eq_empty_of_forall_notMem fun e he => by
      obtain ⟨a, b, -, rfl⟩ := Finset.card_eq_two.1 (mem_facesCard.1 he).2
      exact hV ⟨a⟩
    have : X.dist1 ϕ (fun _ _ => 1) = 0 := by
      unfold dist1; rw [← hEdef, hE]; simp
    rw [this]; positivity
  have hE : ∀ e ∈ E, ∃ a b, a ≠ b ∧ e = {a, b} := fun e he =>
    Finset.card_eq_two.1 (mem_facesCard.1 he).2
  choose! oa ob hoab using hE
  have hEf : ∀ e ∈ E, X.IsFace {oa e, ob e} := fun e he =>
    (hoab e he).2 ▸ (mem_facesCard.1 he).1
  let ϕg : G → (Σ i, G ⧸ H i) → (Σ i, G ⧸ H i) → Λ := fun g u v => ϕ (act g u) (act g v)
  let hg : G → (Σ i, G ⧸ H i) → Λ := fun g u => pp (ϕg g) (C.P u)
  let ψ : G → (Σ i, G ⧸ H i) → (Σ i, G ⧸ H i) → Λ :=
    fun g u v => hg g (act g⁻¹ v) * (hg g (act g⁻¹ u))⁻¹
  let L : G → (Σ i, G ⧸ H i) → (Σ i, G ⧸ H i) → Λ :=
    fun g a b => (hg g b)⁻¹ * ϕg g a b * hg g a
  let I : G → Finset (Σ i, G ⧸ H i) → ℝ := fun g e => if L g (oa e) (ob e) ≠ 1 then 1 else 0
  let cr : Finset (Σ i, G ⧸ H i) → List (Finset (Σ i, G ⧸ H i)) :=
    fun e => crossings X C.apex (C.T (oa e) (ob e))
  let f : G → Finset (Σ i, G ⧸ H i) → ℝ := fun g t => if t.image (act g) ∈ S then 1 else 0
  set K : ℝ := C3 * Fintype.card G * X.normD1 ϕ with hK
  have hK0 : 0 ≤ K := by positivity
  have hpair : ∀ (g : G) (a b : Σ i, G ⧸ H i),
      ({a, b} : Finset _).image (act g) = {act g a, act g b} := by
    intro g a b; simp [Finset.image_insert]
  have hϕg : ∀ g, X.IsC1 (ϕg g) := by
    intro g u v huv
    refine hϕ _ _ ⟨fun h => huv.1 (act_injective g h), ?_⟩
    rw [← hpair]; exact isFace_act g huv.2
  have hψ : ∀ g, X.IsZ1 (ψ g) := fun g =>
    ⟨fun u v _ => by simp only [ψ]; group, fun u v w _ => by simp only [d1, ψ]; group⟩
  have hdist : ∀ g, X.dist1 ϕ (ψ g) ≤ ∑ e ∈ E, X.gw e * I g e := by
    intro g
    unfold dist1
    rw [← hEdef, Finset.sum_filter]
    rw [Finset.sum_nbij' (fun e => e.image (act g⁻¹)) (fun e => e.image (act g))
      (g := fun e => if (∃ u v, e.image (act g) = {u, v} ∧ ϕ u v * (ψ g u v)⁻¹ ≠ 1)
        then X.gw (e.image (act g)) else 0)]
    rotate_left
    · intro e he
      exact mem_facesCard.2 ⟨isFace_act _ (mem_facesCard.1 he).1, by
        rw [Finset.card_image_of_injective _ (act_injective _)]; exact (mem_facesCard.1 he).2⟩
    · intro e he
      exact mem_facesCard.2 ⟨isFace_act _ (mem_facesCard.1 he).1, by
        rw [Finset.card_image_of_injective _ (act_injective _)]; exact (mem_facesCard.1 he).2⟩
    · intro e _; rw [image_act_image, mul_inv_cancel, image_act_one]
    · intro e _; rw [image_act_image, inv_mul_cancel, image_act_one]
    · intro e _; rw [image_act_image, mul_inv_cancel, image_act_one]; congr
    refine Finset.sum_le_sum fun e he => ?_
    obtain ⟨hab, hee⟩ := hoab e he
    split_ifs with hM
    · rw [gw_act]
      have hL : L g (oa e) (ob e) ≠ 1 := by
        obtain ⟨u, v, huv, hne⟩ := hM
        rw [hee, hpair] at huv
        intro hL
        rcases pair_cases huv.symm ((act_injective g).ne hab) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · apply hne
          simp only [ψ, act_inv_act]
          exact alg1 hL
        · apply hne
          simp only [ψ, act_inv_act]
          have hba : ϕ (act g (ob e)) (act g (oa e)) = (ϕg g (oa e) (ob e))⁻¹ :=
            hϕg g (ob e) (oa e) ⟨hab.symm, by rw [Finset.pair_comm]; exact hEf e he⟩
          rw [hba]
          exact alg2 hL
      have hI : I g e = 1 := by simp only [I]; rw [if_pos hL]
      rw [hI, mul_one]
    · exact mul_nonneg (gw_nonneg e) (by simp only [I]; split_ifs <;> norm_num)
  have hf0 : ∀ g t, 0 ≤ f g t := fun g t => by simp only [f]; split_ifs <;> norm_num
  have hedge : ∀ g, ∀ e ∈ E, I g e ≤ ((cr e).map (f g)).sum := by
    intro g e he
    simp only [I]
    split_ifs with hL
    · obtain ⟨t, ht, u, v, w, rfl, huv, hvw, huw, hf, hd⟩ :=
        loop_bound hC (hϕg g) (hoab e he).1 (hEf e he) hL
      have hft : f g {u, v, w} = 1 := by
        simp only [f]
        rw [if_pos]
        refine Finset.mem_filter.2 ⟨mem_facesCard.2 ⟨isFace_act g hf, ?_⟩,
          act g u, act g v, act g w, by simp [Finset.image_insert], hd⟩
        rw [Finset.card_image_of_injective _ (act_injective g)]
        exact Finset.card_eq_three.2 ⟨u, v, w, huv, huw, hvw, rfl⟩
      rw [← hft]
      exact List.single_le_sum (fun x hx => by
        obtain ⟨t, -, rfl⟩ := List.mem_map.1 hx; exact hf0 g t) _ (List.mem_map_of_mem ht)
    · exact List.sum_nonneg fun x hx => by
        obtain ⟨t, -, rfl⟩ := List.mem_map.1 hx; exact hf0 g t
  have htri : ∀ e, ∀ t ∈ cr e, ∑ g : G, f g t ≤ K := by
    intro e t ht
    obtain ⟨x, hx⟩ := isFace_iff.1 (crossings_face X C.apex _ t ht)
    exact (tri_count S (Finset.filter_subset _ _) hx).trans_eq (by rw [hK, hN])
  have hlen : ∀ e ∈ E, ((cr e).length : ℝ) ≤ R := by
    intro e he
    simp only [cr]
    rw [crossings_length]
    have h1 : ((X.trCount C.apex (C.T (oa e) (ob e)) : ℕ) : ℕ∞) ≤ X.rad1 C :=
      le_iSup_of_le (oa e) (le_iSup_of_le (ob e)
        (le_iSup_of_le ⟨(hoab e he).1, hEf e he⟩ le_rfl))
    exact_mod_cast h1.trans hR
  have hsum : ∑ g : G, X.dist1 ϕ (ψ g) ≤ R * K := by
    calc ∑ g : G, X.dist1 ϕ (ψ g) ≤ ∑ g : G, ∑ e ∈ E, X.gw e * I g e :=
          Finset.sum_le_sum fun g _ => hdist g
      _ = ∑ e ∈ E, X.gw e * ∑ g : G, I g e := by
          rw [Finset.sum_comm]; simp only [Finset.mul_sum]
      _ ≤ ∑ e ∈ E, X.gw e * (R * K) := by
          refine Finset.sum_le_sum fun e he => mul_le_mul_of_nonneg_left ?_ (gw_nonneg e)
          calc ∑ g : G, I g e ≤ ∑ g : G, ((cr e).map (f g)).sum :=
                Finset.sum_le_sum fun g _ => hedge g e he
            _ = ((cr e).map (fun t => ∑ g : G, f g t)).sum := sum_list_swap _ _ _
            _ ≤ (cr e).length • K := (List.sum_le_card_nsmul _ _ fun x hx => by
                obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx; exact htri e t ht).trans_eq
                (by rw [List.length_map])
            _ ≤ R * K := by
                rw [nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (hlen e he) hK0
      _ = (∑ e ∈ E, X.gw e) * (R * K) := by rw [Finset.sum_mul]
      _ ≤ 1 * (R * K) := mul_le_mul_of_nonneg_right (sum_gw_le 2) (by positivity)
      _ = R * K := one_mul _
  have hG : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  obtain ⟨g, -, hgle⟩ := Finset.exists_le_of_sum_le (Finset.univ_nonempty)
    (hsum.trans_eq (show (R : ℝ) * K = ∑ _g : G, R * K / Fintype.card G by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp))
  refine ⟨ψ g, hψ g, hfin _ ?_⟩
  rw [hK] at hgle
  calc X.dist1 ϕ (ψ g) ≤ R * (C3 * Fintype.card G * X.normD1 ϕ) / Fintype.card G := hgle
    _ = R * C3 * X.normD1 ϕ := by field_simp

end PolySwap.KMS.P313
end
end Part_Cone

section Part_LinkAux

open Classical Matrix Polynomial

namespace PolySwap.KMS.P313L

open PolySwap.KMS

variable {d : ℕ} {F : Type*} [Field F]

abbrev SLd (d : ℕ) (F : Type*) [Field F] := SpecialLinearGroup (Fin (d + 1)) F

/-- The off-diagonal support of `M` lies on pairs `(i, j)` with `i < j` and every colour of
`(i, j]` in `S`. -/
def Pat (S : Set ℕ) (M : Matrix (Fin (d + 1)) (Fin (d + 1)) F) : Prop :=
  ∀ i j : Fin (d + 1), i ≠ j → M i j ≠ 0 → i < j ∧ ∀ c : ℕ, (i : ℕ) < c → c ≤ j → c ∈ S

/-- Unit diagonal. -/
def Diag1 (M : Matrix (Fin (d + 1)) (Fin (d + 1)) F) : Prop := ∀ i, M i i = 1

lemma Pat.mono {S S' : Set ℕ} {M : Matrix (Fin (d + 1)) (Fin (d + 1)) F} (h : Pat S M)
    (hS : S ⊆ S') : Pat S' M := fun i j hij hne =>
  ⟨(h i j hij hne).1, fun c h1 h2 => hS ((h i j hij hne).2 c h1 h2)⟩

lemma Pat.lower {S : Set ℕ} {M : Matrix (Fin (d + 1)) (Fin (d + 1)) F} (h : Pat S M)
    {i j : Fin (d + 1)} (hij : j < i) : M i j = 0 := by
  by_contra hne
  exact absurd (h i j (ne_of_gt hij) hne).1 (not_lt.2 hij.le)

lemma pat_mul {S : Set ℕ} {M N : Matrix (Fin (d + 1)) (Fin (d + 1)) F}
    (hM : Pat S M) (hN : Pat S N) (dM : Diag1 M) (dN : Diag1 N) :
    Pat S (M * N) ∧ Diag1 (M * N) := by
  refine ⟨fun i j hij hne => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply] at hne
    obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have h1 : M i k ≠ 0 := left_ne_zero_of_mul hk
    have h2 : N k j ≠ 0 := right_ne_zero_of_mul hk
    by_cases hik : i = k
    · subst hik; exact hN i j hij h2
    by_cases hkj : k = j
    · subst hkj; exact hM i k hik h1
    obtain ⟨a1, a2⟩ := hM i k hik h1
    obtain ⟨b1, b2⟩ := hN k j hkj h2
    refine ⟨a1.trans b1, fun c hc1 hc2 => ?_⟩
    by_cases hc : c ≤ (k : ℕ)
    · exact a2 c hc1 hc
    · exact b2 c (by omega) hc2
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · simp [dM i, dN i]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · simp [hM.lower h]
      · simp [hN.lower h]
    · simp

lemma pat_transvection {S : Set ℕ} (i j : Fin (d + 1)) (hij : i < j)
    (hS : ∀ c : ℕ, (i : ℕ) < c → c ≤ j → c ∈ S) (c : F) :
    Pat S (transvection i j c) ∧ Diag1 (transvection i j c) := by
  refine ⟨fun a b hab hne => ?_, fun a => ?_⟩
  · simp only [transvection, Matrix.add_apply, Matrix.one_apply, hab, if_false, zero_add,
      Matrix.single_apply] at hne
    split_ifs at hne with h
    · obtain ⟨rfl, rfl⟩ := h; exact ⟨hij, hS⟩
    · exact absurd rfl hne
  · simp [transvection, Matrix.single_apply]
    intro h1 h2; subst h1; subst h2; exact absurd hij (lt_irrefl _)

lemma ss0 {i j k l : Fin (d + 1)} (h : j ≠ k) (a b : F) :
    (Matrix.single i j a : Matrix (Fin (d + 1)) (Fin (d + 1)) F) * Matrix.single k l b = 0 :=
  by
    ext x y
    simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun z _ => ?_
    split_ifs with h1 h2 <;> first | (exfalso; exact h (h1.2.trans h2.1.symm)) | simp

lemma tv_mul (i j : Fin (d + 1)) (hij : i ≠ j) (a b : F) :
    (transvection i j a : Matrix (Fin (d + 1)) (Fin (d + 1)) F) * transvection i j b =
      transvection i j (a + b) := by
  simp only [transvection, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    ss0 (Ne.symm hij), add_zero, Matrix.single_add]
  abel

/-- Elements of `UL S` are unitriangular with support in `S`-runs. -/
lemma pat_of_mem_UL {S : Finset ℕ} {g : SLd d F} (hg : g ∈ UL d F S) :
    Pat (S : Set ℕ) (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F) ∧
      Diag1 (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F) := by
  induction hg using Subgroup.closure_induction'' with
  | mem x hx =>
    obtain ⟨lam, i, j, hjS, -, hij, hx⟩ := hx
    rw [hx]
    exact pat_transvection i j (Fin.lt_def.2 (by omega))
      (fun c h1 h2 => by have : c = j := by omega
                         subst this; exact hjS) lam
  | inv_mem x hx =>
    obtain ⟨lam, i, j, hjS, -, hij, hx⟩ := hx
    have hne : i ≠ j := fun h => by subst h; omega
    have : ((x⁻¹ : SLd d F) : Matrix (Fin (d + 1)) (Fin (d + 1)) F) = transvection i j (-lam) := by
      have h1 : (x : Matrix (Fin (d + 1)) (Fin (d + 1)) F) * transvection i j (-lam) = 1 := by
        rw [hx, tv_mul i j hne]; simp [transvection]
      have : x⁻¹ = (⟨transvection i j (-lam), det_transvection_of_ne _ _ hne _⟩ : SLd d F) := by
        exact inv_eq_of_mul_eq_one_right (Subtype.ext h1)
      rw [this]
    rw [this]
    exact pat_transvection i j (Fin.lt_def.2 (by omega))
      (fun c h1 h2 => by have : c = j := by omega
                         subst this; exact hjS) _
  | one => exact ⟨fun i j hij hne => absurd (by simp [hij]) hne, fun i => by simp⟩
  | mul x y _ _ hx hy =>
    have e : ((x * y : SLd d F) : Matrix (Fin (d + 1)) (Fin (d + 1)) F) =
        (x : Matrix (Fin (d + 1)) (Fin (d + 1)) F) * y := rfl
    rw [e]
    exact pat_mul hx.1 hy.1 hx.2 hy.2

lemma comm_identity {A : Type*} [Ring A] (E F : A) (hEE : E * E = 0) (hFF : F * F = 0)
    (hFE : F * E = 0) : (1 + E) * (1 + F) * (1 + -E) * (1 + -F) = 1 + E * F := by
  have h1 : E * F * E = 0 := by rw [mul_assoc, hFE, mul_zero]
  have h2 : E * F * F = 0 := by rw [mul_assoc, hFF, mul_zero]
  simp only [add_mul, mul_add, one_mul, mul_one, mul_neg, neg_mul, hEE, hFF, hFE, h1, h2,
    add_zero]
  abel

/-- `t_{ij}(c) ∈ UL S` when `i < j` and every colour of `(i, j]` is in `S`. -/
lemma transvection_mem_UL {S : Finset ℕ} :
    ∀ (k : ℕ) (i j : Fin (d + 1)) (c : F), (j : ℕ) = i + k + 1 →
      (∀ c' : ℕ, (i : ℕ) < c' → c' ≤ j → c' ∈ S) →
      ∀ g : SLd d F, (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F) = transvection i j c →
        g ∈ UL d F S := by
  intro k
  induction k with
  | zero =>
    intro i j c hj hS g hg
    exact Subgroup.subset_closure ⟨c, i, j, hS j (by omega) le_rfl, by omega, by omega, hg⟩
  | succ k ih =>
    intro i j c hj hS g hg
    let m : Fin (d + 1) := ⟨i + k + 1, by omega⟩
    have him : i ≠ m := fun h => by
      have := congrArg Fin.val h; simp only [m] at this; omega
    have hmj : m ≠ j := fun h => by
      have := congrArg Fin.val h; simp only [m] at this; omega
    have hij : i ≠ j := fun h => by subst h; omega
    let e1 : SLd d F := ⟨transvection i m c, det_transvection_of_ne _ _ him _⟩
    let e2 : SLd d F := ⟨transvection m j 1, det_transvection_of_ne _ _ hmj _⟩
    let e3 : SLd d F := ⟨transvection i m (-c), det_transvection_of_ne _ _ him _⟩
    let e4 : SLd d F := ⟨transvection m j (-1), det_transvection_of_ne _ _ hmj _⟩
    have h1 : e1 ∈ UL d F S := ih i m c (by simp [m]) (fun c' h1 h2 => hS c' h1 (by
      simp [m] at h2; omega)) e1 rfl
    have h3 : e3 ∈ UL d F S := ih i m (-c) (by simp [m]) (fun c' h1 h2 => hS c' h1 (by
      simp [m] at h2; omega)) e3 rfl
    have h2 : e2 ∈ UL d F S := Subgroup.subset_closure
      ⟨1, m, j, hS j (by omega) le_rfl, by omega, by simp only [m]; omega, rfl⟩
    have h4 : e4 ∈ UL d F S := Subgroup.subset_closure
      ⟨-1, m, j, hS j (by omega) le_rfl, by omega, by simp only [m]; omega, rfl⟩
    have hprod : g = e1 * e2 * e3 * e4 := by
      apply Subtype.ext
      show (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F) = transvection i m c * transvection m j 1 *
        transvection i m (-c) * transvection m j (-1)
      rw [hg]
      simp only [transvection]
      have hn1 : Matrix.single i m (-c) = -Matrix.single i m c := by
        ext a b; simp only [Matrix.single_apply, Matrix.neg_apply]; split_ifs <;> simp
      have hn2 : Matrix.single m j (-1 : F) = -Matrix.single m j 1 := by
        ext a b; simp only [Matrix.single_apply, Matrix.neg_apply]; split_ifs <;> simp
      rw [hn1, hn2, comm_identity _ _ (ss0 (Ne.symm him) _ _) (ss0 (Ne.symm hmj) _ _)
        (ss0 (Ne.symm hij) _ _), single_mul_single_same, mul_one]
    rw [hprod]
    exact mul_mem (mul_mem (mul_mem h1 h2) h3) h4

lemma det_of_pat {S : Set ℕ} {M : Matrix (Fin (d + 1)) (Fin (d + 1)) F} (h : Pat S M)
    (hd : Diag1 M) : M.det = 1 := by
  have hU : M.IsUpperTriangular := fun i j hij => h.lower hij
  rw [Matrix.det_of_isUpperTriangular hU]
  exact Finset.prod_eq_one fun i _ => hd i

/-- The `SL` element of a unitriangular matrix. -/
noncomputable def mkSL (S : Set ℕ) (M : Matrix (Fin (d + 1)) (Fin (d + 1)) F) (h : Pat S M)
    (hd : Diag1 M) : SLd d F := ⟨M, det_of_pat h hd⟩

@[simp] lemma coe_mkSL (S : Set ℕ) (M : Matrix (Fin (d + 1)) (Fin (d + 1)) F) (h : Pat S M)
    (hd : Diag1 M) : ((mkSL S M h hd : SLd d F) : Matrix (Fin (d + 1)) (Fin (d + 1)) F) = M := rfl

/-- A unitriangular `SL` element with support in `S`-runs lies in `UL S`. -/
theorem mem_UL_of_pat {S : Finset ℕ} :
    ∀ g : SLd d F, Pat (S : Set ℕ) (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F) →
      Diag1 (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F) → g ∈ UL d F S := by
  intro g
  generalize hN : (Finset.univ.filter (fun p : Fin (d + 1) × Fin (d + 1) =>
    p.1 ≠ p.2 ∧ (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F) p.1 p.2 ≠ 0)).card = N
  induction N using Nat.strong_induction_on generalizing g with
  | _ N ih =>
    intro hg hdg
    set Mg := (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F) with hMg
    set Sx := Finset.univ.filter
      (fun p : Fin (d + 1) × Fin (d + 1) => p.1 ≠ p.2 ∧ Mg p.1 p.2 ≠ 0) with hSx
    by_cases hne : Sx.Nonempty
    · obtain ⟨⟨a, b⟩, hp, hmin⟩ := Sx.exists_min_image (fun p => p.2) hne
      simp only [hSx, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      obtain ⟨hab, hrun⟩ := hg a b hp.1 hp.2
      set c := Mg a b with hc
      have hcol : ∀ i, i ≠ a → Mg i a = 0 := by
        intro i hi
        by_contra h
        have := hmin (i, a) (by simp [hSx, hi, h])
        exact absurd hab (not_lt.2 this)
      have hab' : a ≠ b := ne_of_lt hab
      let t : SLd d F := ⟨transvection a b (-c), det_transvection_of_ne _ _ hab' _⟩
      let ti : SLd d F := ⟨transvection a b c, det_transvection_of_ne _ _ hab' _⟩
      have hti : ti ∈ UL d F S := transvection_mem_UL ((b : ℕ) - a - 1) a b c (by omega)
        (fun c' h1 h2 => hrun c' h1 h2) ti rfl
      have hgt_mat : ∀ i j, ((g * t : SLd d F) : Matrix (Fin (d + 1)) (Fin (d + 1)) F) i j =
          if i = a ∧ j = b then 0 else Mg i j := by
        intro i j
        show (Mg * transvection a b (-c)) i j = _
        rw [transvection, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.mul_apply]
        simp only [Matrix.single_apply, mul_ite, mul_zero]
        rw [Finset.sum_eq_single a]
        · by_cases hj : j = b
          · subst hj
            by_cases hi : i = a
            · subst hi; simp [hdg i, hc]
            · simp [hcol i hi, hi]
          · simp [Ne.symm hj, hj]
        · intro k _ hk; simp [Ne.symm hk]
        · simp
      have htti : t * ti = 1 := by
        apply Subtype.ext
        show transvection a b (-c) * transvection a b c = 1
        rw [tv_mul a b hab']; simp [transvection]
      have hg_eq : g = (g * t) * ti := by rw [mul_assoc, htti, mul_one]
      rw [hg_eq]
      refine mul_mem ?_ hti
      have hS' : Finset.univ.filter (fun p : Fin (d + 1) × Fin (d + 1) => p.1 ≠ p.2 ∧
          ((g * t : SLd d F) : Matrix (Fin (d + 1)) (Fin (d + 1)) F) p.1 p.2 ≠ 0) =
          Sx.erase (a, b) := by
        ext ⟨i, j⟩
        simp only [hgt_mat i j, hSx, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_erase, ne_eq, Prod.mk.injEq]
        by_cases h : i = a ∧ j = b
        · simp [h]
        · simp [h]
      refine ih _ ?_ (g * t) rfl ?_ ?_
      · rw [hS', ← hN]
        exact Finset.card_erase_lt_of_mem (by simpa [hSx, hp.1] using hp.2)
      · intro i j hij hne'
        rw [hgt_mat] at hne'
        split_ifs at hne' with h
        · exact absurd rfl hne'
        · exact hg i j hij hne'
      · intro i
        rw [hgt_mat]
        split_ifs with h
        · exact absurd (h.1.symm.trans h.2) hab'
        · exact hdg i
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      have : g = 1 := by
        apply Subtype.ext
        ext i j
        show Mg i j = (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) F) i j
        rw [Matrix.one_apply]
        by_cases hij : i = j
        · subst hij; simp [hdg i]
        · simp only [hij, if_false]
          by_contra h
          have : (i, j) ∈ Sx := by simp [hSx, hij, h]
          rw [hne] at this
          simp at this
      rw [this]; exact one_mem _


/-! ## Cyclic arithmetic -/

lemma val_sub' (i b : Fin (d + 1)) :
    ((i - b : Fin (d + 1)) : ℕ) = if (b : ℕ) ≤ i then (i : ℕ) - b else i + (d + 1) - b := by
  rw [Fin.val_sub]
  have hi := i.isLt; have hb := b.isLt
  split_ifs with h
  · rw [show d + 1 - b + i = (i - b) + (d + 1) by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)]; omega

lemma relabel_eq {b c : ℕ} (hb : b < d + 1) (hc : c < d + 1) :
    relabel d b c = if b ≤ c then c - b else c + (d + 1) - b := by
  unfold relabel
  split_ifs with h
  · rw [show c + (d + 1) - b = (c - b) + (d + 1) by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)]

lemma relabel_self {b : ℕ} (hb : b < d + 1) : relabel d b b = 0 := by
  rw [relabel_eq hb hb]; simp

/-- Colour `c` lies on the cyclic path of coordinates from `i` to `j` (colours `i+1, …, j`). -/
def inCyc (i j c : ℕ) : Prop := (i < j ∧ i < c ∧ c ≤ j) ∨ (j < i ∧ (i < c ∨ c ≤ j))

lemma K1 {i j b : Fin (d + 1)} (hij : i ≠ j) (h : ¬ inCyc i j b) :
    ((i - b : Fin (d + 1)) : ℕ) < ((j - b : Fin (d + 1)) : ℕ) := by
  have := Fin.val_ne_of_ne hij
  rw [val_sub', val_sub']
  have := i.isLt; have := j.isLt; have := b.isLt
  unfold inCyc at h
  split_ifs <;> omega

lemma K2 {i j b : Fin (d + 1)} (h : ((i - b : Fin (d + 1)) : ℕ) < ((j - b : Fin (d + 1)) : ℕ))
    {c : ℕ} (hc : c < d + 1) :
    inCyc i j c ↔ ((i - b : Fin (d + 1)) : ℕ) < relabel d b c ∧
      relabel d b c ≤ ((j - b : Fin (d + 1)) : ℕ) := by
  rw [val_sub', val_sub'] at *
  rw [relabel_eq b.isLt hc]
  have := i.isLt; have := j.isLt; have := b.isLt
  unfold inCyc
  split_ifs at * <;> omega

lemma K2' {i j b : Fin (d + 1)} (h : ((i - b : Fin (d + 1)) : ℕ) < ((j - b : Fin (d + 1)) : ℕ)) :
    (j : ℕ) < i ↔ (b : ℕ) ≤ i ∧ ¬ (b : ℕ) ≤ j := by
  rw [val_sub', val_sub'] at h
  have := i.isLt; have := j.isLt; have := b.isLt
  split_ifs at h <;> omega

/-! ## The embedding `Φ_b` of the upper-triangular model -/

section Phi

variable {f : F[X]} [Fact (Irreducible f)]

variable (f) in
/-- `s_i = t^{[b ≤ i]}`. -/
noncomputable def sc (b i : Fin (d + 1)) : AdjoinRoot f :=
  if (b : ℕ) ≤ i then AdjoinRoot.root f else 1

lemma sc_ne (ht : AdjoinRoot.root f ≠ 0) (b i : Fin (d + 1)) : sc f b i ≠ 0 := by
  unfold sc; split_ifs; exacts [ht, one_ne_zero]

variable (f) in
/-- `Φ_b(M)_{ij} = s_i M_{i-b, j-b} s_j⁻¹`: the model coordinate `a` sits at `a + b`. -/
noncomputable def Φm (b : Fin (d + 1)) (M : Matrix (Fin (d + 1)) (Fin (d + 1)) F) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) (AdjoinRoot f) :=
  fun i j => sc f b i * algebraMap F (AdjoinRoot f) (M (i - b) (j - b)) * (sc f b j)⁻¹

lemma Φm_mul (ht : AdjoinRoot.root f ≠ 0) (b : Fin (d + 1))
    (M N : Matrix (Fin (d + 1)) (Fin (d + 1)) F) : Φm f b (M * N) = Φm f b M * Φm f b N := by
  ext i j
  simp only [Φm, Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  refine (Fintype.sum_equiv (Equiv.subRight b) _ _ (fun k => ?_)).symm
  simp only [Equiv.subRight_apply]
  have := inv_mul_cancel₀ (sc_ne ht b k)
  linear_combination (sc f b i * algebraMap F (AdjoinRoot f) (M (i - b) (k - b)) *
    algebraMap F (AdjoinRoot f) (N (k - b) (j - b)) * (sc f b j)⁻¹) * this

lemma Φm_one (ht : AdjoinRoot.root f ≠ 0) (b : Fin (d + 1)) :
    Φm f b (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) F) = 1 := by
  ext i j
  simp only [Φm, Matrix.one_apply, sub_left_inj]
  split_ifs with h
  · subst h; simp [mul_inv_cancel₀ (sc_ne ht b i)]
  · simp

lemma Φm_det (ht : AdjoinRoot.root f ≠ 0) (b : Fin (d + 1))
    (M : Matrix (Fin (d + 1)) (Fin (d + 1)) F) :
    (Φm f b M).det = algebraMap F (AdjoinRoot f) M.det := by
  have e : Φm f b M = diagonal (sc f b) * ((M.map (algebraMap F (AdjoinRoot f))).submatrix
      (Equiv.subRight b) (Equiv.subRight b)) * diagonal (fun j => (sc f b j)⁻¹) := by
    ext i j; simp [Φm, diagonal_mul, mul_diagonal]
  rw [e, det_mul, det_mul, det_diagonal, det_diagonal, det_submatrix_equiv_self,
    RingHom.map_det, Finset.prod_inv_distrib]
  have : ∏ i, sc f b i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => sc_ne ht b i
  rw [RingHom.mapMatrix_apply]
  field_simp

/-- `Φ_b : SL_{d+1}(F) → SL_{d+1}(F[t]/(f))` (a homomorphism, injective). -/
noncomputable def Φ (ht : AdjoinRoot.root f ≠ 0) (b : Fin (d + 1)) :
    SLd d F →* SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f) where
  toFun M := ⟨Φm f b M, by rw [Φm_det ht, M.2, map_one]⟩
  map_one' := Subtype.ext (Φm_one ht b)
  map_mul' M N := Subtype.ext (Φm_mul ht b M N)

lemma coe_Φ (ht : AdjoinRoot.root f ≠ 0) (b : Fin (d + 1)) (M : SLd d F) :
    ((Φ ht b M : SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f)) :
      Matrix (Fin (d + 1)) (Fin (d + 1)) (AdjoinRoot f)) = Φm f b M := rfl

lemma alg_inj : Function.Injective (algebraMap F (AdjoinRoot f)) := (algebraMap F _).injective

lemma Φ_inj (ht : AdjoinRoot.root f ≠ 0) (b : Fin (d + 1)) : Function.Injective (Φ ht b) := by
  intro M N h
  have h' := congrArg (fun P : SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f) =>
    (P : Matrix (Fin (d + 1)) (Fin (d + 1)) (AdjoinRoot f))) h
  simp only [coe_Φ] at h'
  apply Subtype.ext; ext a a'
  have := congrFun (congrFun h' (a + b)) (a' + b)
  simp only [Φm, add_sub_cancel_right] at this
  have h1 := sc_ne ht b (a + b); have h2 := inv_ne_zero (sc_ne ht b (a' + b))
  rw [mul_assoc, mul_assoc] at this
  exact alg_inj (mul_right_cancel₀ h2 (mul_left_cancel₀ h1 this))

lemma K3 (ht : AdjoinRoot.root f ≠ 0) {i j b : Fin (d + 1)}
    (h : ((i - b : Fin (d + 1)) : ℕ) < ((j - b : Fin (d + 1)) : ℕ)) (x : AdjoinRoot f) :
    sc f b i * x * (sc f b j)⁻¹ = x * (if (j : ℕ) < i then AdjoinRoot.root f else 1) := by
  rw [val_sub', val_sub'] at h
  have := i.isLt; have := j.isLt
  unfold sc
  by_cases h1 : (b : ℕ) ≤ i <;> by_cases h2 : (b : ℕ) ≤ j <;> by_cases h3 : (j : ℕ) < i <;>
    simp only [h1, h2, h3, if_true, if_false] at h ⊢
  all_goals first | (exfalso; omega) | (simp; done) | (field_simp; done) | (simp; ring)

variable (f) in
/-- Entry pattern in original coordinates for `⋂_{c ∈ C} H^f_c`. -/
def OPat (C : Finset ℕ) (N : Matrix (Fin (d + 1)) (Fin (d + 1)) (AdjoinRoot f)) :
    Prop :=
  (∀ i, N i i = 1) ∧ ∀ i j : Fin (d + 1), i ≠ j →
    (∃ l : F, N i j = algebraMap F (AdjoinRoot f) l *
      (if (j : ℕ) < i then AdjoinRoot.root f else 1)) ∧
    (N i j ≠ 0 → ∀ c ∈ C, ¬ inCyc i j c)

lemma OPat.mono {C C' : Finset ℕ} {N : Matrix (Fin (d + 1)) (Fin (d + 1)) (AdjoinRoot f)}
    (h : OPat f C N) (hC : C' ⊆ C) : OPat f C' N :=
  ⟨h.1, fun i j hij => ⟨(h.2 i j hij).1, fun hn c hc => (h.2 i j hij).2 hn c (hC hc)⟩⟩

lemma opat_of_pat (ht : AdjoinRoot.root f ≠ 0) (b : Fin (d + 1)) {S : Set ℕ}
    {M : Matrix (Fin (d + 1)) (Fin (d + 1)) F} (hP : Pat S M) (hD : Diag1 M) {C : Finset ℕ}
    (hCr : ∀ c ∈ C, c < d + 1) (hCS : ∀ c ∈ C, relabel d b c ∉ S) : OPat f C (Φm f b M) := by
  refine ⟨fun i => by simp [Φm, hD (i - b), mul_inv_cancel₀ (sc_ne ht b i)], fun i j hij => ?_⟩
  have hab : i - b ≠ j - b := fun h => hij (sub_left_inj.1 h)
  by_cases hm : M (i - b) (j - b) = 0
  · exact ⟨⟨0, by simp [Φm, hm]⟩, fun h => absurd (by simp [Φm, hm]) h⟩
  obtain ⟨hlt, hS⟩ := hP _ _ hab hm
  have hlt' : ((i - b : Fin (d + 1)) : ℕ) < ((j - b : Fin (d + 1)) : ℕ) := hlt
  refine ⟨⟨_, K3 ht hlt' _⟩, fun _ c hc hcyc => ?_⟩
  have := (K2 hlt' (hCr c hc)).1 hcyc
  exact hCS c hc (hS _ this.1 this.2)

lemma pat_of_opat (ht : AdjoinRoot.root f ≠ 0) (b : Fin (d + 1))
    {M : Matrix (Fin (d + 1)) (Fin (d + 1)) F} {C : Finset ℕ} (hN : OPat f C (Φm f b M))
    (hb : (b : ℕ) ∈ C) (hCr : ∀ c ∈ C, c < d + 1) :
    Pat ((Finset.range (d + 1) \ C.image (relabel d b) : Finset ℕ) : Set ℕ) M ∧ Diag1 M := by
  constructor
  · intro a a' haa hm
    have hij : a + b ≠ a' + b := fun h => haa (add_right_cancel h)
    have hne : Φm f b M (a + b) (a' + b) ≠ 0 := by
      simp only [Φm, add_sub_cancel_right]
      exact mul_ne_zero (mul_ne_zero (sc_ne ht b _) ((_root_.map_ne_zero _).2 hm))
        (inv_ne_zero (sc_ne ht b _))
    have hc := (hN.2 _ _ hij).2 hne
    have hlt := K1 hij (hc _ hb)
    simp only [add_sub_cancel_right] at hlt
    refine ⟨hlt, fun m h1 h2 => ?_⟩
    simp only [Finset.coe_sdiff, Finset.coe_range, Finset.coe_image, Set.mem_sdiff, Set.mem_Iio,
      Set.mem_image, Finset.mem_coe, not_exists, not_and]
    refine ⟨by have := a'.isLt; omega, fun c hcC hcm => hc c hcC ?_⟩
    have hlt' := K1 hij (hc _ hb)
    rw [K2 hlt' (hCr c hcC), hcm]
    simpa only [add_sub_cancel_right] using And.intro h1 h2
  · intro a
    have := hN.1 (a + b)
    simp only [Φm, add_sub_cancel_right] at this
    have h1 := sc_ne ht b (a + b)
    rw [mul_assoc, mul_comm _ (sc f b (a + b))⁻¹, ← mul_assoc, mul_inv_cancel₀ h1, one_mul] at this
    exact alg_inj (by rw [this, map_one])

lemma exists_of_opat (ht : AdjoinRoot.root f ≠ 0) (b : Fin (d + 1))
    {N : Matrix (Fin (d + 1)) (Fin (d + 1)) (AdjoinRoot f)} {C : Finset ℕ} (hN : OPat f C N)
    (hb : (b : ℕ) ∈ C) : ∃ M, Φm f b M = N := by
  have hch : ∀ i j : Fin (d + 1), ∃ l : F, i ≠ j → N i j = algebraMap F (AdjoinRoot f) l *
      (if (j : ℕ) < i then AdjoinRoot.root f else 1) := by
    intro i j
    by_cases h : i = j
    · exact ⟨0, fun h' => absurd h h'⟩
    · obtain ⟨l, hl⟩ := (hN.2 i j h).1; exact ⟨l, fun _ => hl⟩
  choose L hL using hch
  refine ⟨fun a a' => if a = a' then 1 else L (a + b) (a' + b), ?_⟩
  ext i j
  simp only [Φm, sub_add_cancel, sub_left_inj]
  split_ifs with h
  · subst h; rw [hN.1 i, map_one, mul_one, mul_inv_cancel₀ (sc_ne ht b i)]
  · have hs := hL i j h
    by_cases h0 : N i j = 0
    · have hs' : algebraMap F (AdjoinRoot f) (L i j) *
          (if (j : ℕ) < i then AdjoinRoot.root f else 1) = 0 := by rw [← hs]; exact h0
      have : algebraMap F (AdjoinRoot f) (L i j) = 0 := by
        rcases mul_eq_zero.1 hs' with h' | h'
        · exact h'
        · exact absurd h' (by split_ifs <;> simp [ht])
      rw [this, h0]; simp
    · rw [K3 ht (K1 h ((hN.2 i j h).2 h0 _ hb))]; exact hs.symm

lemma sl_of_opat (ht : AdjoinRoot.root f ≠ 0) (b : Fin (d + 1))
    (N : SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f)) {C : Finset ℕ}
    (hN : OPat f C (N : Matrix (Fin (d + 1)) (Fin (d + 1)) (AdjoinRoot f)))
    (hb : (b : ℕ) ∈ C) (hCr : ∀ c ∈ C, c < d + 1) :
    ∃ y : SLd d F, y ∈ UL d F (Finset.range (d + 1) \ C.image (relabel d b)) ∧ Φ ht b y = N := by
  obtain ⟨M, hM⟩ := exists_of_opat ht b hN hb
  rw [← hM] at hN
  obtain ⟨hP, hD⟩ := pat_of_opat ht b hN hb hCr
  refine ⟨mkSL _ M hP hD, mem_UL_of_pat _ hP hD, Subtype.ext ?_⟩
  rw [coe_Φ, coe_mkSL, hM]

end Phi

/-! ## `H^f_c` and its intersections as entry patterns -/

section Hf

variable {f : F[X]} [Fact (Irreducible f)]

lemma tv_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (i j : Fin (d + 1)) (c : R) :
    (transvection i j c).map φ = transvection i j (φ c) := by
  ext a b'
  simp only [transvection, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  split_ifs <;> simp

lemma Φm_tv (ht : AdjoinRoot.root f ≠ 0) (b : Fin (d + 1)) {a a' : Fin (d + 1)}
    (ha : (a : ℕ) + 1 = a') (l : F) :
    Φm f b (transvection a a' l) = transvection (a + b) (a' + b)
      (algebraMap F (AdjoinRoot f) l *
        (if ((a' + b : Fin (d + 1)) : ℕ) < (a + b : Fin (d + 1)) then AdjoinRoot.root f else 1)) := by
  have haa : a ≠ a' := fun h => by subst h; omega
  have hlt : ((a + b - b : Fin (d + 1)) : ℕ) < ((a' + b - b : Fin (d + 1)) : ℕ) := by
    simp only [add_sub_cancel_right]; omega
  have e := K3 ht hlt (algebraMap F (AdjoinRoot f) l)
  have key : ∀ x y : Fin (d + 1), (x = y - b) ↔ (y = x + b) := fun x y =>
    ⟨fun h => by rw [h, sub_add_cancel], fun h => by rw [h, add_sub_cancel_right]⟩
  ext i j
  simp only [Φm, transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
    sub_left_inj]
  simp only [key]
  by_cases hi : i = a + b <;> by_cases hj : j = a' + b
  · subst hi hj
    have : a + b ≠ a' + b := fun h => haa (add_right_cancel h)
    simp only [this, if_false, and_self, if_true, zero_add]; exact e
  all_goals
    have hn : ¬ (a + b = i ∧ a' + b = j) := fun h => by rcases h with ⟨rfl, rfl⟩; tauto
    have hn2 : ¬ (i = a + b ∧ j = a' + b) := fun h => by rcases h with ⟨rfl, rfl⟩; tauto
    simp only [hn, hn2, if_false, add_zero]
    by_cases hij : i = j
    · subst hij; simp only [if_true, map_one, mul_one, add_zero]
      exact mul_inv_cancel₀ (sc_ne ht b i)
    · simp only [hij, if_false, map_zero, mul_zero, zero_mul, add_zero]

omit [Fact (Irreducible f)] in
/-- A transvection as an element of `SL`. -/
def tvSL {R : Type*} [CommRing R] (i j : Fin (d + 1)) (c : R) (h : i ≠ j) :
    SpecialLinearGroup (Fin (d + 1)) R := ⟨transvection i j c, det_transvection_of_ne _ _ h _⟩

omit [Fact (Irreducible f)] in
lemma mk_tv (i j : Fin (d + 1)) (p : F[X]) (g : SpecialLinearGroup (Fin (d + 1)) F[X])
    (hg : (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F[X]) = transvection i j p) :
    ((SpecialLinearGroup.map (AdjoinRoot.mk f) g : SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f)) :
        Matrix (Fin (d + 1)) (Fin (d + 1)) (AdjoinRoot f)) =
      transvection i j (AdjoinRoot.mk f p) := by
  rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, hg]
  exact tv_map _ i j p

lemma Hf_eq (ht : AdjoinRoot.root f ≠ 0) (b : Fin (d + 1)) :
    Hf d F f b = (UL d F (Finset.range (d + 1) \ {0})).map (Φ ht b) := by
  have hb := b.isLt
  unfold Hf Hcol U UL
  rw [MonoidHom.map_closure, MonoidHom.map_closure]
  apply le_antisymm <;> rw [Subgroup.closure_le]
  · rintro _ ⟨g, hg, rfl⟩
    simp only [Set.mem_iUnion] at hg
    obtain ⟨c, hc, l, i, j, hgen⟩ := hg
    rw [Finset.mem_erase, Finset.mem_range] at hc
    apply Subgroup.subset_closure
    have hi := i.isLt; have hj := j.isLt
    rcases hgen with ⟨h1, h2, hic, hjc, hg⟩ | ⟨h0, hic, hjc, hg⟩
    · have hab : (((i - b : Fin (d + 1)) : ℕ)) + 1 = ((j - b : Fin (d + 1)) : ℕ) := by
        rw [val_sub', val_sub']; split_ifs <;> omega
      have hne : i - b ≠ j - b := fun h => by rw [h] at hab; omega
      refine ⟨⟨transvection (i - b) (j - b) l, det_transvection_of_ne _ _ hne _⟩,
        ⟨l, i - b, j - b, ?_, ?_, hab, rfl⟩, ?_⟩
      · simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton]
        constructor
        · exact (j - b).isLt
        · rw [val_sub']; split_ifs <;> omega
      · omega
      · have hij : i ≠ j := fun h => by rw [h] at hic; omega
        apply Subtype.ext
        rw [mk_tv i j _ g hg]
        change Φm f b (transvection (i - b) (j - b) l) = _
        rw [Φm_tv ht b hab, sub_add_cancel, sub_add_cancel, AdjoinRoot.mk_C,
          AdjoinRoot.algebraMap_eq, if_neg (by omega), mul_one]
    · have hab : (((i - b : Fin (d + 1)) : ℕ)) + 1 = ((j - b : Fin (d + 1)) : ℕ) := by
        rw [val_sub', val_sub']; split_ifs <;> omega
      have hne : i - b ≠ j - b := fun h => by rw [h] at hab; omega
      refine ⟨⟨transvection (i - b) (j - b) l, det_transvection_of_ne _ _ hne _⟩,
        ⟨l, i - b, j - b, ?_, ?_, hab, rfl⟩, ?_⟩
      · simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton]
        constructor
        · exact (j - b).isLt
        · rw [val_sub']; split_ifs <;> omega
      · omega
      · have hij : i ≠ j := fun h => by rw [h] at hic; omega
        apply Subtype.ext
        rw [mk_tv i j _ g hg]
        change Φm f b (transvection (i - b) (j - b) l) = _
        rw [Φm_tv ht b hab, sub_add_cancel, sub_add_cancel, map_mul, AdjoinRoot.mk_C,
          AdjoinRoot.mk_X, AdjoinRoot.algebraMap_eq, if_pos (by omega)]
  · rintro _ ⟨y, ⟨l, a, a', ha'S, h1, ha, hy⟩, rfl⟩
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at ha'S
    apply Subgroup.subset_closure
    have hav := a.isLt; have ha'v := a'.isLt
    have hi := Fin.val_add_eq_ite a b; have hj := Fin.val_add_eq_ite a' b
    have hij : a + b ≠ a' + b := fun h => by
      have := congrArg Fin.val h; rw [hi, hj] at this; split_ifs at this <;> omega
    have hΦ : (((Φ ht b) y : SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f)) :
        Matrix (Fin (d + 1)) (Fin (d + 1)) (AdjoinRoot f)) = transvection (a + b) (a' + b)
          (algebraMap F (AdjoinRoot f) l * (if ((a' + b : Fin (d + 1)) : ℕ) <
            (a + b : Fin (d + 1)) then AdjoinRoot.root f else 1)) := by
      rw [coe_Φ, hy, Φm_tv ht b ha]
    have hablt := (a + b).isLt; have ha'blt := (a' + b).isLt
    by_cases hw : ((a' + b : Fin (d + 1)) : ℕ) = 0
    · have hw' : (a' : ℕ) + b = d + 1 := by rw [hj] at hw; split_ifs at hw <;> omega
      refine ⟨tvSL (a + b) (a' + b) (C l * X) hij, ?_, ?_⟩
      · refine Set.mem_iUnion₂.2 ⟨0, ?_, l, a + b, a' + b, Or.inr ⟨rfl, ?_, hw, rfl⟩⟩
        · rw [Finset.mem_erase, Finset.mem_range]; constructor
          · intro h; rw [hj] at hw; split_ifs at hw <;> omega
          · omega
        · rw [hi]; rw [hj] at hw; split_ifs at hw ⊢ <;> omega
      · apply Subtype.ext
        rw [mk_tv _ _ _ _ rfl, hΦ, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X, AdjoinRoot.algebraMap_eq,
          if_pos (by rw [hw, hi]; split_ifs <;> omega)]
    · refine ⟨tvSL (a + b) (a' + b) (C l) hij, ?_, ?_⟩
      · refine Set.mem_iUnion₂.2 ⟨((a' + b : Fin (d + 1)) : ℕ), ?_, l, a + b, a' + b,
          Or.inl ⟨by omega, by omega, ?_, rfl, rfl⟩⟩
        · rw [Finset.mem_erase, Finset.mem_range]; refine ⟨?_, (a' + b).isLt⟩
          rw [hj]; split_ifs <;> omega
        · rw [hi]; rw [hj] at hw ⊢; split_ifs at hw ⊢ <;> omega
      · apply Subtype.ext
        rw [mk_tv _ _ _ _ rfl, hΦ, AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq,
          if_neg (by rw [hi, hj]; rw [hj] at hw; split_ifs at hw ⊢ <;> omega), mul_one]

lemma Hf_char (ht : AdjoinRoot.root f ≠ 0) {c : ℕ} (hc : c < d + 1)
    (N : SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f)) :
    N ∈ Hf d F f c ↔ OPat f {c} (N : Matrix (Fin (d + 1)) (Fin (d + 1)) (AdjoinRoot f)) := by
  have e := Hf_eq ht (⟨c, hc⟩ : Fin (d + 1))
  simp only [Fin.val_mk] at e
  rw [e]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hP, hD⟩ := pat_of_mem_UL hy
    exact opat_of_pat ht _ hP hD (by simpa using hc) (by simp [relabel_self hc])
  · intro h
    obtain ⟨y, hy, rfl⟩ := sl_of_opat ht ⟨c, hc⟩ N h (by simp) (by simpa using hc)
    refine ⟨y, ?_, rfl⟩
    simpa [relabel_self hc] using hy

/-- `⋂_{c ∈ C} H^f_c = Φ_b(U_{[d] \ relabel_b(C)})` for `b ∈ C`. -/
lemma MG (ht : AdjoinRoot.root f ≠ 0) (b : Fin (d + 1)) {C : Finset ℕ} (hb : (b : ℕ) ∈ C)
    (hCr : ∀ c ∈ C, c < d + 1) (N : SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f)) :
    (∀ c ∈ C, N ∈ Hf d F f c) ↔
      ∃ y ∈ UL d F (Finset.range (d + 1) \ C.image (relabel d b)), Φ ht b y = N := by
  constructor
  · intro h
    have h0 := (Hf_char ht (hCr _ hb) N).1 (h _ hb)
    have hO : OPat f C (N : Matrix (Fin (d + 1)) (Fin (d + 1)) (AdjoinRoot f)) :=
      ⟨h0.1, fun i j hij => ⟨(h0.2 i j hij).1, fun hn c hc =>
        (((Hf_char ht (hCr c hc) N).1 (h c hc)).2 i j hij).2 hn c (Finset.mem_singleton_self c)⟩⟩
    exact sl_of_opat ht b N hO hb hCr
  · rintro ⟨y, hy, rfl⟩ c hc
    obtain ⟨hP, hD⟩ := pat_of_mem_UL hy
    have hO := opat_of_pat (f := f) ht b hP hD hCr (fun c hc h => by
      simp only [Finset.coe_sdiff, Finset.coe_range, Finset.coe_image, Set.mem_sdiff,
        Set.mem_image, Finset.mem_coe, not_exists, not_and] at h
      exact h.2 c hc rfl)
    exact (Hf_char ht (hCr c hc) _).2 (hO.mono (by simpa using hc))

end Hf

/-! ## Transfer of trivial `H¹` along a vertex bijection respecting faces -/

section Transfer

variable {V₁ V₂ : Type*} (X₁ : WComplex V₁) (X₂ : WComplex V₂) (Ψ : V₂ → V₁)

lemma face_image (h1 : ∀ τ ∈ X₂.tops, ∃ τ₁ ∈ X₁.tops, τ.image Ψ ⊆ τ₁) {s : Finset V₂}
    (hs : X₂.IsFace s) : X₁.IsFace (s.image Ψ) := by
  obtain ⟨τ, hτ, hsτ⟩ := hs
  obtain ⟨τ₁, h1', h2'⟩ := h1 τ hτ
  exact ⟨τ₁, h1', (Finset.image_subset_image hsτ).trans h2'⟩

/-- If `Ψ : V₂ → V₁` is injective, maps maximal faces of `X₂` into maximal faces of `X₁`, and
every maximal face of `X₁` is covered by the image of a maximal face of `X₂`, then trivial `H¹`
transfers from `X₂` to `X₁`. -/
theorem h1_transfer {Λ : Type*} [Group Λ] (hinj : Function.Injective Ψ)
    (h1 : ∀ τ ∈ X₂.tops, ∃ τ₁ ∈ X₁.tops, τ.image Ψ ⊆ τ₁)
    (h2 : ∀ τ₁ ∈ X₁.tops, ∃ τ ∈ X₂.tops, τ₁ ⊆ τ.image Ψ)
    (h : X₂.H1Trivial Λ) : X₁.H1Trivial Λ := by
  intro ϕ hϕ
  have hE : ∀ a b, X₂.IsEdge a b → X₁.IsEdge (Ψ a) (Ψ b) := by
    rintro a b ⟨hab, hf⟩
    refine ⟨fun e => hab (hinj e), ?_⟩
    simpa [Finset.image_insert, Finset.image_singleton] using face_image X₁ X₂ Ψ h1 hf
  have hT : ∀ a b c, X₂.IsTri a b c → X₁.IsTri (Ψ a) (Ψ b) (Ψ c) := by
    rintro a b c ⟨h1', h2', h3', hf⟩
    refine ⟨fun e => h1' (hinj e), fun e => h2' (hinj e), fun e => h3' (hinj e), ?_⟩
    simpa [Finset.image_insert, Finset.image_singleton] using face_image X₁ X₂ Ψ h1 hf
  obtain ⟨g', hg'⟩ := h (fun a b => ϕ (Ψ a) (Ψ b))
    ⟨fun a b hab => hϕ.1 _ _ (hE a b hab), fun a b c habc => hϕ.2 _ _ _ (hT a b c habc)⟩
  refine ⟨fun u => if hu : ∃ a, Ψ a = u then g' (Classical.choose hu) else 1, fun u v huv => ?_⟩
  obtain ⟨τ₁, hτ₁, hsub⟩ := huv.2
  obtain ⟨τ, hτ, hsub'⟩ := h2 τ₁ hτ₁
  have hu : u ∈ τ.image Ψ := hsub' (hsub (by simp))
  have hv : v ∈ τ.image Ψ := hsub' (hsub (by simp))
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hu
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hv
  have hab : X₂.IsEdge a b := ⟨fun e => huv.1 (congrArg Ψ e), τ, hτ, by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption⟩
  have e1 : ∃ a', Ψ a' = Ψ a := ⟨a, rfl⟩
  have e2 : ∃ b', Ψ b' = Ψ b := ⟨b, rfl⟩
  have := hg' a b hab
  simp only [WComplex.d0] at this ⊢
  rw [dif_pos e1, dif_pos e2, hinj (Classical.choose_spec e1), hinj (Classical.choose_spec e2)]
  exact this

end Transfer

/-! ## Colored faces of the KMS complex -/

section Complex

omit [Field F] in
lemma mem_image' {α β : Type*} {inst : DecidableEq β} {g : α → β} {s : Finset α} {b : β} :
    b ∈ @Finset.image α β inst g s ↔ ∃ a ∈ s, g a = b := Finset.mem_image

variable {f : F[X]}

variable (F) in
/-- `τ_K` for the chamber `τ = gH`: its vertices with colour in `K`. -/
noncomputable def part (f : F[X]) (g : SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f))
    (K : Finset ℕ) :
    Finset (Σ i : Fin (d + 1), SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f) ⧸ Hf d F f i) :=
  (Finset.univ.filter (fun i : Fin (d + 1) => (i : ℕ) ∈ K)).image
    (fun i => ⟨i, (g : SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f) ⧸ Hf d F f i)⟩)

lemma mem_part {g : SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f)} {K : Finset ℕ}
    {x : Σ i : Fin (d + 1), SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f) ⧸ Hf d F f i} :
    x ∈ part F f g K ↔
      (x.1 : ℕ) ∈ K ∧ x.2 = (g : SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f) ⧸ _) := by
  obtain ⟨i, q⟩ := x
  simp only [part, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj, h⟩; cases h; exact ⟨hj, rfl⟩
  · rintro ⟨hi, rfl⟩; exact ⟨i, hi, rfl⟩

lemma part_col {g : SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f)} {K : Finset ℕ}
    (hK : K ⊆ Finset.range (d + 1)) : (part F f g K).image (kmsCol d F f) = K := by
  ext c
  simp only [Finset.mem_image, mem_part, kmsCol]
  constructor
  · rintro ⟨x, ⟨hx, -⟩, rfl⟩; exact hx
  · intro hc
    exact ⟨⟨⟨c, Finset.mem_range.1 (hK hc)⟩, g⟩, ⟨hc, rfl⟩, rfl⟩

lemma part_eq_iff {g g' : SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f)} {K : Finset ℕ}
    (hK : K ⊆ Finset.range (d + 1)) :
    part F f g K = part F f g' K ↔ ∀ k ∈ K, g⁻¹ * g' ∈ Hf d F f k := by
  constructor
  · intro h k hk
    have hk' : k < d + 1 := Finset.mem_range.1 (hK hk)
    have hm : (⟨⟨k, hk'⟩, (g : SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f) ⧸ _)⟩ :
        Σ i : Fin (d + 1), SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f) ⧸ Hf d F f i) ∈
        part F f g' K := h ▸ mem_part.2 ⟨hk, rfl⟩
    exact QuotientGroup.eq.1 (mem_part.1 hm).2
  · intro h
    ext ⟨i, q⟩
    simp only [mem_part]
    constructor
    · rintro ⟨hi, rfl⟩; exact ⟨hi, QuotientGroup.eq.2 (h _ hi)⟩
    · rintro ⟨hi, rfl⟩
      refine ⟨hi, QuotientGroup.eq.2 ?_⟩
      have := inv_mem (h _ hi)
      simpa using this

lemma part_ne {g g' : SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f)} {K K' : Finset ℕ}
    (hK : K ⊆ Finset.range (d + 1)) (hK' : K' ⊆ Finset.range (d + 1))
    (h : part F f g K = part F f g' K') : K = K' := by
  rw [← part_col (g := g) hK, ← part_col (g := g') hK', h]

lemma filt_mem (g : SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f)) (K : Finset ℕ)
    {inst : DecidableEq (Σ i : Fin (d + 1), SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f) ⧸
      Hf d F f i)} {p : DecidablePred (fun v : Σ i : Fin (d + 1),
        SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f) ⧸ Hf d F f i => kmsCol d F f v ∈ K)}
    (x : Σ i : Fin (d + 1), SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f) ⧸ Hf d F f i) :
    x ∈ @Finset.filter _ (fun v => kmsCol d F f v ∈ K) p (@Finset.image _ _ inst
      (fun i : Fin (d + 1) => (⟨i, (g : _ ⧸ Hf d F f i)⟩ :
        Σ i : Fin (d + 1), SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f) ⧸ Hf d F f i))
      Finset.univ) ↔ x ∈ part F f g K := by
  rw [Finset.mem_filter, Finset.mem_image, mem_part]
  simp only [Finset.mem_univ, true_and, kmsCol]
  obtain ⟨i, q⟩ := x
  constructor
  · rintro ⟨⟨j, hj⟩, hi⟩; cases hj; exact ⟨hi, rfl⟩
  · rintro ⟨hi, hq⟩; exact ⟨⟨i, by simp only at hq; rw [hq]⟩, hi⟩

lemma tops_FI (hG : Finite (SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f)))
    {I : Finset (Finset ℕ)} (hI : ∀ K ∈ I, K ⊆ Finset.range (d + 1)) (Tp) :
    Tp ∈ (kmsFI d F f I).tops ↔ ∃ g, ∀ P, P ∈ Tp ↔ ∃ K ∈ I, part F f g K = P := by
  simp only [kmsFI, kmsX, WComplex.coloredFaces, cosetComplex, dif_pos hG, Finset.mem_image,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨τ, ⟨⟨g, rfl⟩, -⟩, rfl⟩
    refine ⟨g, fun P => ?_⟩
    rw [mem_image']
    refine exists_congr fun K => and_congr_right fun _ => ?_
    rw [Finset.ext (filt_mem g K)]
  · rintro ⟨g, hg⟩
    refine ⟨_, ⟨⟨g, rfl⟩, fun K hK => ?_⟩, ?_⟩
    · rw [Finset.ext (filt_mem g K)]; exact part_col (hI K hK)
    · ext P
      rw [mem_image', hg]
      refine exists_congr fun K => and_congr_right fun _ => ?_
      rw [Finset.ext (filt_mem g K)]

lemma tops_link {V : Type*} (X : WComplex V) (v : V) (Tp : Finset V) :
    Tp ∈ (X.link {v}).tops ↔ ∃ T' ∈ X.tops, v ∈ T' ∧ ∀ u, u ∈ Tp ↔ u ∈ T' ∧ u ≠ v := by
  simp only [WComplex.link, mem_image', Finset.mem_filter, Finset.singleton_subset_iff]
  constructor
  · rintro ⟨T', ⟨h1, h2⟩, rfl⟩
    exact ⟨T', h1, h2, fun u => by simp only [Finset.mem_sdiff, Finset.mem_singleton]⟩
  · rintro ⟨T', h1, h2, h3⟩
    exact ⟨T', ⟨h1, h2⟩, by ext u; simp only [Finset.mem_sdiff, Finset.mem_singleton, h3]⟩

lemma tops_linkY {I : Finset (Finset ℕ)} {J : Finset ℕ} [hfin : Finite (UL d F (compl d J))]
    (τ) : τ ∈ (linkY d F I J).tops ↔ ∃ x : UL d F (compl d J),
      ∀ p, p ∈ τ ↔ p.2 = (x : UL d F (compl d J) ⧸ linkH d F I J p.1) := by
  simp only [linkY, cosetComplex, dif_pos hfin, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨x, fun p => ?_⟩
    rw [mem_image']
    obtain ⟨K, q⟩ := p
    constructor
    · rintro ⟨K', -, h⟩; cases h; rfl
    · intro h; exact ⟨K, Finset.mem_univ _, by simp only at h; rw [h]⟩
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    ext p
    rw [mem_image', hx]
    obtain ⟨K, q⟩ := p
    constructor
    · rintro ⟨K', -, h⟩; cases h; rfl
    · intro h; exact ⟨K, Finset.mem_univ _, by simp only at h; rw [h]⟩

end Complex

/-! ## The vertex link of `F^I X` at a vertex of colour `J` -/

section Main

omit [Field F] in
lemma base_mem {J : Finset ℕ} (hne : J.Nonempty) : base J ∈ J := by
  simp only [base, dif_pos hne]; exact J.min'_mem hne

variable {f : F[X]} [Fact (Irreducible f)]

/-- `⟨K, x(H_J ∩ H_K)⟩ ↦ (g₀ Φ(x))_K`. -/
noncomputable def Psi (ht : AdjoinRoot.root f ≠ 0) (b : Fin (d + 1)) (I : Finset (Finset ℕ))
    (J : Finset ℕ) (g₀ : SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f))
    (p : Σ K : {K // K ∈ I.erase J}, (UL d F (compl d J)) ⧸ linkH d F I J K) :
    Finset (Σ i : Fin (d + 1), SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f) ⧸ Hf d F f i) :=
  part F f (g₀ * Φ ht b ((Quotient.out p.2 : UL d F (compl d J)) : SLd d F)) p.1.1

end Main

end PolySwap.KMS.P313L
end Part_LinkAux

section Part_LinkAux2

open Classical

namespace PolySwap.KMS.P313L

open PolySwap.KMS

/-! ## Transfer of Garland weights and `h¹` along an isomorphism onto the image -/

section Iso

variable {V₁ V₂ : Type*} (X₁ : WComplex V₁) (X₂ : WComplex V₂) (Ψ : V₂ → V₁)

lemma tops_eq (h1 : ∀ τ ∈ X₂.tops, τ.image Ψ ∈ X₁.tops)
    (h2 : ∀ τ₁ ∈ X₁.tops, ∃ τ ∈ X₂.tops, τ.image Ψ = τ₁) :
    X₁.tops = X₂.tops.image (fun τ => τ.image Ψ) := by
  ext τ₁
  rw [Finset.mem_image]
  constructor
  · intro h; exact h2 τ₁ h
  · rintro ⟨τ, hτ, rfl⟩; exact h1 τ hτ

lemma gw_image (hinj : Function.Injective Ψ) (h1 : ∀ τ ∈ X₂.tops, τ.image Ψ ∈ X₁.tops)
    (h2 : ∀ τ₁ ∈ X₁.tops, ∃ τ ∈ X₂.tops, τ.image Ψ = τ₁) (c : ℝ) (hc : c ≠ 0)
    (hwt : ∀ τ ∈ X₂.tops, X₁.wt (τ.image Ψ) = c * X₂.wt τ) (s : Finset V₂) :
    X₁.gw (s.image Ψ) = X₂.gw s := by
  have hI : Set.InjOn (fun τ : Finset V₂ => τ.image Ψ) X₂.tops :=
    fun a _ b _ h => Finset.image_injective hinj h
  unfold WComplex.gw
  rw [tops_eq X₁ X₂ Ψ h1 h2, Finset.filter_image, Finset.sum_image (fun a ha b hb h =>
    hI (Finset.mem_filter.1 ha).1 (Finset.mem_filter.1 hb).1 h), Finset.sum_image hI]
  have e1 : ∑ τ ∈ X₂.tops.filter (fun τ => s.image Ψ ⊆ τ.image Ψ),
      X₁.wt (τ.image Ψ) / (((τ.image Ψ).card.choose (s.image Ψ).card : ℕ) : ℝ) =
      c * ∑ τ ∈ X₂.tops.filter (fun τ => s ⊆ τ), X₂.wt τ / ((τ.card.choose s.card : ℕ) : ℝ) := by
    rw [Finset.mul_sum]
    have hf : X₂.tops.filter (fun τ => s.image Ψ ⊆ τ.image Ψ) = X₂.tops.filter (fun τ => s ⊆ τ) :=
      Finset.filter_congr (fun τ _ => Finset.image_subset_image_iff hinj)
    rw [hf]
    refine Finset.sum_congr rfl fun τ hτ => ?_
    rw [hwt τ (Finset.mem_filter.1 hτ).1, Finset.card_image_of_injective _ hinj,
      Finset.card_image_of_injective _ hinj, mul_div_assoc]
  have e2 : ∑ τ ∈ X₂.tops, X₁.wt (τ.image Ψ) = c * ∑ τ ∈ X₂.tops, X₂.wt τ := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun τ hτ => hwt τ hτ
  rw [e1, e2, mul_div_mul_left _ _ hc]

lemma gw_pos (hwt : ∀ τ ∈ X₁.tops, 0 < X₁.wt τ) {σ τ : Finset V₁} (hτ : τ ∈ X₁.tops)
    (hs : σ ⊆ τ) : 0 < X₁.gw σ := by
  unfold WComplex.gw
  apply div_pos
  · apply Finset.sum_pos'
    · intro τ' hτ'
      have := hwt τ' (Finset.mem_filter.1 hτ').1
      positivity
    · refine ⟨τ, Finset.mem_filter.2 ⟨hτ, hs⟩, ?_⟩
      have := Nat.choose_pos (Finset.card_le_card hs)
      have := hwt τ hτ
      positivity
  · exact Finset.sum_pos (fun τ' h => hwt τ' h) ⟨_, hτ⟩

lemma mem_faces_iff (hinj : Function.Injective Ψ) (h1 : ∀ τ ∈ X₂.tops, τ.image Ψ ∈ X₁.tops)
    (h2 : ∀ τ₁ ∈ X₁.tops, ∃ τ ∈ X₂.tops, τ.image Ψ = τ₁) (k : ℕ) (s : Finset V₁) :
    s ∈ X₁.facesCard k ↔ ∃ s' ∈ X₂.facesCard k, s'.image Ψ = s := by
  simp only [WComplex.facesCard, WComplex.faces, Finset.mem_filter, Finset.mem_biUnion,
    Finset.mem_powerset]
  constructor
  · rintro ⟨⟨τ₁, hτ₁, hs⟩, hk⟩
    obtain ⟨τ, hτ, rfl⟩ := h2 τ₁ hτ₁
    refine ⟨τ.filter (fun a => Ψ a ∈ s), ⟨⟨τ, hτ, Finset.filter_subset _ _⟩, ?_⟩, ?_⟩
    · rw [← hk, ← Finset.card_image_of_injective _ hinj]
      congr 1
      ext x
      simp only [Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨a, ⟨-, ha⟩, rfl⟩; exact ha
      · intro hx
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 (hs hx)
        exact ⟨a, ⟨ha, hx⟩, rfl⟩
    · ext x
      simp only [Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨a, ⟨-, ha⟩, rfl⟩; exact ha
      · intro hx
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 (hs hx)
        exact ⟨a, ⟨ha, hx⟩, rfl⟩
  · rintro ⟨s', ⟨⟨τ, hτ, hs'⟩, hk⟩, rfl⟩
    exact ⟨⟨_, h1 τ hτ, Finset.image_subset_image hs'⟩,
      by rw [Finset.card_image_of_injective _ hinj, hk]⟩

lemma facesCard_eq (hinj : Function.Injective Ψ) (h1 : ∀ τ ∈ X₂.tops, τ.image Ψ ∈ X₁.tops)
    (h2 : ∀ τ₁ ∈ X₁.tops, ∃ τ ∈ X₂.tops, τ.image Ψ = τ₁) (k : ℕ) :
    X₁.facesCard k = (X₂.facesCard k).image (fun s => s.image Ψ) := by
  ext s
  rw [mem_faces_iff X₁ X₂ Ψ hinj h1 h2, Finset.mem_image]

lemma sum_transfer (hinj : Function.Injective Ψ) (h1 : ∀ τ ∈ X₂.tops, τ.image Ψ ∈ X₁.tops)
    (h2 : ∀ τ₁ ∈ X₁.tops, ∃ τ ∈ X₂.tops, τ.image Ψ = τ₁)
    (hgw : ∀ s, X₁.gw (s.image Ψ) = X₂.gw s) (k : ℕ) (P₁ : Finset V₁ → Prop)
    (P₂ : Finset V₂ → Prop) (hP : ∀ s, P₁ (s.image Ψ) ↔ P₂ s) :
    ∑ e ∈ (X₁.facesCard k).filter P₁, X₁.gw e = ∑ e ∈ (X₂.facesCard k).filter P₂, X₂.gw e := by
  rw [facesCard_eq X₁ X₂ Ψ hinj h1 h2, Finset.filter_image, Finset.sum_image
    (fun a _ b _ h => Finset.image_injective hinj h)]
  exact Finset.sum_congr (Finset.filter_congr fun s _ => hP s) fun s _ => hgw s

lemma pair_iff (hinj : Function.Injective Ψ) {Q₁ : V₁ → V₁ → Prop} {Q₂ : V₂ → V₂ → Prop}
    (hQ : ∀ a b, Q₁ (Ψ a) (Ψ b) ↔ Q₂ a b) (s : Finset V₂) :
    (∃ u v, s.image Ψ = {u, v} ∧ Q₁ u v) ↔ ∃ a b, s = {a, b} ∧ Q₂ a b := by
  constructor
  · rintro ⟨u, v, hs, hq⟩
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 (hs ▸ (by simp : u ∈ ({u, v} : Finset V₁)))
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 (hs ▸ (by simp : v ∈ ({Ψ a, v} : Finset V₁)))
    refine ⟨a, b, Finset.image_injective hinj ?_, (hQ a b).1 hq⟩
    rw [hs]; simp [Finset.image_insert]
  · rintro ⟨a, b, rfl, hq⟩
    exact ⟨Ψ a, Ψ b, by simp [Finset.image_insert], (hQ a b).2 hq⟩

lemma triple_iff (hinj : Function.Injective Ψ) {Q₁ : V₁ → V₁ → V₁ → Prop}
    {Q₂ : V₂ → V₂ → V₂ → Prop}
    (hQ : ∀ a b c, Q₁ (Ψ a) (Ψ b) (Ψ c) ↔ Q₂ a b c) (s : Finset V₂) :
    (∃ u v w, s.image Ψ = {u, v, w} ∧ Q₁ u v w) ↔ ∃ a b c, s = {a, b, c} ∧ Q₂ a b c := by
  constructor
  · rintro ⟨u, v, w, hs, hq⟩
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 (hs ▸ (by simp : u ∈ ({u, v, w} : Finset V₁)))
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 (hs ▸ (by simp : v ∈ ({Ψ a, v, w} : Finset V₁)))
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1
      (hs ▸ (by simp : w ∈ ({Ψ a, Ψ b, w} : Finset V₁)))
    refine ⟨a, b, c, Finset.image_injective hinj ?_, (hQ a b c).1 hq⟩
    rw [hs]; simp [Finset.image_insert]
  · rintro ⟨a, b, c, rfl, hq⟩
    exact ⟨Ψ a, Ψ b, Ψ c, by simp [Finset.image_insert], (hQ a b c).2 hq⟩

/-- `h¹ ≥ β` transfers along an injective vertex map inducing a bijection of maximal faces and
preserving Garland weights. -/
theorem hone_transfer {Λ : Type*} [Group Λ] (β : ℝ) (hinj : Function.Injective Ψ)
    (h1 : ∀ τ ∈ X₂.tops, τ.image Ψ ∈ X₁.tops)
    (h2 : ∀ τ₁ ∈ X₁.tops, ∃ τ ∈ X₂.tops, τ.image Ψ = τ₁)
    (hgw : ∀ s, X₁.gw (s.image Ψ) = X₂.gw s) (h : X₂.HOneGe Λ β) : X₁.HOneGe Λ β := by
  have hF : ∀ s, X₂.IsFace s → X₁.IsFace (s.image Ψ) := by
    rintro s ⟨τ, hτ, hs⟩; exact ⟨_, h1 τ hτ, Finset.image_subset_image hs⟩
  have hE : ∀ a b, X₂.IsEdge a b → X₁.IsEdge (Ψ a) (Ψ b) := by
    rintro a b ⟨hab, hf⟩
    refine ⟨fun e => hab (hinj e), ?_⟩
    simpa [Finset.image_insert, Finset.image_singleton] using hF _ hf
  have hT : ∀ a b c, X₂.IsTri a b c → X₁.IsTri (Ψ a) (Ψ b) (Ψ c) := by
    rintro a b c ⟨h1', h2', h3', hf⟩
    refine ⟨fun e => h1' (hinj e), fun e => h2' (hinj e), fun e => h3' (hinj e), ?_⟩
    simpa [Finset.image_insert, Finset.image_singleton] using hF _ hf
  -- faces of `X₁` lie in the range of `Ψ`
  have hR : ∀ s, X₁.IsFace s → ∃ s', X₂.IsFace s' ∧ s'.image Ψ = s := by
    rintro s ⟨τ₁, hτ₁, hs⟩
    obtain ⟨τ, hτ, rfl⟩ := h2 τ₁ hτ₁
    refine ⟨τ.filter (fun a => Ψ a ∈ s), ⟨τ, hτ, Finset.filter_subset _ _⟩, ?_⟩
    ext x
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨a, ⟨-, ha⟩, rfl⟩; exact ha
    · intro hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 (hs hx)
      exact ⟨a, ⟨ha, hx⟩, rfl⟩
  have hEb : ∀ u v, X₁.IsEdge u v → ∃ a b, Ψ a = u ∧ Ψ b = v ∧ X₂.IsEdge a b := by
    rintro u v ⟨huv, hf⟩
    obtain ⟨s', hs', he⟩ := hR _ hf
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 (he ▸ (by simp : u ∈ ({u, v} : Finset V₁)))
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 (he ▸ (by simp : v ∈ ({Ψ a, v} : Finset V₁)))
    refine ⟨a, b, rfl, rfl, fun e => huv (by rw [e]), ?_⟩
    obtain ⟨τ, hτ, hsub⟩ := hs'
    refine ⟨τ, hτ, fun x hx => ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hsub ha
    · exact hsub hb
  have hTb : ∀ u v w, X₁.IsTri u v w →
      ∃ a b c, Ψ a = u ∧ Ψ b = v ∧ Ψ c = w ∧ X₂.IsTri a b c := by
    rintro u v w ⟨huv, hvw, huw, hf⟩
    obtain ⟨s', hs', he⟩ := hR _ hf
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 (he ▸ (by simp : u ∈ ({u, v, w} : Finset V₁)))
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 (he ▸ (by simp : v ∈ ({Ψ a, v, w} : Finset V₁)))
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1
      (he ▸ (by simp : w ∈ ({Ψ a, Ψ b, w} : Finset V₁)))
    refine ⟨a, b, c, rfl, rfl, rfl, fun e => huv (by rw [e]), fun e => hvw (by rw [e]),
      fun e => huw (by rw [e]), ?_⟩
    obtain ⟨τ, hτ, hsub⟩ := hs'
    refine ⟨τ, hτ, fun x hx => ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hsub ha
    · exact hsub hb
    · exact hsub hc
  intro ϕ hϕ
  obtain ⟨ψ₂, hψ₂, hβ⟩ := h (fun a b => ϕ (Ψ a) (Ψ b)) (fun a b hab => hϕ _ _ (hE a b hab))
  let ψ : V₁ → V₁ → Λ := fun u v =>
    if hu : ∃ a, Ψ a = u then
      if hv : ∃ b, Ψ b = v then ψ₂ (Classical.choose hu) (Classical.choose hv) else 1
    else 1
  have hψ : ∀ a b, ψ (Ψ a) (Ψ b) = ψ₂ a b := by
    intro a b
    have e1 : ∃ a', Ψ a' = Ψ a := ⟨a, rfl⟩
    have e2 : ∃ b', Ψ b' = Ψ b := ⟨b, rfl⟩
    simp only [ψ, dif_pos e1, dif_pos e2]
    rw [hinj (Classical.choose_spec e1), hinj (Classical.choose_spec e2)]
  refine ⟨ψ, ⟨fun u v huv => ?_, fun u v w huvw => ?_⟩, ?_⟩
  · obtain ⟨a, b, rfl, rfl, hab⟩ := hEb u v huv
    rw [hψ, hψ]; exact hψ₂.1 a b hab
  · obtain ⟨a, b, c, rfl, rfl, rfl, habc⟩ := hTb u v w huvw
    simp only [WComplex.d1] at hψ₂ ⊢
    rw [hψ, hψ, hψ]; exact hψ₂.2 a b c habc
  · have ed : X₁.dist1 ϕ ψ = X₂.dist1 (fun a b => ϕ (Ψ a) (Ψ b)) ψ₂ := by
      unfold WComplex.dist1
      exact sum_transfer X₁ X₂ Ψ hinj h1 h2 hgw 2 _ _
        (pair_iff Ψ hinj (fun a b => by rw [hψ]))
    have en : X₁.normD1 ϕ = X₂.normD1 (fun a b => ϕ (Ψ a) (Ψ b)) := by
      unfold WComplex.normD1
      exact sum_transfer X₁ X₂ Ψ hinj h1 h2 hgw 3 _ _
        (triple_iff Ψ hinj (fun a b c => Iff.rfl))
    rw [ed, en]; exact hβ

end Iso

end PolySwap.KMS.P313L
end Part_LinkAux2

section Part_LinkAux3

open Classical Polynomial Matrix

noncomputable section

namespace PolySwap.KMS.P313L

open PolySwap.KMS

/-! ## Left translation on the KMS complex -/

section Translate

variable {d : ℕ} {F : Type*} [Field F] {f : F[X]}

/-- Left multiplication by `g` on the vertices `⟨i, xH_i⟩`. -/
def Lg (g : SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f))
    (p : Σ i : Fin (d + 1), SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f) ⧸ Hf d F f i) :
    Σ i : Fin (d + 1), SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f) ⧸ Hf d F f i :=
  ⟨p.1, g • p.2⟩

lemma Lg_inj (g : SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f)) :
    Function.Injective (Lg (F := F) g) := by
  refine Function.LeftInverse.injective (g := Lg g⁻¹) fun p => ?_
  obtain ⟨i, q⟩ := p
  exact Sigma.ext rfl (heq_of_eq (inv_smul_smul g q))

variable (F) in
/-- The chamber `{⟨i, gH_i⟩ : i ∈ [d]}`. -/
def chamber (f : F[X]) (g : SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f)) :
    Finset (Σ i : Fin (d + 1), SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f) ⧸ Hf d F f i) :=
  Finset.univ.image (fun i => ⟨i, (g : SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f) ⧸ _)⟩)

lemma mem_chamber {g : SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f)}
    {x : Σ i : Fin (d + 1), SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f) ⧸ Hf d F f i} :
    x ∈ chamber F f g ↔ x.2 = (g : SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f) ⧸ _) := by
  obtain ⟨i, q⟩ := x
  simp only [chamber, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, h⟩; cases h; rfl
  · rintro rfl; exact ⟨i, rfl⟩

lemma tops_kmsX (hG : Finite (SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f))) (τ) :
    τ ∈ (kmsX d F f).tops ↔ ∃ g, chamber F f g = τ := by
  simp only [kmsX, cosetComplex, dif_pos hG, Finset.mem_image, Finset.mem_univ, true_and]
  refine exists_congr fun g => ?_
  constructor <;> rintro rfl <;> ext x <;> simp only [chamber, Finset.mem_image]

lemma chamber_Lg (g g' : SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f)) :
    (chamber F f g').image (Lg g) = chamber F f (g * g') := by
  ext ⟨i, q⟩
  rw [mem_image', mem_chamber]
  constructor
  · rintro ⟨⟨j, q'⟩, h, he⟩
    rw [mem_chamber] at h
    simp only [Lg] at he h
    cases he; subst h; rfl
  · intro h
    refine ⟨⟨i, (g' : _ ⧸ _)⟩, mem_chamber.2 rfl, ?_⟩
    simp only at h
    rw [h]; rfl

lemma part_Lg (g g' : SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f)) (K : Finset ℕ) :
    (part F f g' K).image (Lg g) = part F f (g * g') K := by
  ext ⟨i, q⟩
  rw [mem_image', mem_part]
  constructor
  · rintro ⟨⟨j, q'⟩, h, he⟩
    rw [mem_part] at h
    simp only [Lg] at he h
    cases he; obtain ⟨h1, rfl⟩ := h; exact ⟨h1, rfl⟩
  · rintro ⟨h1, h⟩
    refine ⟨⟨i, (g' : _ ⧸ _)⟩, mem_part.2 ⟨h1, rfl⟩, ?_⟩
    simp only at h
    rw [h]; rfl

lemma part_sub_chamber (g : SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f)) (K : Finset ℕ) :
    part F f g K ⊆ chamber F f g := fun _ hx => mem_chamber.2 (mem_part.1 hx).2

lemma kmsX_wt (τ) : (kmsX d F f).wt τ = 1 := rfl

lemma gw_part_Lg (hG : Finite (SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f)))
    (g : SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f)) (K : Finset ℕ) :
    (kmsX d F f).gw (part F f g K) = (kmsX d F f).gw (part F f 1 K) := by
  have e := part_Lg (F := F) (f := f) g 1 K
  rw [mul_one] at e
  rw [← e]
  have h1 : ∀ τ ∈ (kmsX d F f).tops, τ.image (Lg g) ∈ (kmsX d F f).tops := by
    intro τ hτ
    obtain ⟨g', rfl⟩ := (tops_kmsX hG τ).1 hτ
    rw [chamber_Lg]; exact (tops_kmsX hG _).2 ⟨_, rfl⟩
  have h2 : ∀ τ ∈ (kmsX d F f).tops, ∃ τ' ∈ (kmsX d F f).tops, τ'.image (Lg g) = τ := by
    intro τ hτ
    obtain ⟨g', rfl⟩ := (tops_kmsX hG τ).1 hτ
    refine ⟨chamber F f (g⁻¹ * g'), (tops_kmsX hG _).2 ⟨_, rfl⟩, ?_⟩
    rw [chamber_Lg, mul_inv_cancel_left]
  convert gw_image _ _ _ (Lg_inj g) (by convert h1) (by convert h2) 1 one_ne_zero
    (fun τ _ => (one_mul (1 : ℝ)).symm) (part F f 1 K)

lemma gw_part_pos (hG : Finite (SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f)))
    (g : SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f)) (K : Finset ℕ) :
    0 < (kmsX d F f).gw (part F f g K) :=
  gw_pos _ (fun _ _ => one_pos) ((tops_kmsX hG _).2 ⟨g, rfl⟩) (part_sub_chamber g K)

lemma sup_part (I : Finset (Finset ℕ)) (g : SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f)) :
    (I.image (part F f g)).sup id = part F f g (I.sup id) := by
  ext x
  rw [Finset.mem_sup, mem_part, Finset.mem_sup]
  simp only [Finset.mem_image, id, exists_exists_and_eq_and, mem_part]
  constructor
  · rintro ⟨K, hK, h1, h2⟩; exact ⟨⟨K, hK, h1⟩, h2⟩
  · rintro ⟨⟨K, hK, h1⟩, h2⟩; exact ⟨K, hK, h1, h2⟩

end Translate

end PolySwap.KMS.P313L
end
end Part_LinkAux3

section Part_Link

open Classical Polynomial

noncomputable section

namespace PolySwap.KMS.P313

open PolySwap.KMS PolySwap.KMS.P313L

/-- Every vertex of `F^I X` has a colour set in `I`. -/
theorem vertex_col (d : ℕ) (F : Type*) [Field F] [Fintype F] (f : F[X])
    (I : Finset (Finset ℕ)) (v : Finset (Σ i : Fin (d + 1),
      Matrix.SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f) ⧸ Hf d F f i))
    (hv : v ∈ (kmsFI d F f I).vertices) : v.image (kmsCol d F f) ∈ I := by
  simp only [WComplex.vertices, Finset.mem_biUnion, id] at hv
  obtain ⟨Tp, hT, hvT⟩ := hv
  simp only [kmsFI, WComplex.coloredFaces, Finset.mem_image, Finset.mem_filter] at hT
  obtain ⟨τ, ⟨-, hτ⟩, rfl⟩ := hT
  obtain ⟨J, hJ, rfl⟩ := mem_image'.1 hvT
  convert hJ using 1
  exact hτ J hJ

/-- The vertex link of `F^I X` at a vertex of colour `J` is isomorphic, as a weighted complex,
to the coset complex `Y = CC(U_{[d]\J}; …)`; hence `h¹` transfers. -/
theorem link_hone (d r T : ℕ) (hd : 2 ≤ d) (F : Type*) [Field F] [Fintype F]
    (f : F[X]) (hf : Irreducible f) (hdeg : 2 ≤ f.natDegree)
    (I : Finset (Finset ℕ)) (hI : I ∈ disjointColorSets d r T) (J : Finset ℕ) (hJ : J ∈ I)
    (v : Finset (Σ i : Fin (d + 1),
      Matrix.SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f) ⧸ Hf d F f i))
    (hv : v ∈ (kmsFI d F f I).vertices) (hvJ : v.image (kmsCol d F f) = J)
    (Λ : Type*) [Group Λ] (β : ℝ) (h : (linkY d F I J).HOneGe Λ β) :
    ((kmsFI d F f I).link {v}).HOneGe Λ β := by
  have : Fact (Irreducible f) := ⟨hf⟩
  have ht : AdjoinRoot.root f ≠ 0 := by
    intro h0
    have hdvd : f ∣ X := AdjoinRoot.mk_eq_zero.1 (by rw [AdjoinRoot.mk_X]; exact h0)
    have := Polynomial.natDegree_le_of_dvd hdvd X_ne_zero
    rw [natDegree_X] at this; omega
  have hIr : ∀ K ∈ I, K ⊆ Finset.range (d + 1) ∧ K.Nonempty := by
    intro K hK
    simp only [disjointColorSets, Finset.mem_filter, Finset.mem_powersetCard] at hI
    have := Finset.mem_powersetCard.1 (hI.1.1 hK)
    exact ⟨this.1, Finset.card_pos.1 (by omega)⟩
  have hIr' : ∀ K ∈ I, K ⊆ Finset.range (d + 1) := fun K hK => (hIr K hK).1
  have hJr := (hIr J hJ).1
  have hJne := (hIr J hJ).2
  have hbJlt : base J < d + 1 := Finset.mem_range.1 (hJr (base_mem hJne))
  let b : Fin (d + 1) := ⟨base J, hbJlt⟩
  have hbmem : (b : ℕ) ∈ J := base_mem hJne
  have hG : Finite (Matrix.SpecialLinearGroup (Fin (d + 1)) (AdjoinRoot f)) := by
    by_contra hne
    simp [kmsFI, kmsX, WComplex.coloredFaces, cosetComplex, hne, WComplex.vertices] at hv
  have : Finite (UL d F (compl d J)) := inferInstance
  have MGJ : ∀ N, (∀ j ∈ J, N ∈ Hf d F f j) ↔ ∃ y ∈ UL d F (compl d J), Φ ht b y = N :=
    fun N => MG ht b hbmem (fun c hc => Finset.mem_range.1 (hJr hc)) N
  have MGJK : ∀ K ⊆ Finset.range (d + 1), ∀ N, (∀ c ∈ J ∪ K, N ∈ Hf d F f c) ↔
      ∃ y ∈ UL d F (compl d J \ rl d J K), Φ ht b y = N := by
    intro K hK N
    have e : Finset.range (d + 1) \ (J ∪ K).image (relabel d b) = compl d J \ rl d J K := by
      rw [Finset.image_union]; ext c
      simp only [compl, rl, Finset.mem_sdiff, Finset.mem_union, b]; tauto
    rw [← e]
    exact MG ht b (Finset.mem_union_left _ hbmem) (fun c hc => Finset.mem_range.1
      ((Finset.mem_union.1 hc).elim (fun h => hJr h) (fun h => hK h))) N
  obtain ⟨g₀, hv0⟩ : ∃ g₀, v = part F f g₀ J := by
    simp only [WComplex.vertices, Finset.mem_biUnion, id] at hv
    obtain ⟨Tp, hT, hvT⟩ := hv
    obtain ⟨g, hg⟩ := (tops_FI hG hIr' Tp).1 hT
    obtain ⟨K, hK, rfl⟩ := (hg v).1 hvT
    rw [part_col (hIr' K hK)] at hvJ
    exact ⟨g, by rw [hvJ]⟩
  have hKr : ∀ K : {K // K ∈ I.erase J}, K.1 ⊆ Finset.range (d + 1) :=
    fun K => hIr' K.1 (Finset.mem_of_mem_erase K.2)
  have hΨ : ∀ (K : {K // K ∈ I.erase J}) (x : UL d F (compl d J)),
      Psi ht b I J g₀ ⟨K, (x : _ ⧸ linkH d F I J K)⟩ = part F f (g₀ * Φ ht b x) K.1 := by
    intro K x
    obtain ⟨hh, hh'⟩ := QuotientGroup.mk_out_eq_mul (linkH d F I J K) x
    unfold Psi
    simp only
    rw [hh']
    refine (part_eq_iff (hKr K)).2 fun k hk => ?_
    have hmem : ((hh : UL d F (compl d J)) : SLd d F) ∈ UL d F (compl d J \ rl d J K.1) :=
      Subgroup.mem_subgroupOf.1 hh.2
    have := (MGJK K.1 (hKr K) _).2 ⟨_, hmem, rfl⟩ k (Finset.mem_union_right _ hk)
    have e : (g₀ * Φ ht b ((x * hh : UL d F (compl d J)) : SLd d F))⁻¹ * (g₀ * Φ ht b x) =
        (Φ ht b ((hh : UL d F (compl d J)) : SLd d F))⁻¹ := by
      simp only [Subgroup.coe_mul, map_mul]; group
    rw [e]; exact inv_mem this
  have hinj : Function.Injective (Psi ht b I J g₀) := by
    rintro ⟨K, q⟩ ⟨K', q'⟩ hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective q'
    rw [hΨ, hΨ] at hq
    obtain rfl : K = K' := Subtype.ext (part_ne (hKr K) (hKr K') hq)
    have hk := (part_eq_iff (hKr K)).1 hq
    have e : (g₀ * Φ ht b x)⁻¹ * (g₀ * Φ ht b x') =
        Φ ht b ((x⁻¹ * x' : UL d F (compl d J)) : SLd d F) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]; group
    rw [e] at hk
    have hJp := (MGJ _).2 ⟨_, (x⁻¹ * x').2, rfl⟩
    obtain ⟨y, hy, hyeq⟩ := (MGJK K.1 (hKr K) _).1
      (fun c hc => (Finset.mem_union.1 hc).elim (hJp c) (hk c))
    have hyx := Φ_inj ht b hyeq
    refine Sigma.ext rfl (heq_of_eq ?_)
    apply QuotientGroup.eq.2
    rw [linkH, Subgroup.mem_subgroupOf, ← hyx]; exact hy
  -- the image of the chamber of `x` in `Y`
  have himg : ∀ (x : UL d F (compl d J)) (τ : Finset (Σ K : {K // K ∈ I.erase J},
      (UL d F (compl d J)) ⧸ linkH d F I J K)),
      (∀ p, p ∈ τ ↔ p.2 = (x : UL d F (compl d J) ⧸ linkH d F I J p.1)) →
      τ.image (Psi ht b I J g₀) = I.image (part F f (g₀ * Φ ht b x)) \ {v} := by
    intro x τ hx
    have hgJ : part F f g₀ J = part F f (g₀ * Φ ht b x) J :=
      (part_eq_iff hJr).2 (fun j hj => by
        rw [inv_mul_cancel_left]; exact (MGJ _).2 ⟨x, x.2, rfl⟩ j hj)
    ext u
    rw [mem_image', Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_image]
    constructor
    · rintro ⟨⟨K, q⟩, hp, rfl⟩
      have hq := (hx _).1 hp
      simp only at hq
      subst hq
      rw [hΨ]
      refine ⟨⟨K.1, Finset.mem_of_mem_erase K.2, rfl⟩, fun he => ?_⟩
      rw [hv0] at he
      exact Finset.ne_of_mem_erase K.2 (part_ne (hKr K) hJr he)
    · rintro ⟨⟨K, hK, rfl⟩, hne⟩
      have hKJ : K ≠ J := fun e => hne (by rw [e, hv0, hgJ])
      refine ⟨⟨⟨K, Finset.mem_erase.2 ⟨hKJ, hK⟩⟩, (x : _ ⧸ _)⟩, (hx _).2 rfl, ?_⟩
      rw [hΨ]
  have hvmem : ∀ x : UL d F (compl d J), v ∈ I.image (part F f (g₀ * Φ ht b x)) := by
    intro x
    have hgJ : part F f g₀ J = part F f (g₀ * Φ ht b x) J :=
      (part_eq_iff hJr).2 (fun j hj => by
        rw [inv_mul_cancel_left]; exact (MGJ _).2 ⟨x, x.2, rfl⟩ j hj)
    exact Finset.mem_image.2 ⟨J, hJ, by rw [← hgJ, hv0]⟩
  have htopFI : ∀ g, I.image (part F f g) ∈ (kmsFI d F f I).tops :=
    fun g => (tops_FI hG hIr' _).2 ⟨g, fun P => Finset.mem_image⟩
  have h1 : ∀ τ ∈ (linkY d F I J).tops,
      τ.image (Psi ht b I J g₀) ∈ ((kmsFI d F f I).link {v}).tops := by
    intro τ hτ
    obtain ⟨x, hx⟩ := (tops_linkY τ).1 hτ
    rw [himg x τ hx]
    exact (tops_link _ _ _).2 ⟨_, htopFI _, hvmem x, fun u => by
      simp only [Finset.mem_sdiff, Finset.mem_singleton]⟩
  have h2 : ∀ τ₁ ∈ ((kmsFI d F f I).link {v}).tops,
      ∃ τ ∈ (linkY d F I J).tops, τ.image (Psi ht b I J g₀) = τ₁ := by
    intro τ₁ hτ₁
    obtain ⟨T', hT', hvT', hτ₁m⟩ := (tops_link _ _ _).1 hτ₁
    obtain ⟨g, hg⟩ := (tops_FI hG hIr' T').1 hT'
    obtain ⟨K₀, hK₀, hK₀v⟩ := (hg v).1 hvT'
    have hK₀J : K₀ = J := part_ne (hIr' K₀ hK₀) hJr (hK₀v.trans hv0)
    rw [hK₀J] at hK₀v
    obtain ⟨y, hy, hyeq⟩ := (MGJ _).1 ((part_eq_iff hJr).1 (hv0.symm.trans hK₀v.symm))
    let x : UL d F (compl d J) := ⟨y, hy⟩
    have hx : ∀ p : Σ K : {K // K ∈ I.erase J}, (UL d F (compl d J)) ⧸ linkH d F I J K,
        p ∈ Finset.univ.image (fun K : {K // K ∈ I.erase J} =>
          (⟨K, (x : _ ⧸ linkH d F I J K)⟩ :
            Σ K : {K // K ∈ I.erase J}, (UL d F (compl d J)) ⧸ linkH d F I J K)) ↔
        p.2 = (x : UL d F (compl d J) ⧸ linkH d F I J p.1) := by
      rintro ⟨K, q⟩
      rw [Finset.mem_image]
      constructor
      · rintro ⟨K', -, h⟩; cases h; rfl
      · intro h; exact ⟨K, Finset.mem_univ _, by simp only at h; rw [h]⟩
    refine ⟨_, (tops_linkY _).2 ⟨x, hx⟩, ?_⟩
    rw [himg x _ hx]
    have hgx : g₀ * Φ ht b x = g := by
      show g₀ * Φ ht b y = g
      rw [hyeq, mul_inv_cancel_left]
    rw [hgx]
    ext u
    rw [hτ₁m, Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_image, hg]
  refine hone_transfer _ _ (Psi ht b I J g₀) β hinj (by convert h1) (by convert h2) (fun s => ?_) h
  refine gw_image _ _ _ hinj (by convert h1) (by convert h2) ((kmsX d F f).gw (part F f 1 (I.sup id)))
    (gw_part_pos hG 1 _).ne' (fun τ hτ => ?_) s
  obtain ⟨x, hx⟩ := (tops_linkY τ).1 hτ
  have key : ((kmsFI d F f I).link {v}).wt (I.image (part F f (g₀ * Φ ht b x)) \ {v}) =
      (kmsX d F f).gw (part F f 1 (I.sup id)) := by
    simp only [WComplex.link, kmsFI, WComplex.coloredFaces]
    rw [← gw_part_Lg hG (g₀ * Φ ht b x), ← sup_part]
    congr 1
    have hvm := Finset.mem_image.1 (hvmem x)
    ext u
    simp only [Finset.mem_sup, Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton,
      Finset.mem_image, id]
    constructor
    · rintro ⟨P, ⟨hP, -⟩ | rfl, hu⟩
      · exact ⟨P, hP, hu⟩
      · exact ⟨_, hvm, hu⟩
    · rintro ⟨P, hP, hu⟩
      by_cases hPv : P = v
      · exact ⟨P, Or.inr hPv, hu⟩
      · exact ⟨P, Or.inl ⟨hP, hPv⟩, hu⟩
  rw [show (linkY d F I J).wt τ = 1 from rfl, mul_one, ← key]
  congr 1
  convert himg x τ hx

end PolySwap.KMS.P313
end
end Part_Link


open Classical Polynomial
open scoped ENNReal NNReal

universe u v

namespace PolySwap.KMS.P313

open PolySwap.KMS

/-- The `Rad₁` bound of the vertex-link cone, from Lemmas 6.1, 7.2, Proposition 7.1 and
Theorem 3.19. -/
def radB (K A r : ℕ) : ℕ :=
  15 * (K * ((12 * r + 15) * (r + 1)) ^ 2 + (r + 1) * A * (12 * r + 15) + (12 * r + 15))

end PolySwap.KMS.P313

open PolySwap.KMS PolySwap.KMS.P313 in
theorem solution (r d T : ℕ) (hr : 1 ≤ r) (hd : 3 ≤ d) (hT : 4 ≤ T) :
    ∃ β₂ : ℝ, 0 < β₂ ∧ ∃ q₀ : ℕ, ∀ (F : Type u) [Field F] [Fintype F], q₀ ≤ Fintype.card F →
      ∀ (Λ : Type v) [Group Λ], (∀ g : Λ, g ^ ringChar F = 1 → g = 1) →
      ∀ f : F[X], Irreducible f → 2 ≤ f.natDegree →
      ∀ I ∈ disjointColorSets d r T, IsNice d I →
      ∀ v ∈ (kmsFI d F f I).vertices,
        ((kmsFI d F f I).link {v}).HOneGe Λ β₂ ∧ ((kmsFI d F f I).link {v}).H1Trivial Λ := by
  obtain ⟨K, hK⟩ := PolySwap.KMS.lemma_6_1
  obtain ⟨A, hA⟩ := PolySwap.KMS.lemma_7_2
  set Kc := ⌈(K : ℝ)⌉₊
  set Rb := radB Kc A r
  refine ⟨1 / (((T - 1).choose 3 : ℕ) * (Rb + 1) : ℝ), ?_, 5, ?_⟩
  · have : 0 < (T - 1).choose 3 := Nat.choose_pos (by omega)
    positivity
  intro F _ _ hq Λ _ _ f hf hdeg I hI hnice v hv
  set J := v.image (kmsCol d F f) with hJdef
  have hJ : J ∈ I := vertex_col d F f I v hv
  have hIc : I.card = T := by
    simp only [disjointColorSets, Finset.mem_filter, Finset.mem_powersetCard] at hI
    exact hI.1.2
  have h317 := lemma_3_17 d r T (by omega) hr F hq I hI J hJ
  refine ⟨?_, h317.2.2 (by omega) f hf hdeg v hv rfl Λ⟩
  refine link_hone d r T (by omega) F f hf hdeg I hI J hJ v hv rfl Λ _ ?_
  -- the cone on `Y`
  have h1c : (linkY d F I J).IsOneConnected := h317.2.1 (by omega)
  have hdiam := proposition_7_1 d r T F I hI hnice J hJ
  have hne : (linkY d F I J).diam ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top _) hdiam
  set D := (linkY d F I J).diam.toNat with hDdef
  have hD : (linkY d F I J).diam = D := (ENat.coe_toNat hne).symm
  have hD7 : D ≤ 6 * (r + 1) + 1 := by
    have := hdiam; rw [hD] at this; exact_mod_cast this
  have hcard : Fintype.card {K // K ∈ I.erase J} = T - 1 := by
    rw [Fintype.card_coe, Finset.card_erase_of_mem hJ, hIc]
  obtain ⟨C, hC, -, hC1⟩ := theorem_3_19 (G := UL d F (compl d J))
    (ι := {K // K ∈ I.erase J}) (by rw [hcard]; omega) (linkH d F I J) h1c D hD
  -- the Dehn bound
  have hbin : ∀ ℓ ≤ r, ∀ s : ℕ, (binDehn d F I J ℓ s : ℝ≥0∞) ≤ (A : ℝ≥0) * s := by
    intro ℓ hℓ s
    have := ENat.toENNReal_le.2 (hA d r T F I hI hnice J hJ ℓ hℓ s)
    refine this.trans (le_of_eq ?_)
    simp
  have hdehn := hK d r T F I hI hnice J hJ A hbin (2 * D + 1)
  have hdehn' : linkDehn d F I J (2 * D + 1) ≤
      ((Kc * ((12 * r + 15) * (r + 1)) ^ 2 + (r + 1) * A * (12 * r + 15) : ℕ) : ℕ∞) := by
    rw [← ENat.toENNReal_le]
    refine hdehn.trans ?_
    have hKc : (K : ℝ≥0∞) ≤ (Kc : ℝ≥0∞) := by
      have : (K : ℝ) ≤ Kc := Nat.le_ceil _
      exact_mod_cast (show (K : ℝ≥0) ≤ (Kc : ℝ≥0) from by exact_mod_cast this)
    have h2D : ((2 * D + 1 : ℕ) : ℝ≥0∞) ≤ ((12 * r + 15 : ℕ) : ℝ≥0∞) := by
      exact_mod_cast (by omega : 2 * D + 1 ≤ 12 * r + 15)
    rw [ENat.toENNReal_coe]
    push_cast
    push_cast at h2D
    gcongr
  have hrad : (linkY d F I J).rad1 C ≤ (Rb : ℕ∞) := by
    refine hC1.trans ?_
    have e : linkDehn d F I J (2 * D + 1) = cosetDehn (linkH d F I J) (2 * D + 1) := rfl
    rw [← e]
    simp only [Rb, radB]
    have h2D : ((2 * D + 1 : ℕ) : ℕ∞) ≤ ((12 * r + 15 : ℕ) : ℕ∞) := by
      exact_mod_cast (by omega : 2 * D + 1 ≤ 12 * r + 15)
    calc 15 * (linkDehn d F I J (2 * D + 1) + ((2 * D + 1 : ℕ) : ℕ∞))
        ≤ 15 * (((Kc * ((12 * r + 15) * (r + 1)) ^ 2 + (r + 1) * A * (12 * r + 15) : ℕ) : ℕ∞) +
            ((12 * r + 15 : ℕ) : ℕ∞)) := by gcongr
      _ = _ := by push_cast; ring
  have hcone := cone_h1 (linkH d F I J) C hC Rb hrad Λ
  rw [hcard] at hcone
  exact hcone
