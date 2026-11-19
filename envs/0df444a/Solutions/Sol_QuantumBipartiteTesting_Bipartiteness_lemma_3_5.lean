-- Prove2me | solution 1 for QuantumBipartiteTesting.Bipartiteness.lemma_3_5
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T12:09:01.112127+00:00
-- url     : https://prove2.me/submissions/2292b52a-e342-41c7-adb8-6435040b883d

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Reduction

set_option autoImplicit false
namespace QuantumBipartiteTesting.Bipartiteness
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

private lemma adj_symm {N c : ℕ} (F : Finset (ColoredEdge N c)) : Symmetric (Adj F) := by
  intro u v h
  obtain ⟨e, he, h | h⟩ := h
  · exact ⟨e, he, Or.inr h⟩
  · exact ⟨e, he, Or.inl h⟩

private lemma reach_symm {N c : ℕ} (F : Finset (ColoredEdge N c)) {u v : Fin N}
    (h : Relation.ReflTransGen (Adj F) u v) : Relation.ReflTransGen (Adj F) v u := by
  induction h with
  | refl => exact .refl
  | tail h hvw ih => exact (Relation.ReflTransGen.single (adj_symm F hvw)).trans ih

private def reachSetoid {N c : ℕ} (F : Finset (ColoredEdge N c)) : Setoid (Fin N) where
  r := Relation.ReflTransGen (Adj F)
  iseqv := ⟨fun _ => .refl, fun h => reach_symm F h, fun h h' => h.trans h'⟩

private def fullClass {N c : ℕ} (F : Finset (ColoredEdge N c)) (u : Fin N) : Finset (Fin N) :=
  univ.filter fun v => Relation.ReflTransGen (Adj F) u v

private lemma mem_fullClass {N c : ℕ} (F : Finset (ColoredEdge N c)) (u v : Fin N) :
    v ∈ fullClass F u ↔ Relation.ReflTransGen (Adj F) u v := by
  simp [fullClass]

private lemma self_fullClass {N c : ℕ} (F : Finset (ColoredEdge N c)) (u : Fin N) :
    u ∈ fullClass F u := (mem_fullClass F u u).mpr .refl

private lemma fullClass_eq_iff {N c : ℕ} (F : Finset (ColoredEdge N c)) (u v : Fin N) :
    fullClass F u = fullClass F v ↔ Relation.ReflTransGen (Adj F) u v := by
  constructor
  · intro h
    rw [← mem_fullClass F u v, h]
    exact self_fullClass F v
  · intro h
    ext w
    simp only [mem_fullClass]
    exact ⟨fun hw => (reach_symm F h).trans hw, fun hw => h.trans hw⟩

private lemma adj_incident {N c : ℕ} (F : Finset (ColoredEdge N c)) {u v : Fin N}
    (h : Adj F u v) : u ∈ Vertices F ∧ v ∈ Vertices F := by
  obtain ⟨e, he, h | h⟩ := h
  · exact ⟨by simp only [Vertices, mem_filter, mem_univ, true_and]; exact ⟨e,he,Or.inl h.1⟩,
      by simp only [Vertices, mem_filter, mem_univ, true_and]; exact ⟨e,he,Or.inr h.2⟩⟩
  · exact ⟨by simp only [Vertices, mem_filter, mem_univ, true_and]; exact ⟨e,he,Or.inr h.2⟩,
      by simp only [Vertices, mem_filter, mem_univ, true_and]; exact ⟨e,he,Or.inl h.1⟩⟩

private lemma reach_incident {N c : ℕ} (F : Finset (ColoredEdge N c)) {u v : Fin N}
    (hu : u ∈ Vertices F) (h : Relation.ReflTransGen (Adj F) u v) : v ∈ Vertices F := by
  induction h with
  | refl => exact hu
  | @tail v w h hvw ih => exact (adj_incident F hvw).2

private lemma isolated_class {N c : ℕ} (F : Finset (ColoredEdge N c)) {u : Fin N}
    (hu : u ∉ Vertices F) : fullClass F u = {u} := by
  ext v
  simp only [mem_fullClass, mem_singleton]
  constructor
  · intro h
    induction h with
    | refl => rfl
    | @tail v w h hvw ih => exact (hu (ih ▸ (adj_incident F hvw).1)).elim
  · rintro rfl
    exact .refl

private lemma component_fullClass {N c : ℕ} (F : Finset (ColoredEdge N c)) {u : Fin N}
    (hu : u ∈ Vertices F) :
    (Vertices F).filter (fun v => Relation.ReflTransGen (Adj F) u v) = fullClass F u := by
  ext v
  simp only [mem_filter, mem_fullClass]
  exact ⟨And.right, fun h => ⟨reach_incident F hu h, h⟩⟩

private lemma classes_decomposition {N c : ℕ} (F : Finset (ColoredEdge N c)) :
    univ.image (fullClass F) = Components F ∪ ((univ \ Vertices F).image singleton) := by
  ext S
  simp only [mem_image, mem_univ, true_and, mem_union]
  constructor
  · rintro ⟨u,rfl⟩
    by_cases hu : u ∈ Vertices F
    · left
      exact mem_image.mpr ⟨u,hu,component_fullClass F hu⟩
    · right
      exact ⟨u, mem_sdiff.mpr ⟨mem_univ _, hu⟩, (isolated_class F hu).symm⟩
  · rintro (h | ⟨u,hu,rfl⟩)
    · obtain ⟨u,hu,rfl⟩ := mem_image.mp h
      exact ⟨u,(component_fullClass F hu).symm⟩
    · exact ⟨u,isolated_class F (mem_sdiff.mp hu).2⟩

private lemma classes_disjoint {N c : ℕ} (F : Finset (ColoredEdge N c)) :
    Disjoint (Components F) ((univ \ Vertices F).image singleton) := by
  apply disjoint_left.mpr
  intro S hS hT
  obtain ⟨u,hu,he⟩ := mem_image.mp hS
  obtain ⟨v,hv,hvS⟩ := mem_image.mp hT
  have hv' : v ∉ Vertices F := (mem_sdiff.mp hv).2
  have huS : u ∈ S := by
    rw [← he, component_fullClass F hu]
    exact self_fullClass F u
  have : u = v := mem_singleton.mp (hvS ▸ huS)
  exact hv' (this ▸ hu)

private lemma quotient_card {N c : ℕ} (F : Finset (ColoredEdge N c)) :
    Fintype.card (Quotient (reachSetoid F)) + (Vertices F).card = N + (Components F).card := by
  classical
  let f : Quotient (reachSetoid F) → {S // S ∈ univ.image (fullClass F)} :=
    Quotient.lift (fun u => ⟨fullClass F u, mem_image.mpr ⟨u,mem_univ _,rfl⟩⟩)
      (fun u v h => Subtype.ext ((fullClass_eq_iff F u v).mpr h))
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      induction a using Quotient.inductionOn with | _ u =>
        induction b using Quotient.inductionOn with | _ v =>
          exact Quotient.sound ((fullClass_eq_iff F u v).mp (congrArg Subtype.val hab))
    · rintro ⟨S,hS⟩
      obtain ⟨u,hu,rfl⟩ := mem_image.mp hS
      exact ⟨Quotient.mk _ u, rfl⟩
  have hc := Fintype.card_congr (Equiv.ofBijective f hf)
  rw [Fintype.card_coe, classes_decomposition F, card_union_of_disjoint (classes_disjoint F),
    card_image_of_injective _ singleton_injective, card_sdiff_of_subset (subset_univ _), card_univ,
    Fintype.card_fin] at hc
  have hv : (Vertices F).card ≤ N := by simpa using (card_le_card (subset_univ (Vertices F)))
  omega

private lemma relative_edge {N c : ℕ} (F : Finset (ColoredEdge N c))
    (b : ColoredEdge N c → Bool) (x₀ x : Fin N → Bool)
    (h₀ : ∀ e ∈ F, xor (x₀ e.1) (x₀ e.2.1) = b e)
    (hx : ∀ e ∈ F, xor (x e.1) (x e.2.1) = b e) {u v : Fin N}
    (h : Adj F u v) : xor (x₀ u) (x u) = xor (x₀ v) (x v) := by
  obtain ⟨e,he,h | h⟩ := h
  · obtain ⟨rfl,rfl⟩ := h
    have h' := (h₀ e he).trans (hx e he).symm
    cases h1 : x₀ e.1 <;> cases h2 : x₀ e.2.1 <;>
      cases h3 : x e.1 <;> cases h4 : x e.2.1 <;> simp_all
  · obtain ⟨rfl,rfl⟩ := h
    have h' := (h₀ e he).trans (hx e he).symm
    cases h1 : x₀ e.1 <;> cases h2 : x₀ e.2.1 <;>
      cases h3 : x e.1 <;> cases h4 : x e.2.1 <;> simp_all

private lemma relative_reach {N c : ℕ} (F : Finset (ColoredEdge N c))
    (b : ColoredEdge N c → Bool) (x₀ x : Fin N → Bool)
    (h₀ : ∀ e ∈ F, xor (x₀ e.1) (x₀ e.2.1) = b e)
    (hx : ∀ e ∈ F, xor (x e.1) (x e.2.1) = b e) {u v : Fin N}
    (h : Relation.ReflTransGen (Adj F) u v) : xor (x₀ u) (x u) = xor (x₀ v) (x v) := by
  induction h with
  | refl => rfl
  | tail h hvw ih => exact ih.trans (relative_edge F b x₀ x h₀ hx hvw)

private def labelingEquiv {N c : ℕ} (F : Finset (ColoredEdge N c))
    (b : ColoredEdge N c → Bool) (x₀ : Fin N → Bool)
    (h₀ : ∀ e ∈ F, xor (x₀ e.1) (x₀ e.2.1) = b e) :
    {x : Fin N → Bool // ∀ e ∈ F, xor (x e.1) (x e.2.1) = b e} ≃
      (Quotient (reachSetoid F) → Bool) where
  toFun x := Quotient.lift (fun u => xor (x₀ u) (x.val u))
    (fun u v h => relative_reach F b x₀ x.val h₀ x.property h)
  invFun g := ⟨fun u => xor (x₀ u) (g (Quotient.mk _ u)), by
    intro e he
    have hq : (Quotient.mk (reachSetoid F) e.1) = Quotient.mk _ e.2.1 :=
      Quotient.sound (Relation.ReflTransGen.single ⟨e,he,Or.inl ⟨rfl,rfl⟩⟩)
    change xor (xor (x₀ e.1) (g (Quotient.mk _ e.1)))
      (xor (x₀ e.2.1) (g (Quotient.mk _ e.2.1))) = b e
    rw [hq]
    have hh := h₀ e he
    cases h1 : x₀ e.1 <;> cases h2 : x₀ e.2.1 <;>
      cases h3 : g (Quotient.mk _ e.2.1) <;> simp_all⟩
  left_inv x := by
    apply Subtype.ext
    funext u
    simp [Bool.xor_assoc]
  right_inv g := by
    funext q
    induction q using Quotient.inductionOn with | _ u =>
      simp [Bool.xor_assoc]

private lemma yes_count {N c : ℕ} (F : Finset (ColoredEdge N c))
    (b : ColoredEdge N c → Bool) (h : Balanced F b) :
    ((univ : Finset (Fin N → Bool)).filter
      (fun x => ∀ e ∈ F, xor (x e.1) (x e.2.1) = b e)).card =
      2 ^ Fintype.card (Quotient (reachSetoid F)) := by
  obtain ⟨x₀,h₀⟩ := h
  have hc := Fintype.card_congr (labelingEquiv F b x₀ h₀)
  simpa only [Fintype.card_subtype, Fintype.card_fun, Fintype.card_bool] using hc

private lemma probability_no {N c : ℕ} (F : Finset (ColoredEdge N c))
    (b : ColoredEdge N c → Bool) : SignProbNo F b = (2 : ℝ)^(-(F.card : ℤ)) := by
  have hs : ((univ : Finset ({e // e ∈ F} → Bool)).filter
      (fun s => ∀ e, s e = b e.val)) = {fun e => b e.val} := by
    ext s
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    exact funext_iff.symm
  rw [SignProbNo, hs, card_singleton, Nat.cast_one, one_div, zpow_neg, zpow_natCast]

private lemma probability_yes {N c : ℕ} (F : Finset (ColoredEdge N c))
    (b : ColoredEdge N c → Bool) :
    SignProbYes F b = (if Balanced F b then
      (2 : ℝ) ^ (-((Vertices F).card : ℤ) + (Components F).card) else 0) := by
  classical
  split_ifs with hb
  · rw [SignProbYes, yes_count F b hb]
    push_cast
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ (by norm_num)]
    congr 1
    have hc := quotient_card F
    omega
  · have hs : ((univ : Finset (Fin N → Bool)).filter
        (fun x => ∀ e ∈ F, xor (x e.1) (x e.2.1) = b e)) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hb ⟨x,(mem_filter.mp hx).2⟩
    simp only [SignProbYes, hs, card_empty, Nat.cast_zero, zero_div]

private lemma forest_balanced {N c : ℕ} (F : Finset (ColoredEdge N c))
    (b : ColoredEdge N c → Bool) (hF : Forest F) : Balanced F b := by
  classical
  let signs : (Fin N → Bool) → ({e // e ∈ F} → Bool) :=
    fun x e => xor (x e.val.1) (x e.val.2.1)
  let image := univ.image signs
  have fibers : ∀ s ∈ image, (univ.filter (fun x => signs x = s)).card =
      2 ^ Fintype.card (Quotient (reachSetoid F)) := by
    intro s hs
    obtain ⟨x₀,hx₀,heq⟩ := mem_image.mp hs
    have hf : (univ.filter (fun x => signs x = s)) =
        (univ.filter (fun x : Fin N → Bool => ∀ e ∈ F,
          xor (x e.1) (x e.2.1) = xor (x₀ e.1) (x₀ e.2.1))) := by
      ext x
      simp only [mem_filter, mem_univ, true_and]
      rw [← heq]
      constructor
      · intro hx e he
        exact congrFun hx ⟨e,he⟩
      · intro hx
        funext e
        exact hx e.val e.property
    rw [hf]
    exact yes_count F (fun e => xor (x₀ e.1) (x₀ e.2.1)) ⟨x₀, fun _ _ => rfl⟩
  have count : 2 ^ N = image.card * 2 ^ Fintype.card (Quotient (reachSetoid F)) := by
    have hc := card_eq_sum_card_image signs (univ : Finset (Fin N → Bool))
    calc
      _ = (univ : Finset (Fin N → Bool)).card := by simp
      _ = ∑ s ∈ image, (univ.filter (fun x => signs x = s)).card := hc
      _ = ∑ s ∈ image, 2 ^ Fintype.card (Quotient (reachSetoid F)) :=
        sum_congr rfl fibers
      _ = _ := by simp
  have hc := quotient_card F
  have rank : (F.card : ℤ) - (Vertices F).card + (Components F).card = 0 := hF
  have he : F.card + Fintype.card (Quotient (reachSetoid F)) = N := by omega
  have image_card : image.card = 2 ^ F.card := by
    have hp : 2 ^ F.card * 2 ^ Fintype.card (Quotient (reachSetoid F)) = 2 ^ N := by
      rw [← pow_add]
      exact congrArg (fun n : ℕ => 2^n) he
    exact (mul_right_cancel₀ (by positivity) (hp.trans count)).symm
  have image_all : image = univ := by
    apply eq_of_subset_of_card_le (subset_univ _)
    simp only [card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
    exact image_card.ge
  have hs : (fun e : {e // e ∈ F} => b e.val) ∈ image := by rw [image_all]; exact mem_univ _
  obtain ⟨x,hx,hxb⟩ := mem_image.mp hs
  refine ⟨x, fun e he => ?_⟩
  exact congrFun hxb ⟨e,he⟩

end
end QuantumBipartiteTesting.Bipartiteness

open QuantumBipartiteTesting.Bipartiteness
attribute [local instance] Classical.propDecidable

theorem solution {N colors : ℕ} (F : Finset (ColoredEdge N colors)) (hF : Consistent F)
    (b : ColoredEdge N colors → Bool) :
    SignProbNo F b = (2 : ℝ) ^ (-(F.card : ℤ)) ∧
    SignProbYes F b = (if Balanced F b then
      (2 : ℝ) ^ (-((Vertices F).card : ℤ) + (Components F).card) else 0) ∧
    (Forest F → SignProbYes F b = SignProbNo F b) := by
  refine ⟨probability_no F b, probability_yes F b, ?_⟩
  intro hf
  rw [probability_no F b, probability_yes F b, if_pos (forest_balanced F b hf)]
  congr 1
  have hr : (F.card : ℤ) - (Vertices F).card + (Components F).card = 0 := hf
  omega
