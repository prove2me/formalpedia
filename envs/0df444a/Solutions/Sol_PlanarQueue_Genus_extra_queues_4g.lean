-- Prove2me | solution 1 for PlanarQueue.Genus.extra_queues_4g
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T04:38:58.700211+00:00
-- url     : https://prove2.me/submissions/278243bf-1f78-4f7b-a512-505926cf170f

import Mathlib
import Definitions.Def_PlanarQueue_Genus_Setting

set_option autoImplicit false

namespace ExtraQueues4gAux

open PlanarQueue.Planar

/-- Two nested edges cannot share a vertex. -/
lemma not_nested_of_common {V : Type} (ord : V → ℕ) (e f : Sym2 V) (x : V)
    (hxe : x ∈ e) (hxf : x ∈ f) : ¬ Nested ord e f := by
  rintro ⟨a, b, c, d, h, hab, hbc, hcd⟩
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [Sym2.mem_iff] at hxe hxf
    rcases hxe with rfl | rfl <;> rcases hxf with rfl | rfl <;> omega
  · rw [Sym2.mem_iff] at hxe hxf
    rcases hxe with rfl | rfl <;> rcases hxf with rfl | rfl <;> omega

/-- In a layer-monotone order, all four endpoints of two nested edges lie in two consecutive
layers. -/
lemma nested_two_layers {V : Type} (G : SimpleGraph V) (L : V → ℕ) (hL : IsLayering G L)
    (ord : V → ℕ) (hord : ∀ v w, ord v < ord w → L v ≤ L w) (e f : Sym2 V)
    (he : e ∈ G.edgeSet) (hf : f ∈ G.edgeSet) (h : Nested ord e f) :
    ∃ m : ℕ, ∀ x, (x ∈ e ∨ x ∈ f) → (L x = m ∨ L x = m + 1) := by
  obtain ⟨a, b, c, d, hc, hab, hbc, hcd⟩ := h
  have h1 := hord _ _ hab
  have h2 := hord _ _ hbc
  have h3 := hord _ _ hcd
  refine ⟨L a, ?_⟩
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have had : G.Adj a d := he
    have := (hL a d had).2
    intro x hx
    rcases hx with hx | hx <;> rw [Sym2.mem_iff] at hx <;> rcases hx with rfl | rfl <;> omega
  · have had : G.Adj a d := hf
    have := (hL a d had).2
    intro x hx
    rcases hx with hx | hx <;> rw [Sym2.mem_iff] at hx <;> rcases hx with rfl | rfl <;> omega

/-- An edge of `G` avoiding `Z` lifts to an edge of `G - Z`. -/
lemma exists_lift {V : Type} (G : SimpleGraph V) (Z : Finset V) (s : Sym2 V)
    (hs : s ∈ G.edgeSet) (hZ : ∀ x ∈ s, x ∉ Z) :
    ∃ s' : (G.induce (↑Z : Set V)ᶜ).edgeSet, Sym2.map Subtype.val s'.1 = s := by
  induction s using Sym2.ind with
  | h a b =>
    have ha : a ∈ (↑Z : Set V)ᶜ := by
      simpa using hZ a (Sym2.mem_mk_left a b)
    have hb : b ∈ (↑Z : Set V)ᶜ := by
      simpa using hZ b (Sym2.mem_mk_right a b)
    refine ⟨⟨s(⟨a, ha⟩, ⟨b, hb⟩), ?_⟩, ?_⟩
    · show (G.induce (↑Z : Set V)ᶜ).Adj ⟨a, ha⟩ ⟨b, hb⟩
      simpa using hs
    · simp

end ExtraQueues4gAux

theorem solution (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (L : V → ℕ) (hL : PlanarQueue.Planar.IsLayering G L) (g : ℕ) (Z : Finset V)
    (hZ : ∀ j : ℕ, (Z.filter (fun v => L v = j)).card ≤ 2 * g)
    (ord₀ : ↥((↑Z : Set V)ᶜ) → ℕ) (h₀ : PlanarQueue.Planar.OrderAdmits (G.induce (↑Z : Set V)ᶜ) 49 ord₀)
    (hmono : ∀ a b : ↥((↑Z : Set V)ᶜ), L a < L b → ord₀ a < ord₀ b) :
    PlanarQueue.Planar.HasQueueLayout G (4 * g + 49) := by
  classical
  obtain ⟨q₀, hinj₀, hq₀⟩ := h₀
  set e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V with he_def
  set M : ℕ := (Finset.univ.sup ord₀) + Fintype.card V + 1 with hM
  have hMo : ∀ x, ord₀ x < M := fun x => by
    have := Finset.le_sup (f := ord₀) (Finset.mem_univ x); omega
  have hMe : ∀ v, (e v : ℕ) < M := fun v => by
    have := (e v).isLt; omega
  have hmemc : ∀ v, v ∉ Z → v ∈ (↑Z : Set V)ᶜ := fun v h => by simpa using h
  -- the inner position and the parity bit
  let inner : V → ℕ := fun v => if h : v ∈ Z then (e v : ℕ) else ord₀ ⟨v, hmemc v h⟩
  let par : V → ℕ := fun v => if v ∈ Z then 0 else 1
  let ord : V → ℕ := fun v => 2 * (L v * M + inner v) + par v
  have hinner : ∀ v, inner v < M := fun v => by
    by_cases h : v ∈ Z
    · simp only [inner, dif_pos h]; exact hMe v
    · simp only [inner, dif_neg h]; exact hMo _
  have hpar : ∀ v, par v ≤ 1 := fun v => by
    by_cases h : v ∈ Z <;> simp [par, h]
  have hlayer : ∀ v w, L v < L w → ord v < ord w := fun v w hvw => by
    have h1 : (L v + 1) * M ≤ L w * M := Nat.mul_le_mul_right _ hvw
    have h2 := hinner v
    have h3 := hinner w
    have h4 := hpar v
    simp only [ord]
    nlinarith
  have hord : ∀ v w, ord v < ord w → L v ≤ L w := fun v w h => by
    by_contra hc
    have := hlayer w v (by omega)
    omega
  have hinj : Function.Injective ord := by
    intro v w hvw
    have hL' : L v = L w := by
      rcases lt_trichotomy (L v) (L w) with h | h | h
      · have := hlayer v w h; omega
      · exact h
      · have := hlayer w v h; omega
    by_cases hv : v ∈ Z <;> by_cases hw : w ∈ Z
    · simp only [ord, inner, par, dif_pos hv, dif_pos hw, if_pos hv, if_pos hw, hL'] at hvw
      have : (e v : ℕ) = e w := by omega
      exact e.injective (Fin.ext this)
    · simp only [ord, inner, par, dif_pos hv, dif_neg hw, if_pos hv, if_neg hw, hL'] at hvw
      omega
    · simp only [ord, inner, par, dif_neg hv, dif_pos hw, if_neg hv, if_pos hw, hL'] at hvw
      omega
    · simp only [ord, inner, par, dif_neg hv, dif_neg hw, if_neg hv, if_neg hw, hL'] at hvw
      have : ord₀ ⟨v, hmemc v hv⟩ = ord₀ ⟨w, hmemc w hw⟩ := by omega
      have := hinj₀ this
      simpa using congrArg Subtype.val this
  -- on vertices outside `Z`, the new order agrees with `ord₀`
  have hcompat : ∀ a b : ↥((↑Z : Set V)ᶜ), ord a < ord b → ord₀ a < ord₀ b := by
    intro a b hab
    have ha : (a : V) ∉ Z := fun h => a.2 (Finset.mem_coe.2 h)
    have hb : (b : V) ∉ Z := fun h => b.2 (Finset.mem_coe.2 h)
    rcases lt_trichotomy (L a) (L b) with h | h | h
    · exact hmono a b h
    · simp only [ord, inner, par, dif_neg ha, dif_neg hb, if_neg ha, if_neg hb, h] at hab
      have : ord₀ ⟨a, hmemc a ha⟩ < ord₀ ⟨b, hmemc b hb⟩ := by omega
      simpa using this
    · have := hlayer b a h; omega
  -- the index of a vertex of `Z` inside its layer
  let idx : V → ℕ := fun z => (Z.filter (fun w => L w = L z ∧ e w < e z)).card
  have hidx : ∀ z ∈ Z, idx z < 2 * g := by
    intro z hz
    have hss : Z.filter (fun w => L w = L z ∧ e w < e z) ⊂ Z.filter (fun w => L w = L z) := by
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨z, by simp [hz], by simp⟩
      · intro w hw
        simp only [Finset.mem_filter] at hw ⊢
        exact ⟨hw.1, hw.2.1⟩
    have := Finset.card_lt_card hss
    have := hZ (L z)
    simp only [idx]
    omega
  have hidx_lt : ∀ z z', z ∈ Z → z' ∈ Z → L z = L z' → e z < e z' → idx z < idx z' := by
    intro z z' hz hz' hl hlt
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨z, by simp [hz, hl, hlt], by simp⟩
    · intro w hw
      simp only [Finset.mem_filter] at hw ⊢
      exact ⟨hw.1, hw.2.1.trans hl, hw.2.2.trans hlt⟩
  have hidx_inj : ∀ z z', z ∈ Z → z' ∈ Z → L z = L z' → idx z = idx z' → z = z' := by
    intro z z' hz hz' hl hi
    rcases lt_trichotomy (e z) (e z') with h | h | h
    · have := hidx_lt z z' hz hz' hl h; omega
    · exact e.injective h
    · have := hidx_lt z' z hz' hz hl.symm h; omega
  -- the queue assignment
  have hex : ∀ s : G.edgeSet, ∃ k : Fin (4 * g + 49),
      (∃ z ∈ Z, z ∈ (s : Sym2 V) ∧ (k : ℕ) = 2 * idx z + L z % 2) ∨
      (∃ s' : (G.induce (↑Z : Set V)ᶜ).edgeSet, Sym2.map Subtype.val s'.1 = s ∧
        (k : ℕ) = 4 * g + q₀ s') := by
    intro s
    by_cases h : ∃ z ∈ Z, z ∈ (s : Sym2 V)
    · obtain ⟨z, hz, hzs⟩ := h
      have := hidx z hz
      have : L z % 2 < 2 := Nat.mod_lt _ (by norm_num)
      exact ⟨⟨2 * idx z + L z % 2, by omega⟩, Or.inl ⟨z, hz, hzs, rfl⟩⟩
    · simp only [not_exists, not_and] at h
      obtain ⟨s', hs'⟩ := ExtraQueues4gAux.exists_lift G Z s s.2 (fun x hx hxZ => h x hxZ hx)
      have := (q₀ s').isLt
      exact ⟨⟨4 * g + q₀ s', by omega⟩, Or.inr ⟨s', hs', rfl⟩⟩
  choose q hq using hex
  refine ⟨ord, q, hinj, ?_⟩
  intro s t hst hnest
  rcases hq s with ⟨z, hz, hzs, hks⟩ | ⟨s', hs', hks⟩ <;>
    rcases hq t with ⟨z', hz', hzt, hkt⟩ | ⟨t', ht', hkt⟩
  · -- both edges are charged to vertices of `Z`
    rw [hst] at hks
    have hi1 := hidx z hz
    have hi2 := hidx z' hz'
    have hpm : L z % 2 = L z' % 2 := by omega
    have hii : idx z = idx z' := by omega
    by_cases hl : L z = L z'
    · have := hidx_inj z z' hz hz' hl hii
      subst this
      exact ExtraQueues4gAux.not_nested_of_common ord s t z hzs hzt hnest
    · obtain ⟨m, hm⟩ := ExtraQueues4gAux.nested_two_layers G L hL ord hord s t s.2 t.2 hnest
      have h1 := hm z (Or.inl hzs)
      have h2 := hm z' (Or.inr hzt)
      omega
  · rw [hst] at hks
    have := hidx z hz
    have : L z % 2 < 2 := Nat.mod_lt _ (by norm_num)
    omega
  · rw [hst] at hks
    have := hidx z' hz'
    have : L z' % 2 < 2 := Nat.mod_lt _ (by norm_num)
    omega
  · -- both edges come from `G - Z`
    rw [hst] at hks
    have hqq : q₀ s' = q₀ t' := Fin.ext (by omega)
    apply hq₀ s' t' hqq
    obtain ⟨a, b, c, d, hc, hab, hbc, hcd⟩ := hnest
    have hval : Function.Injective (Sym2.map (Subtype.val : ↥((↑Z : Set V)ᶜ) → V)) :=
      Sym2.map.injective Subtype.val_injective
    have key : ∀ (u : (G.induce (↑Z : Set V)ᶜ).edgeSet) (x y : V) (hx : x ∈ (↑Z : Set V)ᶜ)
        (hy : y ∈ (↑Z : Set V)ᶜ), Sym2.map Subtype.val (u : Sym2 ↥((↑Z : Set V)ᶜ)) = s(x, y) →
        (u : Sym2 ↥((↑Z : Set V)ᶜ)) = s(⟨x, hx⟩, ⟨y, hy⟩) := by
      intro u x y hx hy hu
      apply hval
      rw [hu]
      simp
    have memc : ∀ (u : (G.induce (↑Z : Set V)ᶜ).edgeSet) (x : V),
        x ∈ Sym2.map Subtype.val (u : Sym2 ↥((↑Z : Set V)ᶜ)) → x ∈ (↑Z : Set V)ᶜ := by
      intro u x hx
      rw [Sym2.mem_map] at hx
      obtain ⟨y, -, rfl⟩ := hx
      exact y.2
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← hs'] at h1
      rw [← ht'] at h2
      have ha := memc s' a (by rw [h1]; exact Sym2.mem_mk_left _ _)
      have hd := memc s' d (by rw [h1]; exact Sym2.mem_mk_right _ _)
      have hb := memc t' b (by rw [h2]; exact Sym2.mem_mk_left _ _)
      have hc' := memc t' c (by rw [h2]; exact Sym2.mem_mk_right _ _)
      refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc'⟩, ⟨d, hd⟩,
        Or.inl ⟨key s' a d ha hd h1, key t' b c hb hc' h2⟩,
        hcompat _ _ hab, hcompat _ _ hbc, hcompat _ _ hcd⟩
    · rw [← hs'] at h1
      rw [← ht'] at h2
      have hb := memc s' b (by rw [h1]; exact Sym2.mem_mk_left _ _)
      have hc' := memc s' c (by rw [h1]; exact Sym2.mem_mk_right _ _)
      have ha := memc t' a (by rw [h2]; exact Sym2.mem_mk_left _ _)
      have hd := memc t' d (by rw [h2]; exact Sym2.mem_mk_right _ _)
      refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc'⟩, ⟨d, hd⟩,
        Or.inr ⟨key s' b c hb hc' h1, key t' a d ha hd h2⟩,
        hcompat _ _ hab, hcompat _ _ hbc, hcompat _ _ hcd⟩
