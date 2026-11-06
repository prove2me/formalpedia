-- Prove2me | solution 1 for TuranMatching.Clique.barrier
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T23:31:23.268837+00:00
-- url     : https://prove2.me/submissions/b7cf4dec-733c-487c-b452-33620eca5e3d

import Mathlib
import Definitions.Def_TuranMatching_Clique_Setting

open Finset SimpleGraph

namespace TBAux

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma two_mul_ncard_edgeSet {M : G.Subgraph} (h : M.IsMatching) :
    2 * M.edgeSet.ncard = M.verts.ncard := by
  classical
  have h1 : M.edgeSet.ncard = M.coe.edgeSet.ncard := by
    rw [← Subgraph.image_coe_edgeSet_coe M]
    exact (Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective))
  have h2 := (Subgraph.isMatching_iff_forall_degree.mp h)
  have h3 := M.coe.sum_degrees_eq_twice_card_edges
  rw [h1, Set.ncard_eq_toFinset_card' , ← SimpleGraph.edgeFinset]
  simp only [Subgraph.coe_degree] at h3
  have h4 : ∀ v : M.verts, M.degree v = 1 := fun v => by convert h2 v v.2
  simp only [h4, Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ] at h3
  rw [← h3, Set.ncard_eq_toFinset_card' M.verts]
  simp [Set.toFinset_card]

/-- the support in `V` of a component of `G - S` -/
def cset (G : SimpleGraph V) (S : Set V) (c : (G.induce S).ConnectedComponent) : Set V :=
  Subtype.val '' c.supp

lemma mem_cset {S : Set V} {c : (G.induce S).ConnectedComponent} {z : V} :
    z ∈ cset G S c ↔ ∃ h : z ∈ S, (G.induce S).connectedComponentMk ⟨z, h⟩ = c := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, (ConnectedComponent.mem_supp_iff _ _).1 hx⟩
  · rintro ⟨h, hc⟩
    exact ⟨⟨z, h⟩, (ConnectedComponent.mem_supp_iff _ _).2 hc, rfl⟩

lemma eq_of_mem_cset {S : Set V} {c c' : (G.induce S).ConnectedComponent} {z : V}
    (hc : z ∈ cset G S c) (hc' : z ∈ cset G S c') : c = c' := by
  obtain ⟨h, h1⟩ := mem_cset.1 hc
  obtain ⟨h', h2⟩ := mem_cset.1 hc'
  exact h1.symm.trans h2

lemma ncard_cset {S : Set V} (c : (G.induce S).ConnectedComponent) :
    (cset G S c).ncard = c.supp.ncard :=
  Set.ncard_image_of_injective _ Subtype.val_injective

lemma cset_injective (S : Set V) : Function.Injective (cset G S) := by
  intro c c' h
  obtain ⟨x, hx⟩ := c.nonempty_supp
  have h1 : x.val ∈ cset G S c := ⟨x, hx, rfl⟩
  rw [h] at h1
  exact eq_of_mem_cset ⟨x, hx, rfl⟩ h1

lemma mem_cset_of_adj {S : Set V} {c : (G.induce S).ConnectedComponent} {z w : V}
    (hz : z ∈ cset G S c) (hzw : G.Adj z w) (hw : w ∈ S) : w ∈ cset G S c := by
  obtain ⟨hzS, hc⟩ := mem_cset.1 hz
  refine mem_cset.2 ⟨hw, ?_⟩
  rw [← hc]
  exact (ConnectedComponent.connectedComponentMk_eq_of_adj
    (show (G.induce S).Adj ⟨z, hzS⟩ ⟨w, hw⟩ from hzw)).symm

lemma sum_half_add_odd {W : Type*} [Finite W] (H : SimpleGraph W) :
    2 * ∑ᶠ c : H.ConnectedComponent, c.supp.ncard / 2 + H.oddComponents.ncard
      = Nat.card W := by
  classical
  have := Fintype.ofFinite W
  have : Fintype H.ConnectedComponent := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card]
  have h1 : ∑ c : H.ConnectedComponent, c.supp.ncard = Fintype.card W := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise
      (f := H.connectedComponentMk) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Set.ncard_coe_finset]
    congr 1
    ext a
    simp [ConnectedComponent.mem_supp_iff]
  have h2 : H.oddComponents.ncard = ∑ c : H.ConnectedComponent, c.supp.ncard % 2 := by
    have : H.oddComponents = ↑(Finset.univ.filter fun c : H.ConnectedComponent => Odd c.supp.ncard) := by
      ext c; simp
    rw [this, Set.ncard_coe_finset, Finset.card_filter]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases h : Odd c.supp.ncard
    · rw [if_pos h]; exact (Nat.odd_iff.1 h).symm
    · rw [if_neg h]; have := Nat.odd_iff.not.1 h; omega
  rw [h2, ← h1, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  omega

lemma val_id (B : Finset V) :
    2 * (#B + ∑ᶠ c : (G.induce ((B : Set V)ᶜ)).ConnectedComponent, c.supp.ncard / 2)
      + (G.induce ((B : Set V)ᶜ)).oddComponents.ncard = Fintype.card V + #B := by
  have h := sum_half_add_odd (G.induce ((B : Set V)ᶜ))
  have h2 := Set.ncard_add_ncard_compl (B : Set V)
  rw [Nat.card_coe_set_eq] at h
  rw [Set.ncard_coe_finset, Nat.card_eq_fintype_card] at h2
  omega

/-- `|B| + Σ_c ⌊|c|/2⌋` over the components of `G - B` -/
noncomputable def val (G : SimpleGraph V) (B : Finset V) : ℕ :=
  #B + ∑ᶠ c : (G.induce ((B : Set V)ᶜ)).ConnectedComponent, c.supp.ncard / 2

/-- number of odd components of `G - B` -/
noncomputable def oddCnt (G : SimpleGraph V) (B : Finset V) : ℕ :=
  (G.induce ((B : Set V)ᶜ)).oddComponents.ncard

lemma val_id' (B : Finset V) : 2 * val G B + oddCnt G B = Fintype.card V + #B := by
  unfold val oddCnt
  exact val_id B

lemma even_of_closed {M : G.Subgraph} (hM : M.IsMatching) (S : Set V)
    (hS : ∀ x ∈ S, x ∈ M.verts ∧ ∀ y, M.Adj x y → y ∈ S) : Even S.ncard := by
  classical
  have hM' : (M.induce S).IsMatching := by
    intro v hv
    have hvS : v ∈ S := hv
    obtain ⟨w, hw, huniq⟩ := hM (hS v hvS).1
    refine ⟨w, ⟨hvS, (hS v hvS).2 w hw, hw⟩, ?_⟩
    intro y hy
    exact huniq y hy.2.2
  have : Fintype (M.induce S).verts := Fintype.ofFinite _
  have h := hM'.even_card
  have e : S.ncard = (M.induce S).verts.toFinset.card :=
    Set.ncard_eq_toFinset_card' (M.induce S).verts
  rw [e]
  exact h

lemma odd_add_verts_le {M : G.Subgraph} (hM : M.IsMatching) (B : Finset V) :
    (G.induce ((B : Set V)ᶜ)).oddComponents.ncard + M.verts.ncard ≤ Fintype.card V + #B := by
  classical
  have hex : ∀ c : ↥((G.induce ((B : Set V)ᶜ)).oddComponents), ∃ x : V,
      (x ∈ cset G _ c.1 ∧ x ∉ M.verts) ∨ (x ∈ B ∧ ∃ v ∈ cset G _ c.1, M.Adj v x) := by
    rintro ⟨c, hc⟩
    by_contra hcon
    have h1 : ∀ x, x ∈ cset G _ c → x ∈ M.verts := fun x hx => by
      by_contra hx'; exact hcon ⟨x, Or.inl ⟨hx, hx'⟩⟩
    have h2 : ∀ x ∈ B, ∀ v ∈ cset G _ c, ¬ M.Adj v x := fun x hx v hv hadj =>
      hcon ⟨x, Or.inr ⟨hx, v, hv, hadj⟩⟩
    have := even_of_closed hM (cset G _ c) (fun x hx => ⟨h1 x hx, fun y hy => ?_⟩)
    · rw [ncard_cset] at this
      exact (Nat.not_even_iff_odd.2 hc) this
    · refine mem_cset_of_adj hx (M.adj_sub hy) ?_
      intro hyB
      exact h2 y (Finset.mem_coe.1 hyB) x hx hy
  choose φ hφ using hex
  have hmaps : ∀ c, φ c ∈ (M.vertsᶜ ∪ (B : Set V)) := by
    intro c
    rcases hφ c with ⟨_, h⟩ | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr (Finset.mem_coe.2 h)
  have hinj : Function.Injective φ := by
    intro c c' hcc
    have h1 := hφ c
    have h2 := hφ c'
    rw [hcc] at h1
    apply Subtype.ext
    rcases h1 with ⟨a1, _⟩ | ⟨b1, v, hv, hadj⟩ <;> rcases h2 with ⟨a2, _⟩ | ⟨b2, v', hv', hadj'⟩
    · exact eq_of_mem_cset a1 a2
    · exact absurd (Finset.mem_coe.2 b2) (mem_cset.1 a1).1
    · exact absurd (Finset.mem_coe.2 b1) (mem_cset.1 a2).1
    · have := hM.eq_of_adj_right hadj hadj'
      subst this
      exact eq_of_mem_cset hv hv'
  have hle : Nat.card ↥((G.induce ((B : Set V)ᶜ)).oddComponents) ≤
      Nat.card ↥(M.vertsᶜ ∪ (B : Set V)) :=
    Nat.card_le_card_of_injective (fun c => ⟨φ c, hmaps c⟩) (fun c c' h => hinj (by simpa using h))
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq] at hle
  have h3 := Set.ncard_union_le M.vertsᶜ (B : Set V)
  have h4 := Set.ncard_add_ncard_compl M.verts
  rw [Set.ncard_coe_finset] at h3
  rw [Nat.card_eq_fintype_card] at h4
  omega

lemma matching_ncard_le_val {M : G.Subgraph} (hM : M.IsMatching) (B : Finset V) :
    M.edgeSet.ncard ≤ #B + ∑ᶠ c : (G.induce ((B : Set V)ᶜ)).ConnectedComponent,
      c.supp.ncard / 2 := by
  have h1 := val_id (G := G) B
  have h2 := odd_add_verts_le hM B
  have h3 := two_mul_ncard_edgeSet hM
  omega

/-- `G` with `d` universal vertices added -/
def aug (G : SimpleGraph V) (d : ℕ) : SimpleGraph (V ⊕ Fin d) where
  Adj x y := x ≠ y ∧ ∀ a b, x = Sum.inl a → y = Sum.inl b → G.Adj a b
  symm := ⟨fun x y ⟨h1, h2⟩ => ⟨h1.symm, fun a b hx hy => (h2 b a hy hx).symm⟩⟩
  loopless := ⟨fun x h => h.1 rfl⟩

lemma aug_adj_inl {d : ℕ} {a b : V} : (aug G d).Adj (Sum.inl a) (Sum.inl b) ↔ G.Adj a b := by
  constructor
  · rintro ⟨-, h2⟩
    exact h2 a b rfl rfl
  · intro hab
    refine ⟨fun h => hab.ne (Sum.inl.inj h), fun a' b' ha hb => ?_⟩
    rw [Sum.inl.injEq] at ha hb
    subst ha hb
    exact hab

lemma ncard_odd_iso {W₁ W₂ : Type*} {H₁ : SimpleGraph W₁} {H₂ : SimpleGraph W₂}
    (φ : H₁ ≃g H₂) : H₁.oddComponents.ncard = H₂.oddComponents.ncard := by
  have hsupp : ∀ c : H₁.ConnectedComponent,
      (φ.connectedComponentEquiv c).supp.ncard = c.supp.ncard := by
    intro c
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact (Nat.card_congr (ConnectedComponent.isoEquivSupp φ c)).symm
  have : H₂.oddComponents = φ.connectedComponentEquiv '' H₁.oddComponents := by
    ext c'
    constructor
    · intro h
      refine ⟨φ.connectedComponentEquiv.symm c', ?_, by simp⟩
      show Odd _
      rw [← hsupp, Equiv.apply_symm_apply]
      exact h
    · rintro ⟨c, hc, rfl⟩
      show Odd _
      rw [hsupp]
      exact hc
  rw [this, Set.ncard_image_of_injective _ φ.connectedComponentEquiv.injective]

lemma oc_deleteVerts {W : Type*} [Finite W] (H : SimpleGraph W) (u : Set W) :
    ((⊤ : H.Subgraph).deleteVerts u).coe.oddComponents.ncard
      = (H.induce uᶜ).oddComponents.ncard := by
  have hv : ((⊤ : H.Subgraph).deleteVerts u).verts = uᶜ := by
    ext x
    simp
  refine ncard_odd_iso
    { toEquiv := Equiv.setCongr hv
      map_rel_iff' := ?_ }
  intro a b
  have ha : (a : W) ∉ u := by simpa using a.2
  have hb : (b : W) ∉ u := by simpa using b.2
  simp [ha, hb]

lemma not_violator_aug (d : ℕ) (hd : Even (Fintype.card V + d))
    (h : ∀ B : Finset V, (G.induce ((B : Set V)ᶜ)).oddComponents.ncard ≤ #B + d)
    (u : Set (V ⊕ Fin d)) : ¬ (aug G d).IsTutteViolator u := by
  classical
  unfold SimpleGraph.IsTutteViolator
  rw [oc_deleteVerts]
  intro hlt
  by_cases hu : ∀ j : Fin d, Sum.inr j ∈ u
  · let B : Finset V := Finset.univ.filter (fun a => Sum.inl a ∈ u)
    have hB : ∀ a, a ∈ B ↔ Sum.inl a ∈ u := by intro a; simp [B]
    let f : ↥((B : Set V)ᶜ) → ↥uᶜ := fun a => ⟨Sum.inl a.1, fun h => a.2 ((hB a.1).2 h)⟩
    have hf : Function.Bijective f := by
      constructor
      · intro a b hab
        exact Subtype.ext (Sum.inl.inj (congrArg Subtype.val hab))
      · rintro ⟨x, hx⟩
        cases x with
        | inl a => exact ⟨⟨a, fun h => hx ((hB a).1 h)⟩, rfl⟩
        | inr j => exact absurd (hu j) hx
    let e : G.induce ((B : Set V)ᶜ) ≃g (aug G d).induce uᶜ :=
      { toEquiv := Equiv.ofBijective f hf
        map_rel_iff' := by
          intro a b
          show (aug G d).Adj (Sum.inl a.1) (Sum.inl b.1) ↔ G.Adj a.1 b.1
          exact aug_adj_inl }
    have hcard : u.ncard = #B + d := by
      have : u = ↑(B.disjSum (Finset.univ : Finset (Fin d))) := by
        ext x
        cases x with
        | inl a => simp [hB a]
        | inr j => simp [hu j]
      rw [this, Set.ncard_coe_finset, Finset.card_disjSum, Finset.card_univ, Fintype.card_fin]
    rw [← ncard_odd_iso e, hcard] at hlt
    have := h B
    omega
  · push Not at hu
    obtain ⟨j, hj⟩ := hu
    have hall : ∀ x y : ↥uᶜ, ((aug G d).induce uᶜ).Reachable x y := by
      have hx : ∀ x : ↥uᶜ, ((aug G d).induce uᶜ).Reachable x ⟨Sum.inr j, hj⟩ := by
        intro x
        by_cases hxz : x = ⟨Sum.inr j, hj⟩
        · rw [hxz]
        · apply Adj.reachable
          show (aug G d).Adj x.val (Sum.inr j)
          exact ⟨fun h => hxz (Subtype.ext h), by intro a b _ hb; cases hb⟩
      exact fun x y => (hx x).trans (hx y).symm
    have hsub : Subsingleton ((aug G d).induce uᶜ).ConnectedComponent := ⟨fun a b => by
      induction a using ConnectedComponent.ind
      induction b using ConnectedComponent.ind
      exact ConnectedComponent.eq.2 (hall _ _)⟩
    have hle : ((aug G d).induce uᶜ).oddComponents.ncard ≤ 1 :=
      (Set.ncard_le_one (Set.toFinite _)).2 (fun a _ b _ => Subsingleton.elim a b)
    have h0 : u.ncard = 0 := by omega
    have h1 : ((aug G d).induce uᶜ).oddComponents.ncard = 1 := by omega
    have hu0 : u = ∅ := (Set.ncard_eq_zero (Set.toFinite u)).1 h0
    have hodd : Odd (((aug G d).induce uᶜ).oddComponents.ncard) := by rw [h1]; exact odd_one
    have := (odd_ncard_oddComponents _).1 hodd
    subst hu0
    simp only [Set.compl_empty, Nat.card_univ] at this
    rw [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_fin] at this
    exact (Nat.not_even_iff_odd.2 this) hd

lemma exists_matching_of_def (d : ℕ) (hd : Even (Fintype.card V + d))
    (h : ∀ B : Finset V, (G.induce ((B : Set V)ᶜ)).oddComponents.ncard ≤ #B + d) :
    ∃ M : G.Subgraph, M.IsMatching ∧ Fintype.card V ≤ M.verts.ncard + d := by
  classical
  obtain ⟨M', hM'⟩ := (SimpleGraph.tutte (G := aug G d)).2 (fun u => not_violator_aug d hd h u)
  let M : G.Subgraph :=
    { verts := {a | ∃ b, M'.Adj (Sum.inl a) (Sum.inl b)}
      Adj := fun a b => M'.Adj (Sum.inl a) (Sum.inl b)
      adj_sub := fun {a b} hab => aug_adj_inl.1 (M'.adj_sub hab)
      edge_vert := fun {a b} hab => ⟨b, hab⟩
      symm := ⟨fun a b hab => hab.symm⟩ }
  have hM : M.IsMatching := by
    intro a ha
    obtain ⟨b, hb⟩ := ha
    refine ⟨b, hb, fun b' hb' => ?_⟩
    have := hM'.1 (hM'.2 (Sum.inl a))
    exact Sum.inl.inj (this.unique hb' hb)
  refine ⟨M, hM, ?_⟩
  have hex : ∀ a : ↥M.vertsᶜ, ∃ j : Fin d, M'.Adj (Sum.inl a.1) (Sum.inr j) := by
    intro a
    obtain ⟨w, hw, -⟩ := hM'.1 (hM'.2 (Sum.inl a.1))
    cases w with
    | inl b => exact absurd ⟨b, hw⟩ a.2
    | inr j => exact ⟨j, hw⟩
  choose g hg using hex
  have hinj : Function.Injective g := by
    intro a a' haa
    apply Subtype.ext
    have h1 := hg a
    have h2 := hg a'
    rw [← haa] at h2
    exact Sum.inl.inj (hM'.1.eq_of_adj_right h1 h2)
  have hle := Nat.card_le_card_of_injective g hinj
  rw [Nat.card_coe_set_eq, Nat.card_eq_fintype_card (α := Fin d), Fintype.card_fin] at hle
  have h4 := Set.ncard_add_ncard_compl M.verts
  rw [Nat.card_eq_fintype_card] at h4
  omega

open TuranMatching.Clique in
lemma le_matchingNumber {M : G.Subgraph} (hM : M.IsMatching) :
    M.edgeSet.ncard ≤ matchingNumber G := by
  refine le_csSup ⟨Fintype.card V, ?_⟩ ⟨M, hM, rfl⟩
  rintro m ⟨M', hM', rfl⟩
  have h1 := two_mul_ncard_edgeSet hM'
  have h2 := Set.ncard_add_ncard_compl M'.verts
  rw [Nat.card_eq_fintype_card] at h2
  omega

open TuranMatching.Clique in
lemma matchingNumber_le {k : ℕ} (h : ∀ M : G.Subgraph, M.IsMatching → M.edgeSet.ncard ≤ k) :
    matchingNumber G ≤ k := by
  refine csSup_le ?_ ?_
  · refine ⟨(⊥ : G.Subgraph).edgeSet.ncard, ⊥, ?_, rfl⟩
    intro v hv
    simp at hv
  · rintro m ⟨M, hM, rfl⟩
    exact h M hM

open TuranMatching.Clique in
lemma exists_val_le : ∃ B : Finset V, val G B ≤ matchingNumber G := by
  classical
  obtain ⟨B₀, -, hB₀⟩ := Finset.exists_min_image (Finset.univ : Finset (Finset V)) (val G)
    ⟨∅, Finset.mem_univ _⟩
  have h0 := val_id' (G := G) ∅
  have h0' := hB₀ ∅ (Finset.mem_univ _)
  simp only [Finset.card_empty, add_zero] at h0
  have hm : 2 * val G B₀ ≤ Fintype.card V := by omega
  obtain ⟨M, hM, hcard⟩ := exists_matching_of_def (G := G) (Fintype.card V - 2 * val G B₀)
    ⟨Fintype.card V - val G B₀, by omega⟩ (by
      intro B
      have h1 := val_id' (G := G) B
      have h2 := hB₀ B (Finset.mem_univ _)
      unfold oddCnt at h1
      omega)
  refine ⟨B₀, ?_⟩
  have := two_mul_ncard_edgeSet hM
  have := le_matchingNumber hM
  omega

lemma reach_of_walk {s t : Set V} :
    ∀ {x y : ↥s} (p : (G.induce s).Walk x y), (∀ w ∈ p.support, w.val ∈ t) →
      ∀ (a b : ↥t), x.val = a.val → y.val = b.val → (G.induce t).Reachable a b := by
  intro x y p
  induction p with
  | nil =>
    intro hp a b ha hb
    have : a = b := Subtype.ext (ha.symm.trans hb)
    subst this
    exact Reachable.refl _
  | cons h p ih =>
    rename_i u w v
    intro hp a b ha hb
    have hw : w.val ∈ t := hp w (by simp)
    have hadj : (G.induce t).Adj a ⟨w.val, hw⟩ := by
      show G.Adj a.val w.val
      rw [← ha]
      exact h
    exact hadj.reachable.trans (ih (fun z hz => hp z (by simp [hz])) ⟨w.val, hw⟩ b rfl hb)

lemma odd_le_insert [DecidableEq V] (B : Finset V) (v : V) (hv : v ∉ B)
    (heven : ∀ c : (G.induce ((B : Set V)ᶜ)).ConnectedComponent, v ∈ cset G _ c →
      ¬ Odd c.supp.ncard) :
    (G.induce ((B : Set V)ᶜ)).oddComponents.ncard ≤
      (G.induce (((insert v B : Finset V) : Set V)ᶜ)).oddComponents.ncard := by
  classical
  have hsub : ((insert v B : Finset V) : Set V)ᶜ ⊆ (B : Set V)ᶜ := by
    intro z hz hzB
    exact hz (by simp [hzB])
  have key : ∀ c ∈ (G.induce ((B : Set V)ᶜ)).oddComponents,
      ∃ c' ∈ (G.induce (((insert v B : Finset V) : Set V)ᶜ)).oddComponents,
        cset G _ c' = cset G _ c := by
    intro c hc
    have hc' : Odd c.supp.ncard := hc
    obtain ⟨x, hx⟩ := c.nonempty_supp
    have hnv : ∀ w : ↥((B : Set V)ᶜ), (G.induce ((B : Set V)ᶜ)).connectedComponentMk w = c →
        w.val ≠ v := by
      intro w hw h
      exact heven c ⟨w, (ConnectedComponent.mem_supp_iff _ _).2 hw, h⟩ hc'
    have hxv : x.val ≠ v := hnv x ((ConnectedComponent.mem_supp_iff _ _).1 hx)
    have hx' : x.val ∈ ((insert v B : Finset V) : Set V)ᶜ := by
      simp only [Finset.coe_insert, Set.mem_compl_iff, Set.mem_insert_iff, not_or]
      exact ⟨hxv, x.2⟩
    have hcx : (G.induce ((B : Set V)ᶜ)).connectedComponentMk x = c :=
      (ConnectedComponent.mem_supp_iff _ _).1 hx
    have heq : cset G _ ((G.induce (((insert v B : Finset V) : Set V)ᶜ)).connectedComponentMk
        ⟨x.val, hx'⟩) = cset G _ c := by
      ext z
      constructor
      · intro hz
        obtain ⟨hz', hmk⟩ := mem_cset.1 hz
        have hr := (ConnectedComponent.eq.1 hmk)
        have hr2 := hr.map (G.induceHomOfLE hsub).toHom
        refine mem_cset.2 ⟨hsub hz', ?_⟩
        rw [← hcx]
        exact ConnectedComponent.eq.2 hr2
      · intro hz
        obtain ⟨hz, hmk⟩ := mem_cset.1 hz
        have hr : (G.induce ((B : Set V)ᶜ)).Reachable ⟨z, hz⟩ x :=
          ConnectedComponent.eq.1 (hmk.trans hcx.symm)
        obtain ⟨p⟩ := hr
        have hp : ∀ w ∈ p.support, w.val ∈ ((insert v B : Finset V) : Set V)ᶜ := by
          intro w hw
          have hwc : (G.induce ((B : Set V)ᶜ)).connectedComponentMk w = c := by
            rw [← hcx]
            exact ConnectedComponent.eq.2 (p.dropUntil w hw).reachable
          simp only [Finset.coe_insert, Set.mem_compl_iff, Set.mem_insert_iff, not_or]
          exact ⟨hnv w hwc, w.2⟩
        have hz' : z ∈ ((insert v B : Finset V) : Set V)ᶜ := hp _ p.start_mem_support
        refine mem_cset.2 ⟨hz', ConnectedComponent.eq.2 ?_⟩
        exact reach_of_walk p hp ⟨z, hz'⟩ ⟨x.val, hx'⟩ rfl rfl
    refine ⟨_, ?_, heq⟩
    show Odd _
    rw [← ncard_cset, heq, ncard_cset]
    exact hc'
  have hsub2 : cset G _ '' (G.induce ((B : Set V)ᶜ)).oddComponents ⊆
      cset G _ '' (G.induce (((insert v B : Finset V) : Set V)ᶜ)).oddComponents := by
    rintro _ ⟨c, hc, rfl⟩
    obtain ⟨c', hc', h⟩ := key c hc
    exact ⟨c', hc', h⟩
  have := Set.ncard_le_ncard hsub2 (Set.toFinite _)
  rwa [Set.ncard_image_of_injective _ (cset_injective _),
    Set.ncard_image_of_injective _ (cset_injective _)] at this

end TBAux

open TuranMatching.Clique in
theorem solution (n : ℕ) (G : SimpleGraph (Fin n)) :
    ∃ B : Finset (Fin n), IsOddBarrier G B (matchingNumber G) := by
  classical
  obtain ⟨B₁, hB₁⟩ := TBAux.exists_val_le (G := G)
  have hge : ∀ B, matchingNumber G ≤ TBAux.val G B := fun B =>
    TBAux.matchingNumber_le (fun M hM => TBAux.matching_ncard_le_val hM B)
  obtain ⟨B, hBT, hBmax⟩ := Finset.exists_max_image
    (Finset.univ.filter (fun B : Finset (Fin n) => TBAux.val G B ≤ matchingNumber G))
    (fun B => #B) ⟨B₁, by simpa using hB₁⟩
  have hBval : TBAux.val G B = matchingNumber G :=
    le_antisymm (by simpa using hBT) (hge B)
  have hodd : ∀ c : (G.induce ((B : Set (Fin n))ᶜ)).ConnectedComponent, Odd c.supp.ncard := by
    intro c
    by_contra hc
    obtain ⟨x, hx⟩ := c.nonempty_supp
    have hvB : x.val ∉ B := x.2
    have heven : ∀ c' : (G.induce ((B : Set (Fin n))ᶜ)).ConnectedComponent, x.val ∈ TBAux.cset G _ c' → ¬ Odd c'.supp.ncard := by
      intro c' hc'
      have : c' = c := TBAux.eq_of_mem_cset hc' ⟨x, hx, rfl⟩
      subst this
      exact hc
    have h1 := TBAux.odd_le_insert B x.val hvB heven
    have h2 := TBAux.val_id' (G := G) B
    have h3 := TBAux.val_id' (G := G) (insert x.val B)
    have h4 : #(insert x.val B) = #B + 1 := Finset.card_insert_of_notMem hvB
    unfold TBAux.oddCnt at h2 h3
    have h5 : TBAux.val G (insert x.val B) ≤ matchingNumber G := by
      rw [Fintype.card_fin] at h2 h3
      omega
    have := hBmax (insert x.val B) (by simpa using h5)
    omega
  refine ⟨B, hodd, ?_⟩
  have : ∑ᶠ c : (G.induce ((B : Set (Fin n))ᶜ)).ConnectedComponent, (c.supp.ncard - 1) / 2
      = ∑ᶠ c : (G.induce ((B : Set (Fin n))ᶜ)).ConnectedComponent, c.supp.ncard / 2 :=
    finsum_congr fun c => by have := Nat.odd_iff.1 (hodd c); omega
  rw [this]
  exact hBval
