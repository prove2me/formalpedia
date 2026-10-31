-- Prove2me | solution 1 for PlanarQueue.Genus.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-30T14:27:05.132559+00:00
-- url     : https://prove2.me/submissions/66e5ffaf-fb3f-4669-9299-9cbdb431deac

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_IsPlanar
import Definitions.Def_PlanarQueue_Genus_Setting
import Definitions.Def_PlanarQueue_Genus_EulerGenus
import Theorems.Thm_PlanarQueue_Genus_lemma_21
import Theorems.Thm_PlanarQueue_Genus_lemma_18
import Theorems.Thm_PlanarQueue_Genus_extra_queues_4g
import Theorems.Thm_PlanarQueue_Genus_eulerGenusLE_component

set_option autoImplicit false

namespace PlanarQueueGlue2

open PlanarQueue.Planar PlanarQueue.Genus

/-- Along an edge the distance from a fixed root grows by at most one. -/
lemma dist_le_dist_add_one {V : Type} (G : SimpleGraph V) {r v w : V}
    (hr : G.Reachable r v) (h : G.Adj v w) : G.dist r w ≤ G.dist r v + 1 := by
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  have := SimpleGraph.dist_le (p.concat h)
  rw [SimpleGraph.Walk.length_concat, hp] at this
  exact this

/-- A queue layout restricts along an injective adjacency-preserving map. -/
lemma orderAdmits_comap {V W : Type} (H : SimpleGraph V) (Gp : SimpleGraph W) (k : ℕ)
    (f : V → W) (hf : Function.Injective f) (hadj : ∀ a b, H.Adj a b → Gp.Adj (f a) (f b))
    (ord : W → ℕ) (h : OrderAdmits Gp k ord) : OrderAdmits H k (ord ∘ f) := by
  obtain ⟨q, hinj, hq⟩ := h
  have hmem : ∀ e : H.edgeSet, Sym2.map f e.1 ∈ Gp.edgeSet := by
    rintro ⟨e, he⟩
    induction e using Sym2.ind with
    | h x y => simpa using hadj x y he
  refine ⟨fun e => q ⟨Sym2.map f e.1, hmem e⟩, hinj.comp hf, ?_⟩
  intro e e' hqe hn
  apply hq _ _ hqe
  obtain ⟨a, b, c, d, hs, h1, h2, h3⟩ := hn
  refine ⟨f a, f b, f c, f d, ?_, h1, h2, h3⟩
  rcases hs with ⟨he, he'⟩ | ⟨he, he'⟩
  · left; exact ⟨by simp [he], by simp [he']⟩
  · right; exact ⟨by simp [he], by simp [he']⟩

/-- In a connected graph every non-root vertex has a neighbour one step closer to the root. -/
lemma exists_parent {V : Type} (G : SimpleGraph V) (hconn : G.Connected) (r v : V) (hv : v ≠ r) :
    ∃ p, G.Adj p v ∧ G.dist r p + 1 = G.dist r v := by
  obtain ⟨w, hw⟩ := (hconn.preconnected v r).exists_walk_length_eq_dist
  cases w with
  | nil => exact absurd rfl hv
  | cons h q =>
    rename_i p
    refine ⟨p, h.symm, ?_⟩
    have h1 : G.dist p r ≤ q.length := SimpleGraph.dist_le q
    have h2 : G.dist r v ≤ G.dist r p + 1 := dist_le_dist_add_one G (hconn.preconnected r p) h.symm
    rw [SimpleGraph.Walk.length_cons] at hw
    rw [SimpleGraph.dist_comm] at hw h1
    omega

/-- Every finite connected graph has a BFS spanning tree at any root. -/
lemma exists_bfsTree {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hconn : G.Connected) (r : V) : ∃ T : SimpleGraph V, IsBFSTree G T r := by
  classical
  have hex : ∀ v, ∃ p, v ≠ r → (G.Adj p v ∧ G.dist r p + 1 = G.dist r v) := by
    intro v
    by_cases hv : v = r
    · exact ⟨r, fun h => absurd hv h⟩
    · obtain ⟨p, hp⟩ := exists_parent G hconn r v hv
      exact ⟨p, fun _ => hp⟩
  choose par hpar using hex
  let T : SimpleGraph V := SimpleGraph.fromRel (fun u v => v ≠ r ∧ u = par v)
  have hTadj : ∀ u v, T.Adj u v ↔ u ≠ v ∧ ((v ≠ r ∧ u = par v) ∨ (u ≠ r ∧ v = par u)) := by
    intro u v; simp [T, SimpleGraph.fromRel_adj]
  have hTG : T ≤ G := by
    intro u v h
    rcases ((hTadj u v).1 h).2 with ⟨hv, rfl⟩ | ⟨hu, rfl⟩
    · exact (hpar v hv).1
    · exact (hpar u hu).1.symm
  have hwalk : ∀ n, ∀ v, G.dist r v = n → ∃ w : T.Walk r v, w.length = n := by
    intro n
    induction n with
    | zero =>
      intro v hv
      have : r = v := (hconn.preconnected r v).dist_eq_zero_iff.1 hv
      subst this; exact ⟨SimpleGraph.Walk.nil, rfl⟩
    | succ n ih =>
      intro v hv
      have hvr : v ≠ r := by
        rintro rfl; simp at hv
      obtain ⟨hadj, hd⟩ := hpar v hvr
      obtain ⟨w, hw⟩ := ih (par v) (by omega)
      have hT : T.Adj (par v) v := by
        rw [hTadj]; exact ⟨hadj.ne, Or.inl ⟨hvr, rfl⟩⟩
      exact ⟨w.concat hT, by rw [SimpleGraph.Walk.length_concat, hw]⟩
  have hTreach : ∀ v, T.Reachable r v := fun v => (hwalk _ v rfl).elim fun w _ => ⟨w⟩
  have hTconn : T.Connected :=
    { preconnected := fun u v => (hTreach u).symm.trans (hTreach v), nonempty := ⟨r⟩ }
  have hdist : ∀ v, T.dist r v = G.dist r v := by
    intro v
    apply le_antisymm
    · obtain ⟨w, hw⟩ := hwalk _ v rfl
      exact hw ▸ SimpleGraph.dist_le w
    · obtain ⟨w, hw⟩ := (hTreach v).exists_walk_length_eq_dist
      have := SimpleGraph.dist_le (w.mapLe hTG)
      rwa [SimpleGraph.Walk.length_mapLe, hw] at this
  let f : {v : V // v ≠ r} → T.edgeSet := fun v =>
    ⟨s(par v.1, v.1), by
      rw [SimpleGraph.mem_edgeSet, hTadj]; exact ⟨(hpar v.1 v.2).1.ne, Or.inl ⟨v.2, rfl⟩⟩⟩
  have hfinj : Function.Injective f := by
    intro v w h
    have h' := congrArg Subtype.val h
    simp only [f, Sym2.eq_iff] at h'
    rcases h' with ⟨-, h2⟩ | ⟨h1, h2⟩
    · exact Subtype.ext h2
    · have a := (hpar v.1 v.2).2
      have b := (hpar w.1 w.2).2
      rw [h1] at a; rw [← h2] at b; omega
  have hfsurj : Function.Surjective f := by
    rintro ⟨e, he⟩
    induction e using Sym2.ind with
    | h x y =>
      rw [SimpleGraph.mem_edgeSet, hTadj] at he
      rcases he.2 with ⟨hy, rfl⟩ | ⟨hx, rfl⟩
      · exact ⟨⟨y, hy⟩, rfl⟩
      · exact ⟨⟨x, hx⟩, Subtype.ext Sym2.eq_swap⟩
  have hcard : Nat.card T.edgeSet + 1 = Nat.card V := by
    rw [← Nat.card_congr (Equiv.ofBijective f ⟨hfinj, hfsurj⟩)]
    simp only [Nat.card_eq_fintype_card]
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    have : 0 < Fintype.card V := Fintype.card_pos_iff.2 ⟨r⟩
    omega
  exact ⟨T, hTG, SimpleGraph.isTree_iff_connected_and_card.2 ⟨hTconn, hcard⟩, hdist⟩

/-- Queue layouts of the components concatenate to a queue layout of the graph. -/
lemma hasQueueLayout_of_components {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ)
    (h : ∀ c : G.ConnectedComponent, HasQueueLayout (G.induce c.supp) k) :
    HasQueueLayout G k := by
  classical
  choose ordc hordc using h
  choose qc hqc using hordc
  have hmemmk : ∀ v : V, v ∈ (G.connectedComponentMk v).supp := fun v =>
    (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).2 rfl
  have hcomp : ∀ u w, G.Adj u w → G.connectedComponentMk u = G.connectedComponentMk w :=
    fun u w h => SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj h
  let o : V → ℕ := fun v => ordc (G.connectedComponentMk v) ⟨v, hmemmk v⟩
  have ho : ∀ (c : G.ConnectedComponent) (v : V) (hv : v ∈ c.supp), o v = ordc c ⟨v, hv⟩ := by
    intro c v hv
    have : G.connectedComponentMk v = c := (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hv
    subst this; rfl
  let M : ℕ := Finset.univ.sup o + 1
  have hoM : ∀ v, o v < M := fun v => Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ v))
  have hM : 0 < M := Nat.succ_pos _
  let e := Fintype.equivFin G.ConnectedComponent
  let O : V → ℕ := fun v => (e (G.connectedComponentMk v)).1 * M + o v
  have hdiv : ∀ v, O v / M = (e (G.connectedComponentMk v)).1 := by
    intro v
    simp only [O]
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hM, Nat.div_eq_of_lt (hoM v), Nat.zero_add]
  have hmod : ∀ v, O v % M = o v := by
    intro v; simp only [O]
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (hoM v)]
  have hblock : ∀ u w x, G.connectedComponentMk u = G.connectedComponentMk x → O u ≤ O w →
      O w ≤ O x → G.connectedComponentMk w = G.connectedComponentMk u := by
    intro u w x hux h1 h2
    have a1 : O u / M ≤ O w / M := Nat.div_le_div_right h1
    have a2 : O w / M ≤ O x / M := Nat.div_le_div_right h2
    rw [hdiv, hdiv] at a1 a2
    rw [← hux] at a2
    exact e.injective (Fin.ext (by omega))
  have hsame : ∀ u w, G.connectedComponentMk u = G.connectedComponentMk w → O u < O w →
      o u < o w := by
    intro u w h hlt
    simp only [O] at hlt
    rw [h] at hlt
    omega
  have hOinj : Function.Injective O := by
    intro u w h
    have h1 := hdiv u
    rw [h, hdiv w] at h1
    have hc : G.connectedComponentMk u = G.connectedComponentMk w := (e.injective (Fin.ext h1)).symm
    have h2 := hmod u
    rw [h, hmod w] at h2
    have hw : w ∈ (G.connectedComponentMk u).supp := by rw [hc]; exact hmemmk w
    rw [ho _ u (hmemmk u), ho _ w hw] at h2
    exact congrArg Subtype.val ((hqc _).1 h2.symm)
  -- every edge of `G` lies in the induced graph of its component
  have hlift : ∀ e : G.edgeSet, ∃ c : G.ConnectedComponent, ∃ x : (G.induce c.supp).edgeSet,
      Sym2.map Subtype.val x.1 = e.1 := by
    rintro ⟨e, he⟩
    induction e using Sym2.ind with
    | h x y =>
      have hy : y ∈ (G.connectedComponentMk x).supp :=
        (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).2 (hcomp x y he).symm
      exact ⟨G.connectedComponentMk x, ⟨s(⟨x, hmemmk x⟩, ⟨y, hy⟩), by simpa using he⟩, by simp⟩
  choose ce e' he' using hlift
  have hmemc : ∀ (c : G.ConnectedComponent) (x : (G.induce c.supp).edgeSet) (v : V),
      v ∈ Sym2.map Subtype.val x.1 → v ∈ c.supp := by
    intro c x v hv
    obtain ⟨a, -, rfl⟩ := Sym2.mem_map.1 hv
    exact a.2
  have hce : ∀ (ed : G.edgeSet) (a d : V), ed.1 = s(a, d) → ce ed = G.connectedComponentMk a := by
    intro ed a d h
    have : a ∈ (ce ed).supp := hmemc _ _ a (by rw [he' ed, h]; exact Sym2.mem_mk_left a d)
    exact ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 this).symm
  have transport : ∀ (c₁ c₂ : G.ConnectedComponent) (_ : c₁ = c₂)
      (x₁ : (G.induce c₁.supp).edgeSet) (x₂ : (G.induce c₂.supp).edgeSet),
      Sym2.map Subtype.val x₁.1 = Sym2.map Subtype.val x₂.1 → qc c₁ x₁ = qc c₂ x₂ := by
    intro c₁ c₂ h x₁ x₂ hx
    subst h
    congr 1
    exact Subtype.ext (Sym2.map.injective Subtype.val_injective hx)
  have core : ∀ (ed fd : G.edgeSet), qc (ce ed) (e' ed) = qc (ce fd) (e' fd) →
      ∀ a b x d : V, ed.1 = s(a, d) → fd.1 = s(b, x) → O a < O b → O b < O x → O x < O d →
      False := by
    intro ed fd hq a b x d hed hfd h1 h2 h3
    have had : G.Adj a d := by have := ed.2; rw [hed] at this; exact this
    have hbx : G.Adj b x := by have := fd.2; rw [hfd] at this; exact this
    have hmad := hcomp a d had
    have hmbx := hcomp b x hbx
    have hmba : G.connectedComponentMk b = G.connectedComponentMk a :=
      hblock a b d hmad h1.le (h2.trans h3).le
    set c := G.connectedComponentMk a with hc
    have ha : a ∈ c.supp := hmemmk a
    have hd : d ∈ c.supp := (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).2 hmad.symm
    have hb : b ∈ c.supp := (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).2 hmba
    have hx : x ∈ c.supp := (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).2 (hmbx.symm.trans hmba)
    let x₁ : (G.induce c.supp).edgeSet := ⟨s(⟨a, ha⟩, ⟨d, hd⟩), by simpa using had⟩
    let x₂ : (G.induce c.supp).edgeSet := ⟨s(⟨b, hb⟩, ⟨x, hx⟩), by simpa using hbx⟩
    have t1 : qc (ce ed) (e' ed) = qc c x₁ :=
      transport _ _ (hce ed a d hed) _ _ (by rw [he' ed, hed]; simp [x₁])
    have t2 : qc (ce fd) (e' fd) = qc c x₂ :=
      transport _ _ ((hce fd b x hfd).trans hmba) _ _ (by rw [he' fd, hfd]; simp [x₂])
    have hq' : qc c x₁ = qc c x₂ := t1.symm.trans (hq.trans t2)
    refine (hqc c).2 x₁ x₂ hq' ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨x, hx⟩, ⟨d, hd⟩, Or.inl ⟨rfl, rfl⟩, ?_, ?_, ?_⟩
    · rw [← ho c a ha, ← ho c b hb]; exact hsame a b hmba.symm h1
    · rw [← ho c b hb, ← ho c x hx]; exact hsame b x hmbx h2
    · rw [← ho c x hx, ← ho c d hd]
      exact hsame x d (hmbx.symm.trans (hmba.trans hmad)) h3
  refine ⟨O, fun ed => qc (ce ed) (e' ed), hOinj, ?_⟩
  intro ed fd hq hn
  obtain ⟨a, b, x, d, hs, h1, h2, h3⟩ := hn
  rcases hs with ⟨he, hf⟩ | ⟨he, hf⟩
  · exact core ed fd hq a b x d he hf h1 h2 h3
  · exact core fd ed hq.symm a b x d hf he h1 h2 h3

/-- The connected case of Theorem 2 (p. 22): Lemma 21, then Lemma 18 on `G⁺`, then the `4g`
extra queues for the vertices of `Z`. -/
lemma theorem2_connected (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hconn : G.Connected) (g : ℕ) (hG : EulerGenusLE G g) :
    HasQueueLayout G (4 * g + 49) := by
  classical
  obtain ⟨r⟩ := hconn.nonempty
  obtain ⟨T, hT⟩ := exists_bfsTree G hconn r
  obtain ⟨Z, -, hZc, -, W, hWfin, Gp, Tp, rp, ι, hGpconn, hGpplanar, hιadj, hTp, hdist, -⟩ :=
    PlanarQueue.Genus.lemma_21 V G hconn g hG T r hT
  have _instW : Fintype W := Fintype.ofFinite W
  have hBFS : PlanarQueue.Genus.IsBFSLayering Gp (Gp.dist rp) :=
    ⟨{rp}, fun v => ⟨rp, ⟨Finset.mem_singleton_self _, hGpconn.preconnected rp v⟩,
      fun r' h => Finset.mem_singleton.1 h.1⟩,
     fun r' hr' v _ => by rw [Finset.mem_singleton.1 hr']⟩
  obtain ⟨ord', hord', hmono'⟩ := PlanarQueue.Genus.lemma_18 W Gp hGpplanar (Gp.dist rp) hBFS
  let Z' : Finset V := Z.verts.toFinset
  have hlay : IsLayering G (G.dist r) := fun v w h =>
    ⟨dist_le_dist_add_one G (hconn.preconnected r w) h.symm,
     dist_le_dist_add_one G (hconn.preconnected r v) h⟩
  have hZ : ∀ j : ℕ, (Z'.filter (fun v => G.dist r v = j)).card ≤ 2 * g := by
    intro j
    have := hZc j
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at this
    convert this using 2
    ext v; simp [Z']
  let jj : ↥((↑Z' : Set V)ᶜ) → ↥(Z.vertsᶜ) := fun a => ⟨a.1, by simpa [Z'] using a.2⟩
  have hjj : Function.Injective jj := fun a b h => Subtype.ext (by have := congrArg Subtype.val h; exact this)
  have h₀ : OrderAdmits (G.induce (↑Z' : Set V)ᶜ) 49 (ord' ∘ (ι ∘ jj)) :=
    orderAdmits_comap _ Gp 49 (ι ∘ jj) (ι.injective.comp hjj)
      (fun a b h => hιadj (jj a) (jj b) h) ord' hord'
  refine PlanarQueue.Genus.extra_queues_4g V G (G.dist r) hlay g Z' hZ (ord' ∘ (ι ∘ jj)) h₀ ?_
  intro a b hab
  show ord' (ι (jj a)) < ord' (ι (jj b))
  apply hmono'
  rw [hdist, hdist]
  exact hab

end PlanarQueueGlue2

theorem solution (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (g : ℕ) (hG : PlanarQueue.Genus.EulerGenusLE G g) :
    PlanarQueue.Planar.HasQueueLayout G (4 * g + 49) := by
  classical
  apply PlanarQueueGlue2.hasQueueLayout_of_components
  intro c
  exact PlanarQueueGlue2.theorem2_connected c.supp (G.induce c.supp)
    (SimpleGraph.ConnectedComponent.maximal_connected_induce_supp c).1 g
    (PlanarQueue.Genus.eulerGenusLE_component V G g hG c)
