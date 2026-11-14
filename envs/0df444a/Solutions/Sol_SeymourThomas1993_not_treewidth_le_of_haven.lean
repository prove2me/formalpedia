-- Prove2me | solution 1 for SeymourThomas1993.not_treewidth_le_of_haven
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-13T20:01:59.834212+00:00
-- url     : https://prove2.me/submissions/c492cc60-e7a9-48e3-bf08-f7fe84263aba

import Definitions.Def_DvorakNorin2018_HavenCloudConfiguration
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped Classical
namespace StableMSR.Recovery.TreeHelly

/-- A set contains the unique tree path between any two of its vertices. -/
def PathConvex {T : Type} (tree : SimpleGraph T) (C : Finset T) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, ∀ p : tree.Walk x y, p.IsPath → ∀ z ∈ p.support, z ∈ C

lemma leaf_neighbor_mem {T : Type} [Fintype T] [DecidableEq T]
    (tree : SimpleGraph T) (htree : tree.IsTree) {v w : T}
    (hadj : tree.Adj v w) (huniq : ∀ u, tree.Adj v u → u = w)
    (C : Finset T) (hc : PathConvex tree C) (hv : v ∈ C) (hC : C ≠ {v}) :
    w ∈ C := by
  classical
  obtain ⟨x, hx, hxv⟩ : ∃ x ∈ C, x ≠ v := by
    by_contra hn
    apply hC
    ext x
    simp only [Finset.mem_singleton]
    constructor
    · intro hx
      by_contra hne
      exact hn ⟨x, hx, hne⟩
    · rintro rfl
      exact hv
  obtain ⟨p, hp⟩ := htree.connected.exists_isPath v x
  have hnil : ¬ p.Nil := SimpleGraph.Walk.not_nil_of_ne hxv.symm
  have hw : p.snd = w := huniq _ (p.adj_snd hnil)
  exact hw ▸ hc v hv x hx p hp p.snd (List.mem_of_mem_tail (p.snd_mem_tail_support hnil))

/-- The Helly property for arbitrary families of nonempty path-convex subsets
of a finite tree. The index type need not be finite. -/
theorem finite_tree_helly {T : Type} [Fintype T] [DecidableEq T]
    (tree : SimpleGraph T) (htree : tree.IsTree) {I : Type*}
    (C : I → Finset T) (hne : ∀ i, (C i).Nonempty)
    (hconv : ∀ i, PathConvex tree (C i))
    (hpair : ∀ i j, ((C i) ∩ (C j)).Nonempty) :
    ∃ t : T, ∀ i, t ∈ C i := by
  classical
  have aux : ∀ n : ℕ, ∀ (T : Type) [Fintype T] [DecidableEq T],
      Fintype.card T = n → ∀ (tree : SimpleGraph T), tree.IsTree →
      ∀ (C : I → Finset T), (∀ i, (C i).Nonempty) →
      (∀ i, PathConvex tree (C i)) →
      (∀ i j, ((C i) ∩ (C j)).Nonempty) → ∃ t : T, ∀ i, t ∈ C i := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro T _ _ hcard tree ht C hne hc hp
      by_cases hsub : Subsingleton T
      · obtain ⟨t⟩ := ht.connected.nonempty
        refine ⟨t, ?_⟩
        intro i
        obtain ⟨x, hx⟩ := hne i
        exact (hsub.elim x t) ▸ hx
      · letI : Nontrivial T := not_subsingleton_iff_nontrivial.mp hsub
        obtain ⟨v, hvdeg⟩ := ht.exists_vert_degree_one_of_nontrivial
        obtain ⟨w, hvw, hw⟩ := tree.degree_eq_one_iff_existsUnique_adj.mp hvdeg
        by_cases hsing : ∃ i, C i = {v}
        · obtain ⟨i, hi⟩ := hsing
          refine ⟨v, ?_⟩
          intro j
          obtain ⟨x, hx⟩ := hp i j
          obtain ⟨hxi, hxj⟩ := Finset.mem_inter.mp hx
          rw [hi, Finset.mem_singleton] at hxi
          exact hxi ▸ hxj
        · have hnot : ∀ i, C i ≠ {v} := by simpa only [not_exists] using hsing
          let U : Set T := {v}ᶜ
          let tree' := tree.induce U
          have ht' : tree'.IsTree :=
            ⟨ht.connected.induce_compl_singleton_of_degree_eq_one hvdeg, ht.isAcyclic.induce U⟩
          let C' : I → Finset U := fun i => Finset.univ.filter (fun x => x.val ∈ C i)
          have hne' : ∀ i, (C' i).Nonempty := by
            intro i
            obtain ⟨x, hx⟩ := hne i
            by_cases hxv : x = v
            · have hvC : v ∈ C i := hxv ▸ hx
              have hwC := leaf_neighbor_mem tree ht hvw hw (C i) (hc i) hvC (hnot i)
              refine ⟨⟨w, ?_⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwC⟩⟩
              exact fun heq => tree.ne_of_adj hvw heq.symm
            · exact ⟨⟨x, hxv⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
          have hc' : ∀ i, PathConvex tree' (C' i) := by
            intro i x hx y hy p hpath z hz
            have hxC := (Finset.mem_filter.mp hx).2
            have hyC := (Finset.mem_filter.mp hy).2
            let f : tree' →g tree := {toFun := Subtype.val, map_rel' := by intro x y h; exact h}
            have hpath' : (p.map f).IsPath := hpath.map Subtype.val_injective
            have hz' : z.val ∈ (p.map f).support := by
              rw [SimpleGraph.Walk.support_map]
              exact List.mem_map.mpr ⟨z, hz, rfl⟩
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc i x.val hxC y.val hyC
              (p.map f) hpath' z.val hz'⟩
          have hp' : ∀ i j, (C' i ∩ C' j).Nonempty := by
            intro i j
            obtain ⟨x, hx⟩ := hp i j
            obtain ⟨hxi, hxj⟩ := Finset.mem_inter.mp hx
            by_cases hxv : x = v
            · have hi := leaf_neighbor_mem tree ht hvw hw (C i) (hc i) (hxv ▸ hxi) (hnot i)
              have hj := leaf_neighbor_mem tree ht hvw hw (C j) (hc j) (hxv ▸ hxj) (hnot j)
              exact ⟨⟨w, fun heq => tree.ne_of_adj hvw heq.symm⟩,
                Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩,
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩⟩
            · exact ⟨⟨x, hxv⟩, Finset.mem_inter.mpr
                ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxi⟩,
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxj⟩⟩⟩
          have hlt : Fintype.card U < n := by
            rw [← hcard]
            exact Fintype.card_subtype_lt (x := v) (by simp [U])
          obtain ⟨t, htC⟩ := ih (Fintype.card U) hlt U rfl tree' ht' C' hne' hc' hp'
          exact ⟨t.val, fun i => (Finset.mem_filter.mp (htC i)).2⟩
  exact aux (Fintype.card T) T rfl tree htree C hne hconv hpair

/-- Every clique of graph vertices is covered by one bag of the canonical
tree decomposition, including the empty clique. -/
theorem clique_subset_bag {V T : Type} [DecidableEq V] [Fintype T] [DecidableEq T]
    (G : SimpleGraph V) (tree : SimpleGraph T) (bags : T → Finset V)
    (htd : RobertsonSeymour1986.GM5.IsTreeDecomposition G tree bags)
    (K : Finset V) (hK : (K : Set V).Pairwise G.Adj) :
    ∃ t : T, K ⊆ bags t := by
  classical
  let C : K → Finset T := fun v => Finset.univ.filter (fun t => v.val ∈ bags t)
  have hne : ∀ v, (C v).Nonempty := by
    intro v
    obtain ⟨t, ht⟩ := htd.2.1 v.val
    exact ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩⟩
  have hconv : ∀ v, PathConvex tree (C v) := by
    intro v x hx y hy p hp z hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      htd.2.2.2 x z y p hp hz (Finset.mem_inter.mpr
        ⟨(Finset.mem_filter.mp hx).2, (Finset.mem_filter.mp hy).2⟩)⟩
  have hpair : ∀ v w, (C v ∩ C w).Nonempty := by
    intro v w
    by_cases heq : v = w
    · subst w
      simpa only [Finset.inter_self] using hne v
    · have hadj := hK v.property w.property (fun h => heq (Subtype.ext h))
      obtain ⟨t, htv, htw⟩ := htd.2.2.1 v.val w.val hadj
      exact ⟨t, Finset.mem_inter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, htv⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, htw⟩⟩⟩
  obtain ⟨t, ht⟩ := finite_tree_helly tree htd.1 C hne hconv hpair
  exact ⟨t, fun v hv => (Finset.mem_filter.mp (ht ⟨v, hv⟩)).2⟩

end StableMSR.Recovery.TreeHelly
namespace StableMSR.Recovery.HavenTreewidthObstruction
open Havens TreeHelly RobertsonSeymour1986.GM5

/-- Lift a walk in a connected vertex set to a walk through bags meeting that set. -/
lemma lift_connected_walk {V T : Type} [DecidableEq V] [DecidableEq T]
    (G : SimpleGraph V) (tree : SimpleGraph T) (bags : T → Finset V)
    (htd : IsTreeDecomposition G tree bags) {C : Finset V} {u v : V}
    (p : G.Walk u v) (hp : ∀ z ∈ p.support, z ∈ C)
    (s t : T) (hs : u ∈ bags s) (ht : v ∈ bags t) :
    ∃ q : tree.Walk s t, ∀ z ∈ q.support, ∃ c ∈ C, c ∈ bags z := by
  induction p generalizing s with
  | nil =>
    obtain ⟨q,hq⟩ := htd.1.connected.exists_isPath s t
    refine ⟨q,?_⟩
    intro z hz
    exact ⟨_, hp _ (by simp), htd.2.2.2 s z t q hq hz (Finset.mem_inter.mpr ⟨hs,ht⟩)⟩
  | @cons u v w huv p ih =>
    obtain ⟨b,hbu,hbv⟩ := htd.2.2.1 u v huv
    obtain ⟨q,hq⟩ := htd.1.connected.exists_isPath s b
    have htail : ∀ z ∈ p.support, z ∈ C := by
      intro z hz; exact hp z (by simp only [SimpleGraph.Walk.support_cons,List.mem_cons]; exact Or.inr hz)
    obtain ⟨r,hr⟩ := ih htail b hbv ht
    refine ⟨q.append r,?_⟩
    intro z hz
    have hz' : z ∈ q.support ∨ z ∈ r.support := by
      exact (SimpleGraph.Walk.mem_support_append_iff q r).mp hz
    rcases hz' with hzq | hzr
    · exact ⟨u,hp u (by simp),htd.2.2.2 s z b q hq hzq (Finset.mem_inter.mpr ⟨hs,hbu⟩)⟩
    · exact hr z hzr

noncomputable def bagSupport {V T : Type} [DecidableEq V] [Fintype T]
    (bags : T → Finset V) (C : Finset V) : Finset T :=
  Finset.univ.filter (fun t => ∃ c ∈ C, c ∈ bags t)

lemma bagSupport_nonempty {V T : Type} [DecidableEq V] [Fintype T]
    {G : SimpleGraph V} {tree : SimpleGraph T} {bags : T → Finset V}
    (htd : IsTreeDecomposition G tree bags) {C : Finset V} (hC : C.Nonempty) :
    (bagSupport bags C).Nonempty := by
  classical
  obtain ⟨v,hv⟩ := hC
  obtain ⟨t,ht⟩ := htd.2.1 v
  exact ⟨t,Finset.mem_filter.mpr ⟨Finset.mem_univ _,v,hv,ht⟩⟩

lemma bagSupport_convex {V T : Type} [DecidableEq V] [Fintype T] [DecidableEq T]
    {G : SimpleGraph V} {tree : SimpleGraph T} {bags : T → Finset V}
    (htd : IsTreeDecomposition G tree bags) {C : Finset V} (hC : ConnectedSet G C) :
    PathConvex tree (bagSupport bags C) := by
  classical
  intro s hs t ht p hp z hz
  obtain ⟨u,hu,hbu⟩ := (Finset.mem_filter.mp hs).2
  obtain ⟨v,hv,hbv⟩ := (Finset.mem_filter.mp ht).2
  obtain ⟨q,hq⟩ := hC.2 u hu v hv
  obtain ⟨r,hr⟩ := lift_connected_walk G tree bags htd q hq s t hbu hbv
  have he := htd.1.isAcyclic.subsingleton_path s t |>.elim ⟨p,hp⟩ r.toPath
  have hpR : p = r.toPath.val := congrArg Subtype.val he
  have hzR : z ∈ r.support := by
    rw [hpR] at hz
    exact r.support_toPath_subset_support hz
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr z hzR⟩

lemma bagSupport_inter_of_touch {V T : Type} [DecidableEq V] [Fintype T] [DecidableEq T]
    {G : SimpleGraph V} {tree : SimpleGraph T} {bags : T → Finset V}
    (htd : IsTreeDecomposition G tree bags) {C D : Finset V} (h : Touch G C D) :
    (bagSupport bags C ∩ bagSupport bags D).Nonempty := by
  classical
  rcases h with ⟨v,hvC,hvD⟩ | ⟨u,hu,v,hv,hadj⟩
  · obtain ⟨t,ht⟩ := htd.2.1 v
    exact ⟨t,Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,v,hvC,ht⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,v,hvD,ht⟩⟩⟩
  · obtain ⟨t,htu,htv⟩ := htd.2.2.1 u v hadj
    exact ⟨t,Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,u,hu,htu⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,v,hv,htv⟩⟩⟩

/-- Every family of pairwise touching connected sets has a common hitting bag. -/
theorem common_hitting_bag {V T : Type} [DecidableEq V] [Fintype T] [DecidableEq T]
    {G : SimpleGraph V} {tree : SimpleGraph T} {bags : T → Finset V}
    (htd : IsTreeDecomposition G tree bags) {I : Type*} (C : I → Finset V)
    (hC : ∀ i, ConnectedSet G (C i)) (htouch : ∀ i j, Touch G (C i) (C j)) :
    ∃ t, ∀ i, ∃ c ∈ C i, c ∈ bags t := by
  classical
  obtain ⟨t,ht⟩ := finite_tree_helly tree htd.1 (fun i => bagSupport bags (C i))
    (fun i => bagSupport_nonempty htd (hC i).1)
    (fun i => bagSupport_convex htd (hC i))
    (fun i j => bagSupport_inter_of_touch htd (htouch i j))
  exact ⟨t,fun i => (Finset.mem_filter.mp (ht i)).2⟩

/-- A haven cannot avoid every bag of a finite tree decomposition. -/
theorem haven_forces_large_bag {V T : Type} [DecidableEq V] [Fintype T] [DecidableEq T]
    {G : SimpleGraph V} {tree : SimpleGraph T} {bags : T → Finset V}
    (htd : IsTreeDecomposition G tree bags) {k : ℕ} {β : Finset V → Finset V}
    (hβ : Haven G k β) : ∃ t, k ≤ (bags t).card := by
  classical
  by_contra hn
  have hsmall : ∀ t, (bags t).card < k := by simpa using hn
  obtain ⟨t,ht⟩ := common_hitting_bag htd (fun s => β (bags s))
    (fun s => (hβ.flap (bags s) (hsmall s)).connected)
    (fun s s' => hβ.touch (bags s) (bags s') (hsmall s) (hsmall s'))
  obtain ⟨v,hvC,hvbag⟩ := ht t
  exact Finset.disjoint_left.mp (hβ.flap (bags t) (hsmall t)).avoids hvbag hvC

/-- The easy direction of treewidth–haven duality, with the canonical width convention. -/
theorem haven_order_le_of_treewidthLE {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {w k : ℕ} (htw : TreewidthLE G w)
    {β : Finset V → Finset V} (hβ : Haven G k β) : k ≤ w+1 := by
  classical
  obtain ⟨T,hT,tree,bags,htd,hwidth⟩ := htw
  letI := hT
  obtain ⟨t,ht⟩ := haven_forces_large_bag htd hβ
  exact ht.trans (hwidth t)

/-- A haven of order `w+2` witnesses failure of width at most `w`. -/
theorem not_treewidthLE_of_haven {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {w : ℕ} {β : Finset V → Finset V}
    (hβ : Haven G (w+2) β) : ¬ TreewidthLE G w := by
  intro htw
  have h := haven_order_le_of_treewidthLE htw hβ
  omega
end StableMSR.Recovery.HavenTreewidthObstruction

open StableMSR.Recovery.Havens RobertsonSeymour1986.GM5
theorem solution {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {w : ℕ} {β : Finset V → Finset V}
    (hβ : Haven G (w+2) β) : ¬ TreewidthLE G w := by
  exact StableMSR.Recovery.HavenTreewidthObstruction.not_treewidthLE_of_haven hβ
