-- Prove2me | solution 1 for SingleExpBisect.Main.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T09:29:11.979525+00:00
-- url     : https://prove2.me/submissions/7f4f0fff-da9d-4db1-86f9-da5a772ebf8a

/- The cut-edge membership, minimum bound and attainment lemmas are adapted from Secousses, Prove2Me submission 797eedb1-a223-4590-b528-4b3d16d0ab3c (Apache-2.0). -/
import Mathlib
import Definitions.Def_SingleExpBisect_Main_Graphs
import Definitions.Def_SingleExpBisect_Main_NodeData

set_option autoImplicit false

open scoped Classical

open SingleExpBisect.Main

open MinBisectFPT

private lemma mem_cutEdges_mk {n : ℕ} (H : SimpleGraph (Fin n)) (X : Finset (Fin n)) (a b : Fin n) :
    s(a, b) ∈ cutEdges H X ↔ H.Adj a b ∧ ((a ∈ X ∧ b ∉ X) ∨ (b ∈ X ∧ a ∉ X)) := by
  simp only [cutEdges, Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.mem_edgeSet,
    Sym2.eq_iff]
  constructor
  · rintro ⟨hadj, u, hu, v, hv, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
    · exact ⟨hadj, Or.inl ⟨hu, hv⟩⟩
    · exact ⟨hadj, Or.inr ⟨hu, hv⟩⟩
  · rintro ⟨hadj, (⟨ha, hb⟩ | ⟨hb, ha⟩)⟩
    · exact ⟨hadj, a, ha, b, hb, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨hadj, b, hb, a, ha, Or.inr ⟨rfl, rfl⟩⟩

private lemma mu_le {n : ℕ} (G : SimpleGraph (Fin n)) (W S A : Finset (Fin n)) (h : A ∩ W = S) :
    mu G W S ≤ cutSize G A :=
  Nat.sInf_le ⟨A, h, rfl⟩

private lemma mu_attained {n : ℕ} (G : SimpleGraph (Fin n)) (W S : Finset (Fin n)) (hS : S ⊆ W) :
    ∃ A : Finset (Fin n), A ∩ W = S ∧ cutSize G A = mu G W S :=
  Nat.sInf_mem (s := {c : ℕ | ∃ A : Finset (Fin n), A ∩ W = S ∧ cutSize G A = c})
    ⟨cutSize G S, S, Finset.inter_eq_left.mpr hS, rfl⟩

private lemma eta_attained {n : ℕ} (G : SimpleGraph (Fin n)) (W D P : Finset (Fin n)) (hP : P ⊆ D)
    (hD : D ⊆ W) : ∃ E : Finset (Fin n), E ⊆ Finset.univ \ (W \ D) ∧ E ∩ D = P ∧
    cutSize (restrictMinus G (Finset.univ \ (W \ D)) ∅) E = eta G W D P := by
  let O := Finset.univ \ (W \ D)
  have hPO : P ⊆ O := by
    intro x hx
    simp [O, hP hx]
  exact Nat.sInf_mem (s := {c : ℕ | ∃ E : Finset (Fin n), E ⊆ O ∧ E ∩ D = P ∧
      cutSize (restrictMinus G O ∅) E = c})
    ⟨_, P, hPO, Finset.inter_eq_left.mpr hP, rfl⟩

private lemma splitting_cut {n : ℕ} (G : SimpleGraph (Fin n)) (W D : Finset (Fin n))
    (hD : D ⊆ W)
    (sep : ∀ u v, G.Adj u v → u ∈ W → u ∉ D → v ∈ W)
    (X : Finset (Fin n)) :
    cutSize G X = cutSize (restrictMinus G W D) (X ∩ W) +
      cutSize (restrictMinus G (Finset.univ \ (W \ D)) ∅) (X ∩ (Finset.univ \ (W \ D))) := by
  let O := Finset.univ \ (W \ D)
  let A := cutEdges (restrictMinus G W D) (X ∩ W)
  let B := cutEdges (restrictMinus G O ∅) (X ∩ O)
  have ha (u v : Fin n) : (restrictMinus G W D).Adj u v ↔
      G.Adj u v ∧ u ∈ W ∧ v ∈ W ∧ ¬(u ∈ D ∧ v ∈ D) := Iff.rfl
  have hb (u v : Fin n) : (restrictMinus G O ∅).Adj u v ↔
      G.Adj u v ∧ u ∈ O ∧ v ∈ O := by change _ ∧ _ ∧ _ ∧ ¬ (_ ∧ _) ↔ _; simp
  have ho (u : Fin n) : u ∈ O ↔ ¬(u ∈ W ∧ u ∉ D) := by simp [O]
  have hem : cutEdges G X = A ∪ B := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      simp only [A, B, Finset.mem_union, mem_cutEdges_mk, ha, hb, Finset.mem_inter, ho]
      have huv := sep u v
      have hvu : G.Adj u v → v ∈ W → v ∉ D → u ∈ W := fun h => sep v u h.symm
      grind only
  have hd : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro e
    induction e using Sym2.ind with
    | _ u v =>
      simp only [A, B, mem_cutEdges_mk, ha, hb, Finset.mem_inter, ho]
      grind only
  unfold cutSize
  rw [hem, Finset.card_union_of_disjoint hd]

private lemma completion_cost {n : ℕ} (G : SimpleGraph (Fin n)) (W D S : Finset (Fin n))
    (hD : D ⊆ W) (hS : S ⊆ W)
    (sep : ∀ u v, G.Adj u v → u ∈ W → u ∉ D → v ∈ W) :
    mu G W S = cutSize (restrictMinus G W D) S + eta G W D (S ∩ D) := by
  classical
  let O := Finset.univ \ (W \ D)
  have hDO : D ⊆ O := by intro x hx; simp [O, hx]
  obtain ⟨X, hx, hxmin⟩ := mu_attained G W S hS
  have heX : (X ∩ O) ∩ D = S ∩ D := by
    rw [← hx]
    ext z
    simp only [Finset.mem_inter]
    constructor <;> aesop
  have hle : eta G W D (S ∩ D) ≤ cutSize (restrictMinus G O ∅) (X ∩ O) :=
    Nat.sInf_le ⟨X ∩ O, Finset.inter_subset_right, heX, rfl⟩
  apply le_antisymm
  · obtain ⟨E,hE,hed,hem⟩ := eta_attained G W D (S ∩ D) Finset.inter_subset_right hD
    have hew : (S ∪ E) ∩ W = S := by
      ext z
      have : z ∈ E → z ∈ W → z ∈ D := by
        intro he hw
        have hh := hE he
        simpa [hw] using hh
      have hz := Finset.ext_iff.mp hed z
      simp only [Finset.mem_union, Finset.mem_inter] at hz ⊢
      constructor <;> aesop
    have heo : (S ∪ E) ∩ O = E := by
      ext z
      have : z ∈ S → z ∈ O → z ∈ D := by
        intro hs ho
        simpa [O, hS hs] using ho
      have hz := Finset.ext_iff.mp hed z
      simp only [Finset.mem_union, Finset.mem_inter] at hz ⊢
      have hsub : z ∈ E → z ∈ O := fun he => hE he
      tauto
    have hh := mu_le G W S (S ∪ E) hew
    rw [splitting_cut G W D hD sep, hew, show (S ∪ E) ∩ (Finset.univ \ (W \ D)) = E from heo, hem] at hh
    exact hh
  · rw [← hxmin, splitting_cut G W D hD sep, hx]
    exact Nat.add_le_add_left hle _

private lemma cone_mem {n : ℕ} {T : RootedTD n} {t : Fin T.N} {v : Fin n} :
    v ∈ T.cone t ↔ ∃ s, T.Below s t ∧ v ∈ T.bag s := by
  simp only [RootedTD.cone, Finset.mem_filter, Finset.mem_univ, true_and]

private lemma bag_cone {n : ℕ} (T : RootedTD n) (t : Fin T.N) : T.bag t ⊆ T.cone t :=
  fun _ h => cone_mem.mpr ⟨t, .refl, h⟩

private lemma adh_cone {n : ℕ} (T : RootedTD n) (t : Fin T.N) : T.adhesion t ⊆ T.cone t := by
  unfold RootedTD.adhesion
  split
  · exact Finset.empty_subset _
  · exact Finset.inter_subset_left.trans (bag_cone T t)

private lemma boundaryDart {n : ℕ} {T : RootedTD n} {t u v : Fin T.N}
    (hu : T.Below u t) (hv : ¬ T.Below v t) (ha : T.treeGraph.Adj u v) :
    u = t ∧ T.parent u = some v := by
  rcases ha.2 with huv | hvu
  · refine ⟨?_, huv⟩
    rcases hu.cases_head with hh | ⟨w,huw,hw⟩
    · exact hh
    · have : w = v := Option.some.inj (huw.symm.trans huv)
      exact (hv (this ▸ hw)).elim
  · exact (hv (hu.head hvu)).elim

private lemma shared_adh {n : ℕ} {G : SimpleGraph (Fin n)} {T : RootedTD n}
    (hT : IsRootedTreeDecomp G T) {t a b : Fin T.N} {v : Fin n}
    (h1 : T.Below a t) (h2 : ¬T.Below b t) (ha : v ∈ T.bag a) (hb : v ∈ T.bag b) :
    v ∈ T.adhesion t := by
  obtain ⟨p,hp⟩ := hT.2.1.connected.exists_isPath a b
  obtain ⟨e,he,hu,hv⟩ := p.exists_boundary_dart {s | T.Below s t} h1 h2
  obtain ⟨het,hpar⟩ := boundaryDart hu hv e.adj
  have common (s : Fin T.N) (hs : s ∈ p.support) : v ∈ T.bag s :=
    hT.2.2.2.2 a s b p hp hs (Finset.mem_inter.mpr ⟨ha,hb⟩)
  have x := common e.fst (p.dart_fst_mem_support_of_mem_darts he)
  have y := common e.snd (p.dart_snd_mem_support_of_mem_darts he)
  rw [← het, RootedTD.adhesion, hpar]
  exact Finset.mem_inter.mpr ⟨x,y⟩

private lemma node_cost {n : ℕ} {G : SimpleGraph (Fin n)} {T : RootedTD n}
    (hT : IsRootedTreeDecomp G T) (t : Fin T.N) (S : Finset (Fin n)) (hS : S ⊆ T.cone t) :
    mu G (T.cone t) S = cutSize (subtreeGraph G T t) S + etaNode G T t (S ∩ T.adhesion t) := by
  apply completion_cost G (T.cone t) (T.adhesion t) S (adh_cone T t) hS
  intro u v huv hu huid
  obtain ⟨a, ha, hua⟩ := cone_mem.mp hu
  obtain ⟨b,hbu,hbv⟩ := hT.2.2.2.1 u v huv
  by_contra hv
  exact huid (shared_adh hT ha (fun h => hv (cone_mem.mpr ⟨b,h,hbv⟩)) hua hbu)

private lemma parent_outside {n : ℕ} {G : SimpleGraph (Fin n)} {T : RootedTD n}
    (hT : IsRootedTreeDecomp G T) {t s : Fin T.N} (h : T.parent s = some t) : ¬T.Below t s := by
  intro hts
  obtain ⟨r,hr,_⟩ := hT.1
  have hrs : ¬ T.Below r s := by
    intro hrs
    rcases hrs.cases_head with he | ⟨v,huv,_⟩
    · rw [he,h] at hr; contradiction
    · change T.parent r = some v at huv
      rw [hr] at huv; contradiction
  obtain ⟨p,hp⟩ := hT.2.1.connected.exists_isPath s r
  obtain ⟨e,he,hin,hout⟩ := p.exists_boundary_dart {a | T.Below a s} (.refl : T.Below s s) hrs
  obtain ⟨hu,hv⟩ := boundaryDart hin hout e.adj
  rw [hu,h] at hv
  exact hout (Option.some.inj hv ▸ hts)

private lemma comparable {n : ℕ} {T : RootedTD n} {a b c : Fin T.N}
    (hb : T.Below a b) (hc : T.Below a c) : T.Below b c ∨ T.Below c b := by
  induction hb using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inl hc
  | head hab hbc ih =>
    rcases hc.cases_head with h | ⟨z,hz,hzc⟩
    · subst c; exact Or.inr (hbc.head hab)
    · have he := Option.some.inj (hab.symm.trans hz)
      subst z
      exact ih hzc

private lemma sibling_nodes {n : ℕ} {G : SimpleGraph (Fin n)} {T : RootedTD n}
    (hT : IsRootedTreeDecomp G T) {t i j a : Fin T.N}
    (hi : T.parent i = some t) (hj : T.parent j = some t) (hne : i ≠ j)
    (hai : T.Below a i) : ¬ T.Below a j := by
  intro haj
  rcases comparable hai haj with h | h
  · rcases h.cases_head with e | ⟨z,hz,hzj⟩
    · exact hne e
    · exact parent_outside hT hj (Option.some.inj (hz.symm.trans hi) ▸ hzj)
  · rcases h.cases_head with e | ⟨z,hz,hzi⟩
    · exact hne e.symm
    · exact parent_outside hT hi (Option.some.inj (hz.symm.trans hj) ▸ hzi)

private lemma mem_children {n : ℕ} {T : RootedTD n} {t i : Fin T.N} :
    i ∈ T.children t ↔ T.parent i = some t := by simp [RootedTD.children]
private lemma interior_bag_disj {n : ℕ} {G : SimpleGraph (Fin n)} {T : RootedTD n}
    (hT : IsRootedTreeDecomp G T) {t i : Fin T.N} (hi : i ∈ T.children t) :
    Disjoint (T.component i) (T.bag t) := by
  apply Finset.disjoint_left.mpr
  intro v hv hvt
  obtain ⟨hvc,hvd⟩ := Finset.mem_sdiff.mp hv
  obtain ⟨a,ha,hva⟩ := cone_mem.mp hvc
  exact hvd (shared_adh hT ha (parent_outside hT (mem_children.mp hi)) hva hvt)

private lemma interiors_disj {n : ℕ} {G : SimpleGraph (Fin n)} {T : RootedTD n}
    (hT : IsRootedTreeDecomp G T) {t i j : Fin T.N} (hi : i ∈ T.children t)
    (hj : j ∈ T.children t) (hne : i ≠ j) :
    Disjoint (T.component i) (T.component j) := by
  apply Finset.disjoint_left.mpr
  intro v hv hw
  obtain ⟨hvc,hvd⟩ := Finset.mem_sdiff.mp hv
  obtain ⟨awc,awd⟩ := Finset.mem_sdiff.mp hw
  obtain ⟨a,ha,hva⟩ := cone_mem.mp hvc
  obtain ⟨b,hb,hvb⟩ := cone_mem.mp awc
  exact hvd (shared_adh hT ha (sibling_nodes hT (mem_children.mp hj) (mem_children.mp hi) hne.symm hb) hva hvb)

private lemma cone_partition {n : ℕ} {T : RootedTD n} (t : Fin T.N) :
    T.cone t = T.bag t ∪ (T.children t).biUnion T.component := by
  ext v
  simp only [Finset.mem_union, Finset.mem_biUnion, cone_mem]
  constructor
  · rintro ⟨a,ha,hv⟩
    rcases ha.cases_tail with he | ⟨c,hac,hct⟩
    · exact Or.inl (he.symm ▸ hv)
    · by_cases hvc : v ∈ T.adhesion c
      · apply Or.inl
        rw [RootedTD.adhesion, hct] at hvc
        exact (Finset.mem_inter.mp hvc).2
      · exact Or.inr ⟨c, mem_children.mpr hct, Finset.mem_sdiff.mpr ⟨cone_mem.mpr ⟨a, hac, hv⟩, hvc⟩⟩
  · rintro (hb | ⟨c,hc,hv⟩)
    · exact ⟨t, .refl, hb⟩
    · obtain ⟨a,ha,hva⟩ := cone_mem.mp (Finset.mem_sdiff.mp hv).1
      exact ⟨a, ha.tail (mem_children.mp hc), hva⟩

private lemma childCone {n : ℕ} {T : RootedTD n} {t s : Fin T.N}
    (hs : s ∈ T.children t) : T.cone s ⊆ T.cone t := by
  intro x hx
  obtain ⟨a,ha,hx⟩ := cone_mem.mp hx
  exact cone_mem.mpr ⟨a,ha.tail (mem_children.mp hs),hx⟩

private lemma childBoundary {n : ℕ} {T : RootedTD n} {t s : Fin T.N}
    (hs : s ∈ T.children t) : T.adhesion s ⊆ T.bag t := by
  rw [RootedTD.adhesion, mem_children.mp hs]
  exact Finset.inter_subset_right

private lemma cone_sep {n : ℕ} {G : SimpleGraph (Fin n)} {T : RootedTD n}
    (hT : IsRootedTreeDecomp G T) (t : Fin T.N)
    {u v : Fin n} (huv : G.Adj u v) (hu : u ∈ T.cone t) (hnot : u ∉ T.adhesion t) : v ∈ T.cone t := by
  obtain ⟨a,ha,hua⟩ := cone_mem.mp hu
  obtain ⟨b,hbu,hbv⟩ := hT.2.2.2.1 u v huv
  by_contra hv
  exact hnot (shared_adh hT ha (fun hb => hv (cone_mem.mpr ⟨b,hb,hbv⟩)) hua hbu)

private lemma child_edge_interior {n : ℕ} {G : SimpleGraph (Fin n)} {T : RootedTD n}
    {s : Fin T.N} {u v : Fin n} (h : (subtreeGraph G T s).Adj u v) :
    u ∈ T.component s ∨ v ∈ T.component s := by
  change G.Adj u v ∧ u ∈ _ ∧ v ∈ _ ∧ ¬ (u ∈ _ ∧ v ∈ _) at h
  simp only [RootedTD.component, Finset.mem_sdiff]
  tauto

private lemma inner_adj {n : ℕ} {G : SimpleGraph (Fin n)} {T : RootedTD n}
    (hT : IsRootedTreeDecomp G T) {s : Fin T.N} {u v : Fin n}
    (ha : G.Adj u v) (hu : u ∈ T.component s) : (subtreeGraph G T s).Adj u v :=
  let hh := Finset.mem_sdiff.mp hu
  ⟨ha, hh.1, cone_sep hT s ha hh.1 hh.2, fun h => hh.2 h.1⟩

private lemma childParent_edge {n : ℕ} {G : SimpleGraph (Fin n)} {T : RootedTD n}
    (hT : IsRootedTreeDecomp G T) {t s : Fin T.N} (hc : s ∈ T.children t)
    {u v : Fin n} (ha : (subtreeGraph G T s).Adj u v) : (subtreeGraph G T t).Adj u v := by
  have membag : T.adhesion t ⊆ T.bag t := by
    unfold RootedTD.adhesion; split
    · exact Finset.empty_subset _
    · exact Finset.inter_subset_left
  refine ⟨ha.1,childCone hc ha.2.1,childCone hc ha.2.2.1,?_⟩
  rintro ⟨hu,hv⟩
  rcases child_edge_interior ha with h | h
  · exact Finset.disjoint_left.mp (interior_bag_disj hT hc) h (membag hu)
  · exact Finset.disjoint_left.mp (interior_bag_disj hT hc) h (membag hv)

private lemma child_inter_bag {n : ℕ} {G : SimpleGraph (Fin n)} {T : RootedTD n}
    (hT : IsRootedTreeDecomp G T) {t s : Fin T.N} (hs : s ∈ T.children t) :
    T.cone s ∩ T.bag t = T.adhesion s := by
  apply Finset.Subset.antisymm
  · intro u hu
    by_contra h
    exact Finset.disjoint_left.mp (interior_bag_disj hT hs)
      (Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hu).1,h⟩) (Finset.mem_inter.mp hu).2
  · exact Finset.subset_inter (adh_cone T s) (childBoundary hs)

private lemma adj_partition {n : ℕ} {G : SimpleGraph (Fin n)} {T : RootedTD n}
    (hT : IsRootedTreeDecomp G T) (t : Fin T.N) (u v : Fin n) :
    (subtreeGraph G T t).Adj u v ↔ (bagGraph G T t).Adj u v ∨
      ∃ s ∈ T.children t, (subtreeGraph G T s).Adj u v := by
  constructor
  · intro h
    have classify {x y : Fin n} (hy : G.Adj x y) (hx : x ∈ T.cone t) (hb : x ∉ T.bag t) :
        ∃ s ∈ T.children t, (subtreeGraph G T s).Adj x y := by
      rw [cone_partition t] at hx
      obtain ⟨s, hs, hv⟩ := Finset.mem_biUnion.mp ((Finset.mem_union.mp hx).resolve_left hb)
      exact ⟨s,hs,inner_adj hT hy hv⟩
    by_cases hu : u ∈ T.bag t
    · by_cases hv : v ∈ T.bag t
      · exact Or.inl ⟨h.1,hu,hv,h.2.2.2⟩
      · obtain ⟨s,hs,hed⟩ := classify h.1.symm h.2.2.1 hv
        exact Or.inr ⟨s,hs,hed.symm⟩
    · exact Or.inr (classify h.1 h.2.1 hu)
  · rintro (h | ⟨s,hs,h⟩)
    · exact ⟨h.1,bag_cone T t h.2.1,bag_cone T t h.2.2.1,h.2.2.2⟩
    · exact childParent_edge hT hs h

private lemma inner_outside_other {n : ℕ} {G : SimpleGraph (Fin n)} {T : RootedTD n}
    (hT : IsRootedTreeDecomp G T) {t s j : Fin T.N}
    (hs : s ∈ T.children t) (hj : j ∈ T.children t) (hne : s ≠ j)
    {u : Fin n} (hu : u ∈ T.component s) : u ∉ T.cone j := by
  intro hv
  by_cases h : u ∈ T.adhesion j
  · exact Finset.disjoint_left.mp (interior_bag_disj hT hs) hu (childBoundary hj h)
  · exact Finset.disjoint_left.mp (interiors_disj hT hs hj hne) hu (Finset.mem_sdiff.mpr ⟨hv,h⟩)

private lemma measure_partition {n : ℕ} {G : SimpleGraph (Fin n)} {T : RootedTD n}
    (hT : IsRootedTreeDecomp G T) (t : Fin T.N) (X : Finset (Fin n)) :
    cutSize (subtreeGraph G T t) X = cutSize (bagGraph G T t) X +
      ∑ s ∈ T.children t, cutSize (subtreeGraph G T s) X := by
  classical
  let CE := fun s => cutEdges (subtreeGraph G T s) X
  let BE := cutEdges (bagGraph G T t) X
  have eq : cutEdges (subtreeGraph G T t) X = BE ∪ (T.children t).biUnion CE := by
    ext e; induction e using Sym2.ind with
    | _ u v =>
      simp only [BE, CE, Finset.mem_union, Finset.mem_biUnion, mem_cutEdges_mk]
      rw [adj_partition hT t u v]
      aesop
  have h1 : Disjoint BE ((T.children t).biUnion CE) := by
    apply Finset.disjoint_left.mpr
    intro e he he'
    obtain ⟨s,hs,hes⟩ := Finset.mem_biUnion.mp he'
    induction e using Sym2.ind with
    | _ u v =>
      have hB := ((mem_cutEdges_mk ..).mp he).1
      have hC := ((mem_cutEdges_mk ..).mp hes).1
      rcases child_edge_interior hC with hu | hv
      · exact Finset.disjoint_left.mp (interior_bag_disj hT hs) hu hB.2.1
      · exact Finset.disjoint_left.mp (interior_bag_disj hT hs) hv hB.2.2.1
  have h2 : (↑(T.children t) : Set _).PairwiseDisjoint CE := by
    intro s hs j hj hne
    apply Finset.disjoint_left.mpr
    intro e he he'
    induction e using Sym2.ind with
    | _ u v =>
      have hS := ((mem_cutEdges_mk ..).mp he).1
      have hJ := ((mem_cutEdges_mk ..).mp he').1
      rcases child_edge_interior hS with hu | hv
      · exact inner_outside_other hT hs hj hne hu hJ.2.1
      · exact inner_outside_other hT hs hj hne hv hJ.2.2.1
  unfold cutSize
  rw [eq, Finset.card_union_of_disjoint h1, Finset.card_biUnion h2]

private lemma cut_same_on {n : ℕ} (H : SimpleGraph (Fin n)) (V X : Finset (Fin n))
    (hV : ∀ u v, H.Adj u v → u ∈ V) : cutSize H (X ∩ V) = cutSize H X := by
  unfold cutSize; congr 1
  ext e; induction e using Sym2.ind with
  | _ u v =>
    simp only [mem_cutEdges_mk, Finset.mem_inter]
    have h1 := hV u v
    have h2 : H.Adj u v → v ∈ V := fun h => hV v u h.symm
    tauto

private lemma node_cost_eq {n : ℕ} {G : SimpleGraph (Fin n)} {T : RootedTD n}
    (hT : IsRootedTreeDecomp G T) (t : Fin T.N) (X : Finset (Fin n)) (hx : X ⊆ T.cone t) :
    (mu G (T.cone t) X : ℤ) =
    (cutSize (bagGraph G T t) (X ∩ T.bag t) : ℤ) + etaNode G T t ((X ∩ T.bag t) ∩ T.adhesion t) +
      ∑ s ∈ T.children t, ((mu G (T.cone s) (X ∩ T.cone s) : ℤ) -
        etaNode G T s ((X ∩ T.bag t) ∩ T.adhesion s)) := by
  have nodeMem (s : Fin T.N) : T.adhesion s ⊆ T.bag s := by
    unfold RootedTD.adhesion; split
    · exact Finset.empty_subset _
    · exact Finset.inter_subset_left
  have hin (A B : Finset (Fin n)) (h : B ⊆ A) : X ∩ A ∩ B = X ∩ B := by ext v; simp only [Finset.mem_inter]; constructor <;> aesop
  rw [node_cost hT t X hx, Nat.cast_add, measure_partition hT, Nat.cast_add, Nat.cast_sum,
    cut_same_on (bagGraph G T t) (T.bag t) X (fun _ _ h => h.2.1), hin _ _ (nodeMem t)]
  have eq (s : Fin T.N) (hs : s ∈ T.children t) :
      (mu G (T.cone s) (X ∩ T.cone s) : ℤ) - etaNode G T s ((X ∩ T.bag t) ∩ T.adhesion s) =
      cutSize (subtreeGraph G T s) X := by
    rw [node_cost hT s (X ∩ T.cone s) Finset.inter_subset_right, Nat.cast_add,
      cut_same_on (subtreeGraph G T s) (T.cone s) X (fun _ _ h => h.2.1),
      hin _ _ (adh_cone T s), hin _ _ (childBoundary hs)]
    omega
  rw [Finset.sum_congr rfl eq]
  ring

private lemma choose_union {n : ℕ} {G : SimpleGraph (Fin n)} {T : RootedTD n}
    (hT : IsRootedTreeDecomp G T) (t : Fin T.N) (R : Finset (Fin n)) (hR : R ⊆ T.bag t)
    (f : {s // s ∈ T.children t} → Finset (Fin n))
    (hf : ∀ s, f s ⊆ T.cone s.val ∧ f s ∩ T.adhesion s.val = R ∩ T.adhesion s.val) :
    let A := R ∪ Finset.univ.biUnion (fun s => f s \ T.adhesion s.val)
    A ⊆ T.cone t ∧ A ∩ T.bag t = R ∧ ∀ s, A ∩ T.cone s.val = f s := by
  classical
  dsimp only
  let I := fun s : {s // s ∈ T.children t} => f s \ T.adhesion s.val
  have hI (s) : I s ⊆ T.component s.val := fun v hv => Finset.mem_sdiff.mpr ⟨(hf s).1 (Finset.mem_sdiff.mp hv).1,(Finset.mem_sdiff.mp hv).2⟩
  have hAB : (R ∪ Finset.univ.biUnion I) ∩ T.bag t = R := by
    ext v; simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hv,hb⟩; rcases hv with h | ⟨s,hs⟩
      · exact h
      · exact False.elim (Finset.disjoint_left.mp (interior_bag_disj hT s.2) (hI s hs) hb)
    · intro h; exact ⟨Or.inl h,hR h⟩
  refine ⟨?_,hAB,?_⟩
  · intro v hv
    obtain h | ⟨s,_,hi⟩ := (Finset.mem_union.mp hv).imp_right Finset.mem_biUnion.mp
    · exact bag_cone T t (hR h)
    · exact childCone s.2 ((hf s).1 (Finset.mem_sdiff.mp hi).1)
  · intro s
    ext v
    have hb (hv : v ∈ R) (hc : v ∈ T.cone s.val) : v ∈ T.adhesion s.val := by
      rw [←child_inter_bag hT s.2]
      exact Finset.mem_inter.mpr ⟨hc,hR hv⟩
    have hres := Finset.ext_iff.mp (hf s).2 v
    simp only [Finset.mem_inter] at hres
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h,hc⟩; rcases h with r | ⟨j,hj⟩
      · exact (hres.mpr ⟨r,hb r hc⟩).1
      · by_cases he : j = s
        · subst j; exact (Finset.mem_sdiff.mp hj).1
        · exact False.elim (inner_outside_other hT j.2 s.2 (fun eq => he (Subtype.ext eq)) (hI j hj) hc)
    · intro hf'
      refine ⟨?_,(hf s).1 hf'⟩
      by_cases hd : v ∈ T.adhesion s.val
      · exact Or.inl (hres.mp ⟨hf',hd⟩).1
      · exact Or.inr ⟨s, Finset.mem_sdiff.mpr ⟨hf',hd⟩⟩

private lemma reconstruct {n : ℕ} {G : SimpleGraph (Fin n)} {T : RootedTD n}
    (hT : IsRootedTreeDecomp G T) (t : Fin T.N) (X : Finset (Fin n)) (hx : X ⊆ T.cone t) :
    X \ T.bag t = Finset.univ.biUnion
      (fun s : {s // s ∈ T.children t} => (X ∩ T.cone s.val) \ T.adhesion s.val) := by
  ext v; simp only [Finset.mem_sdiff,Finset.mem_biUnion,Finset.mem_inter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨hv,hb⟩
    have hc := hx hv; rw [cone_partition t] at hc
    obtain ⟨s,hs,hvs⟩ := Finset.mem_biUnion.mp ((Finset.mem_union.mp hc).resolve_left hb)
    exact ⟨⟨s,hs⟩,⟨hv,(Finset.mem_sdiff.mp hvs).1⟩,(Finset.mem_sdiff.mp hvs).2⟩
  · rintro ⟨s,⟨hv,hc⟩,hd⟩
    exact ⟨hv,Finset.disjoint_left.mp (interior_bag_disj hT s.2) (Finset.mem_sdiff.mpr ⟨hc,hd⟩)⟩

private lemma count_interior {n : ℕ} {G : SimpleGraph (Fin n)} {T : RootedTD n}
    (hT : IsRootedTreeDecomp G T) (t : Fin T.N) (X : Finset (Fin n)) (hx : X ⊆ T.cone t) :
    (X \ T.bag t).card = ∑ s : {s // s ∈ T.children t}, ((X ∩ T.cone s.val) \ T.adhesion s.val).card := by
  classical
  rw [reconstruct hT t X hx,Finset.card_biUnion]
  intro s hs j hj hne
  apply (interiors_disj hT s.2 j.2 (fun h => hne (Subtype.ext h))).mono
  all_goals intro u hu; obtain ⟨a,b⟩ := Finset.mem_sdiff.mp hu; exact Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp a).2,b⟩

private lemma cost_restrict {n : ℕ} (G : SimpleGraph (Fin n)) (W W' X : Finset (Fin n))
    (hw : W' ⊆ W) (hx : X ⊆ W) : mu G W' (X ∩ W') ≤ mu G W X := by
  obtain ⟨M,hm,hcut⟩ := mu_attained G W X hx
  rw [←hcut]; apply mu_le; rw [←hm]
  ext v; simp only [Finset.mem_inter]; constructor <;> aesop

private lemma p2m_map_sum {ι M N : Type*} (f : M → N) (s : Finset ι)
    (x : ι → AddMonoidAlgebra ℚ M) :
    AddMonoidAlgebra.mapDomain f (∑ a ∈ s, x a) =
    ∑ a ∈ s, AddMonoidAlgebra.mapDomain f (x a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp only [Finset.sum_insert hi, AddMonoidAlgebra.mapDomain_add, ih]

private noncomputable def xw {n : ℕ} (x w : ℤ) : LPoly n :=
  AddMonoidAlgebra.single (Finsupp.single Var.x x + Finsupp.single Var.w w) 1

private lemma xw_mul {n : ℕ} (a b c d : ℤ) :
    xw (n:=n) a b * xw c d = xw (a+c) (b+d) := by
  simp only [xw,AddMonoidAlgebra.single_mul_single,mul_one,Finsupp.single_add]
  congr 1; abel

private lemma xw_zero {n : ℕ} : xw (n:=n) 0 0 = 1 := by
  simp [xw, AddMonoidAlgebra.one_def]

private lemma xw_wPow {n : ℕ} (w : ℤ) : wPow (n:=n) w = xw 0 w := by simp [xw,wPow]

private lemma xw_prod {n : ℕ} {ι : Type*} (s : Finset ι) (a b : ι → ℤ) :
    ∏ i ∈ s, xw (n:=n) (a i) (b i) = xw (∑ i ∈ s,a i) (∑ i ∈ s,b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [xw_zero]
  | insert i s hi ih => simp only [Finset.prod_insert hi,Finset.sum_insert hi,ih,xw_mul]

private lemma xw_nat {n : ℕ} (a b : ℕ) : toL (MvPolynomial.monomial
    (Finsupp.single Var.x a + Finsupp.single Var.w b) (1 : ℚ)) = xw (n:=n) a b := by
  simp only [toL, ← MvPolynomial.single_eq_monomial,AddMonoidAlgebra.mapDomain_single,xw]
  congr 1; ext v; cases v <;> simp [Finsupp.mapRange_apply,Finsupp.single_apply]

private lemma trunc_sum {n : ℕ} {ι : Type*} (k : ℕ) (s : Finset ι) (f : ι → LPoly n) :
    truncWL k (∑ i ∈ s, f i) = ∑ i ∈ s, truncWL k (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [truncWL,Finsupp.filter_zero]
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi,←ih]
    unfold truncWL; simp [Finsupp.filter_add]

private lemma trunc_xw {n : ℕ} (k : ℕ) (a b : ℤ) :
    truncWL k (xw (n:=n) a b) = if b ≤ (k:ℤ) then xw a b else 0 := by
  classical
  by_cases h : b ≤ (k:ℤ)
  · simp only [if_pos h,xw,truncWL,AddMonoidAlgebra.coeff_single]
    rw [Finsupp.filter_single_of_pos (fun e : Var n →₀ ℤ => e Var.w ≤ (k:ℤ)) (by simpa using h)]; rfl
  · simp only [if_neg h,xw,truncWL,AddMonoidAlgebra.coeff_single]
    rw [Finsupp.filter_single_of_neg (fun e : Var n →₀ ℤ => e Var.w ≤ (k:ℤ)) (by simpa using h)]; rfl

private noncomputable def yHom {n : ℕ} (P : Finset (Fin n)) :
    MvPolynomial (Var n) ℚ →+ MvPolynomial (Var n) ℚ where
  toFun := yCoeff P
  map_zero' := by simp [yCoeff]
  map_add' F H := by
    classical
    let f := fun (e : Var n →₀ ℕ) (q : ℚ) =>
      if (∀ v : Fin n, e (Var.y v) = if v ∈ P then 1 else 0) then
        MvPolynomial.monomial (e.filter fun z => ¬ IsYVar z) q else 0
    change ((AddMonoidAlgebra.coeff F + AddMonoidAlgebra.coeff H).sum f) =
      (AddMonoidAlgebra.coeff F).sum f + (AddMonoidAlgebra.coeff H).sum f
    apply Finsupp.sum_add_index'
    · intro e; dsimp only [f]; split <;> simp
    · intro e x y; dsimp only [f]; split <;> simp

private lemma ymono_val {n : ℕ} (A : Finset (Fin n)) (v : Fin n) :
    yMono A (Var.y v) = if v ∈ A then 1 else 0 := by
  simp [yMono,Finsupp.finsetSum_apply,Finsupp.single_apply,eq_comm]

private lemma rename_exponent {n : ℕ} (D A : Finset (Fin n)) (c : ℕ) :
    Finsupp.mapDomain (omegaVar D) (Finsupp.single Var.w c + yMono A) =
      Finsupp.single Var.x (A \ D).card + Finsupp.single Var.w c + yMono (A ∩ D) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [yMono,omegaVar,Finsupp.mapDomain_single]
  | insert i A hi ih =>
    have hs : yMono (insert i A) = Finsupp.single (Var.y i) 1 + yMono A := by simp [yMono,hi]
    rw [hs,add_left_comm,Finsupp.mapDomain_add,Finsupp.mapDomain_single,ih]
    by_cases hd : i ∈ D
    · have e : insert i A \ D = A \ D := by ext x; simp only [Finset.mem_sdiff,Finset.mem_insert]; constructor <;> aesop
      have f : insert i A ∩ D = insert i (A ∩ D) := by ext x; simp only [Finset.mem_inter,Finset.mem_insert]; constructor <;> aesop
      rw [e,f]; simp [omegaVar,hd,yMono,hi,add_comm,add_left_comm,add_assoc]
    · have e : insert i A \ D = insert i (A \ D) := by ext x; simp only [Finset.mem_sdiff,Finset.mem_insert]; constructor <;> aesop
      have f : insert i A ∩ D = A ∩ D := by ext x; simp only [Finset.mem_inter,Finset.mem_insert]; constructor <;> aesop
      rw [e,f,Finset.card_insert_of_notMem (by simp [hi]),Finsupp.single_add]
      simp only [omegaVar,if_neg hd]; abel

private lemma y_omega_mono {n : ℕ} (D P A : Finset (Fin n)) (c : ℕ) :
    yHom P (omega D (MvPolynomial.monomial (Finsupp.single Var.w c + yMono A) (1:ℚ))) =
      if A ∩ D = P then
        MvPolynomial.monomial (Finsupp.single Var.x (A \ D).card + Finsupp.single Var.w c) 1
      else 0 := by
  classical
  let b : Var n →₀ ℕ := Finsupp.single Var.x (A \ D).card + Finsupp.single Var.w c
  have vy (v : Fin n) : (b + yMono (A ∩ D)) (Var.y v) = if v ∈ A ∩ D then 1 else 0 := by
    simp [b,ymono_val]
  have e : (∀ v : Fin n, (b + yMono (A ∩ D)) (Var.y v) = if v ∈ P then 1 else 0) ↔ A ∩ D = P := by
    simp only [vy]; constructor
    · intro h; ext v; have hh := h v
      by_cases h1 : v ∈ A ∩ D <;> by_cases h2 : v ∈ P <;> simp_all
    · intro h; rw [h]; simp
  have erase : (b + yMono (A ∩ D)).filter (fun z => ¬ IsYVar z) = b := by
    ext z; cases z with
    | y v => simp [Finsupp.filter_apply,IsYVar,b]
    | x => simp [Finsupp.filter_apply,IsYVar,yMono,Finsupp.finsetSum_apply]
    | x' => simp [Finsupp.filter_apply,IsYVar,yMono,Finsupp.finsetSum_apply]
    | w => simp [Finsupp.filter_apply,IsYVar,yMono,Finsupp.finsetSum_apply]
  change yCoeff P (MvPolynomial.rename (omegaVar D) _) = _
  rw [MvPolynomial.rename_monomial,rename_exponent]
  change yCoeff P (MvPolynomial.monomial (b + yMono (A ∩ D)) 1) = _
  have e' : (∀ v : Fin n, (yMono (A ∩ D)) (Var.y v) = if v ∈ P then 1 else 0) ↔ A ∩ D = P := by
    simpa [b] using e
  simp [yCoeff,MvPolynomial.support_monomial,e',erase,MvPolynomial.coeff_monomial,b]

private noncomputable def choices {n : ℕ} (G : SimpleGraph (Fin n)) (W D R : Finset (Fin n)) (k : ℕ) :=
  W.powerset.filter (fun A => mu G W A ≤ k ∧ A ∩ D = R)

private lemma choices_mem {n : ℕ} (G : SimpleGraph (Fin n)) (W D R A : Finset (Fin n)) (k : ℕ) :
    A ∈ choices G W D R k ↔ A ⊆ W ∧ mu G W A ≤ k ∧ A ∩ D = R := by
  simp [choices]

private lemma child_factor {n : ℕ} (G : SimpleGraph (Fin n)) (W D P : Finset (Fin n)) (k : ℕ) :
    toL (yCoeff P (omega D (Zfull G W k))) =
    ∑ A ∈ choices G W D P k, xw (n:=n) (A \ D).card (mu G W A) := by
  classical
  change toL (yHom P (omega D (Zfull G W k))) = _
  rw [Zfull,map_sum,map_sum]
  simp only [y_omega_mono,Finset.sum_ite_irrel] 
  rw [←Finset.sum_filter]
  have h : ({x ∈ {A ∈ W.powerset | mu G W A ≤ k} | x ∩ D = P}) = choices G W D P k := by
    ext A; simp [choices,and_assoc]
  rw [h]; unfold toL; rw [p2m_map_sum]
  exact Finset.sum_congr rfl fun i _ => xw_nat _ _

private lemma parent_poly {n : ℕ} (G : SimpleGraph (Fin n)) (W D P : Finset (Fin n)) (k : ℕ) :
    toL (Qpoly G W D k P) = ∑ A ∈ choices G W D P k, xw (n:=n) (A \ D).card (mu G W A) := by
  classical
  unfold Qpoly toL; rw [p2m_map_sum]
  exact Finset.sum_congr rfl fun i _ => xw_nat _ _

theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) (T : RootedTD n) (hT : IsRootedTreeDecomp G T)
    (k : ℕ) (t : Fin T.N) (R : Finset (Fin n)) (hR : R ⊆ T.bag t) :
    toL (Qpoly G (T.cone t) (T.bag t) k R) =
      truncWL k
        (wPow ((cutSize (bagGraph G T t) R + etaNode G T t (R ∩ T.adhesion t) : ℕ) : ℤ) *
          ∏ s ∈ T.children t,
            (wPow (-((etaNode G T s (R ∩ T.adhesion s) : ℕ) : ℤ)) *
              toL (yCoeff (R ∩ T.adhesion s) (Zomega G T k s)))) := by
  classical
  let I := {s // s ∈ T.children t}
  let base : ℤ := (cutSize (bagGraph G T t) R + etaNode G T t (R ∩ T.adhesion t) : ℕ)
  let D := fun s : I => T.adhesion s.val
  let C := fun s : I => T.cone s.val
  let opts := fun s : I => choices G (C s) (D s) (R ∩ D s) k
  let allOpts := Fintype.piFinset opts
  let sz := fun (s : I) (X : Finset (Fin n)) => ((X \ D s).card : ℤ)
  let wt := fun (s : I) (X : Finset (Fin n)) => (mu G (C s) X : ℤ) - etaNode G T s.val (R ∩ D s)
  let sizeOf := fun f : I → Finset (Fin n) => ∑ s, sz s (f s)
  let costOf := fun f : I → Finset (Fin n) => base + ∑ s, wt s (f s)
  let good := allOpts.filter fun f => costOf f ≤ (k:ℤ)
  let restrict := fun (A : Finset (Fin n)) (s : I) => A ∩ C s
  let combine := fun f : I → Finset (Fin n) => R ∪ Finset.univ.biUnion (fun s => f s \ D s)
  let parents := choices G (T.cone t) (T.bag t) R k
  have hchild (s : I) :
      wPow (-(etaNode G T s.val (R ∩ D s) : ℤ)) *
        toL (yCoeff (R ∩ D s) (Zomega G T k s.val)) =
      ∑ A ∈ opts s, xw (sz s A) (wt s A) := by
    rw [Zomega,child_factor,Finset.mul_sum]
    apply Finset.sum_congr rfl; intro A hA
    rw [xw_wPow,xw_mul,zero_add]; congr 1; dsimp [wt]; abel
  have prodEq :
      (∏ s ∈ T.children t, wPow (-(etaNode G T s (R ∩ T.adhesion s) : ℤ)) *
        toL (yCoeff (R ∩ T.adhesion s) (Zomega G T k s))) =
      ∑ f ∈ allOpts, xw (sizeOf f) (∑ s, wt s (f s)) := by
    rw [←Finset.prod_coe_sort]
    change (∏ s : I, _) = _
    trans ∏ s : I, ∑ A ∈ opts s, xw (sz s A) (wt s A)
    · exact Finset.prod_congr rfl (fun s _ => hchild s)
    rw [Finset.prod_univ_sum]
    apply Finset.sum_congr rfl; intro f _
    exact xw_prod _ _ _
  have rhs : truncWL k (wPow (n:=n) base *
      (∑ f ∈ allOpts, xw (sizeOf f) (∑ s, wt s (f s)))) =
      ∑ f ∈ good, xw (sizeOf f) (costOf f) := by
    rw [Finset.mul_sum,trunc_sum]
    simp only [xw_wPow,xw_mul,zero_add,trunc_xw]
    exact (Finset.sum_filter ..).symm
  have weights (A : Finset (Fin n)) (hC : A ⊆ T.cone t) (hb : A ∩ T.bag t = R) :
      ((A \ T.bag t).card : ℤ) = sizeOf (restrict A) ∧ (mu G (T.cone t) A : ℤ) = costOf (restrict A) := by
    constructor
    · rw [count_interior hT t A hC,Nat.cast_sum]
    · have h := node_cost_eq hT t A hC
      rw [hb,←Finset.sum_coe_sort] at h
      simpa only [costOf,base,Nat.cast_add,restrict,wt,C,D] using h
  have choose (f : I → Finset (Fin n)) (hf : f ∈ allOpts) :
      combine f ⊆ T.cone t ∧ combine f ∩ T.bag t = R ∧ restrict (combine f) = f := by
    have hr (s : I) := (choices_mem ..).mp (Fintype.mem_piFinset.mp hf s)
    obtain ⟨a,b,c⟩ := choose_union hT t R hR f (fun s => ⟨(hr s).1,(hr s).2.2⟩)
    exact ⟨a,b,funext c⟩
  have restricted {A : Finset (Fin n)} (ha : A ∈ parents) : restrict A ∈ good := by
    obtain ⟨hC,hk,hb⟩ := (choices_mem ..).mp ha
    apply Finset.mem_filter.mpr
    refine ⟨Fintype.mem_piFinset.mpr (fun s => (choices_mem ..).mpr ⟨Finset.inter_subset_right,
      (cost_restrict G _ _ _ (childCone s.2) hC).trans hk,?_⟩),?_⟩
    · change (A ∩ C s) ∩ D s = R ∩ D s
      rw [←hb]
      ext v; simp only [Finset.mem_inter]
      have h1 : v ∈ D s → v ∈ C s := fun h => adh_cone T s.val h
      have h2 : v ∈ D s → v ∈ T.bag t := fun h => childBoundary s.2 h
      tauto
    · rw [←(weights A hC hb).2]; exact_mod_cast hk
  have combined {f : I → Finset (Fin n)} (hf : f ∈ good) : combine f ∈ parents := by
    obtain ⟨hf,hk⟩ := Finset.mem_filter.mp hf
    obtain ⟨hC,hb,he⟩ := choose f hf
    refine (choices_mem ..).mpr ⟨hC,?_,hb⟩
    have hh := (weights (combine f) hC hb).2
    rw [he] at hh
    exact_mod_cast hh.le.trans hk
  rw [parent_poly,prodEq,rhs]
  refine Finset.sum_bij' (fun A _ => restrict A) (fun f _ => combine f) (fun _ h => restricted h)
    (fun _ h => combined h) ?_ ?_ ?_
  · intro A hA
    obtain ⟨hC,hk,hb⟩ := (choices_mem ..).mp hA
    change R ∪ Finset.univ.biUnion _ = A
    rw [←reconstruct hT t A hC,←hb]
    ext v; simp only [Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]; tauto
  · intro f hf
    exact (choose f (Finset.mem_filter.mp hf).1).2.2
  · intro A hA
    obtain ⟨hC,hk,hb⟩ := (choices_mem ..).mp hA
    rw [(weights A hC hb).1,(weights A hC hb).2]
