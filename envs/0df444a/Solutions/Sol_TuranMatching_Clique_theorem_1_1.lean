-- Prove2me | solution 1 for TuranMatching.Clique.theorem_1_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-30T04:53:17.361874+00:00
-- url     : https://prove2.me/submissions/3597c164-28b5-455f-97f8-94d2079e55e8

import Definitions.Def_TuranMatching_Clique_Setting

-- BEGIN MODULE TMProof.MatchingNumber

namespace TuranMatching.Clique.TMFresh
open SimpleGraph

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

theorem matching_sizes_bounded : BddAbove {m : ℕ | ∃ M : G.Subgraph,
    M.IsMatching ∧ M.edgeSet.ncard = m} := by
  refine ⟨G.edgeSet.ncard, ?_⟩
  rintro m ⟨M, _, rfl⟩
  exact Set.ncard_le_ncard M.edgeSet_subset

theorem matching_size_le (M : G.Subgraph) (hM : M.IsMatching) :
    M.edgeSet.ncard ≤ matchingNumber G := by
  exact le_csSup (matching_sizes_bounded G) ⟨M, hM, rfl⟩

theorem matchingNumber_le_iff (s : ℕ) : matchingNumber G ≤ s ↔
    ∀ M : G.Subgraph, M.IsMatching → M.edgeSet.ncard ≤ s := by
  constructor
  · intro h M hM
    exact (matching_size_le G M hM).trans h
  · intro h
    apply csSup_le'
    rintro m ⟨M, hM, rfl⟩
    exact h M hM

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.MatchingNumber

-- BEGIN MODULE TMProof.OddCertificate

namespace TuranMatching.Clique.TMFresh
open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

structure OddCertificate (G : SimpleGraph V) (B : Finset V)
    (blocks : Finset (Finset V)) (s : ℕ) : Prop where
  nonempty : ∀ C ∈ blocks, C.Nonempty
  odd : ∀ C ∈ blocks, Odd C.card
  disjoint : ∀ C ∈ blocks, Disjoint C B
  pairwise : Set.PairwiseDisjoint (blocks : Set (Finset V)) id
  cover : ∀ v, v ∉ B ↔ ∃ C ∈ blocks, v ∈ C
  edges : ∀ C ∈ blocks, ∀ D ∈ blocks, C ≠ D →
    ∀ u ∈ C, ∀ v ∈ D, ¬ G.Adj u v
  budget : B.card + ∑ C ∈ blocks, (C.card - 1) / 2 = s

omit [Fintype V] [DecidableEq V] in
theorem OddCertificate.of_outside_eq {G H : SimpleGraph V} {B : Finset V}
    {blocks : Finset (Finset V)} {s : ℕ} (hc : OddCertificate G B blocks s)
    (he : ∀ u ∉ B, ∀ v ∉ B, H.Adj u v ↔ G.Adj u v) :
    OddCertificate H B blocks s := by
  refine ⟨hc.nonempty, hc.odd, hc.disjoint, hc.pairwise, hc.cover, ?_, hc.budget⟩
  intro C hC D hD hne u hu v hv hadj
  have huB : u ∉ B := (hc.cover u).mpr ⟨C, hC, hu⟩
  have hvB : v ∉ B := (hc.cover v).mpr ⟨D, hD, hv⟩
  exact hc.edges C hC D hD hne u hu v hv ((he u huB v hvB).mp hadj)

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.OddCertificate

-- BEGIN MODULE TMProof.Optimizer

namespace TuranMatching.Clique.TMFresh
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def blockSquare (blocks : Finset (Finset V)) : ℕ := ∑ C ∈ blocks, C.card^2

structure OptimalCertificate (G : SimpleGraph V) (B : Finset V)
    (blocks : Finset (Finset V)) (k s : ℕ) : Prop where
  certificate : OddCertificate G B blocks s
  cliqueFree : G.CliqueFree (k+1)
  edge_max : ∀ H : SimpleGraph V, ∀ bs, OddCertificate H B bs s → H.CliqueFree (k+1) →
    H.edgeSet.ncard ≤ G.edgeSet.ncard
  square_max : ∀ H : SimpleGraph V, ∀ bs, OddCertificate H B bs s → H.CliqueFree (k+1) →
    H.edgeSet.ncard = G.edgeSet.ncard → blockSquare bs ≤ blockSquare blocks

theorem exists_optimal_certificate (G : SimpleGraph V) (B : Finset V)
    (blocks : Finset (Finset V)) (k s : ℕ)
    (hc : OddCertificate G B blocks s) (hk : G.CliqueFree (k+1)) :
    ∃ H bs, OptimalCertificate H B bs k s ∧ G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  classical
  let candidates : Finset (SimpleGraph V × Finset (Finset V)) :=
    univ.filter (fun p => OddCertificate p.1 B p.2 s ∧ p.1.CliqueFree (k+1))
  have hmem : (G,blocks) ∈ candidates := mem_filter.mpr ⟨mem_univ _,hc,hk⟩
  obtain ⟨p,hp,hmax⟩ := exists_max_image candidates (fun p => p.1.edgeSet.ncard) ⟨_,hmem⟩
  let tied := candidates.filter (fun q => q.1.edgeSet.ncard = p.1.edgeSet.ncard)
  have htied : p ∈ tied := mem_filter.mpr ⟨hp,rfl⟩
  obtain ⟨q,hq,hsq⟩ := exists_max_image tied (fun q => blockSquare q.2) ⟨_,htied⟩
  have hq' := mem_filter.mp hq
  have hvalid := (mem_filter.mp hq'.1).2
  refine ⟨q.1,q.2,⟨hvalid.1,hvalid.2,?_,?_⟩,?_⟩
  · intro H bs hh hhk
    have hm : (H,bs) ∈ candidates := mem_filter.mpr ⟨mem_univ _,hh,hhk⟩
    exact (hmax _ hm).trans_eq hq'.2.symm
  · intro H bs hh hhk he
    apply hsq (H,bs)
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,hh,hhk⟩,he.trans hq'.2⟩
  · exact (hmax _ hmem).trans_eq hq'.2.symm

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.Optimizer

-- BEGIN MODULE TMProof.CloneBasics

namespace TuranMatching.Clique.TMFresh
open Finset SimpleGraph

variable {V : Type*} [DecidableEq V]

def cloneMap (S : Finset V) (v x : V) : V := if x ∈ S then v else x

def cloneOn (G : SimpleGraph V) (S : Finset V) (v : V) : SimpleGraph V :=
  G.comap (cloneMap S v)

instance (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (v : V) :
    DecidableRel (cloneOn G S v).Adj := by
  unfold cloneOn
  infer_instance

@[simp] theorem cloneOn_empty (G : SimpleGraph V) (v : V) : cloneOn G ∅ v = G := by
  ext a b
  simp [cloneOn, cloneMap]

theorem cloneOn_outside (G : SimpleGraph V) (S : Finset V) (v : V)
    {a b : V} (ha : a ∉ S) (hb : b ∉ S) :
    (cloneOn G S v).Adj a b ↔ G.Adj a b := by
  simp [cloneOn, cloneMap, ha, hb]

theorem cloneOn_twins (G : SimpleGraph V) (S : Finset V) (v : V)
    (hv : v ∉ S) {u : V} (hu : u ∈ S) (x : V) :
    (cloneOn G S v).Adj u x ↔ (cloneOn G S v).Adj v x := by
  simp [cloneOn, cloneMap, hu, hv]

theorem cliqueFree_comap {G : SimpleGraph V} {k : ℕ} (h : G.CliqueFree k)
    (f : V → V) : (G.comap f).CliqueFree k := by
  classical
  intro s hs
  apply h (s.image f)
  have hinj : Set.InjOn f (s : Set V) := by
    intro a ha b hb he
    by_contra hn
    have hab := hs.isClique ha hb hn
    change G.Adj (f a) (f b) at hab
    rw [he] at hab
    exact G.irrefl hab
  refine ⟨?_, (Finset.card_image_of_injOn hinj).trans hs.card_eq⟩
  intro a ha b hb hab
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
  have hxy : x ≠ y := fun he => hab (congrArg f he)
  exact hs.isClique hx hy hxy

theorem cloneOn_cliqueFree {G : SimpleGraph V} {k : ℕ} (h : G.CliqueFree k)
    (S : Finset V) (v : V) : (cloneOn G S v).CliqueFree k :=
  cliqueFree_comap h _

theorem cloneOn_insert (G : SimpleGraph V) (S : Finset V) (v u : V)
    (hu : u ∉ S) (hv : v ∉ S) :
    cloneOn G (insert u S) v = (cloneOn G S v).replaceVertex v u := by
  ext a b
  by_cases ha : a = u
  · subst a
    by_cases hb : b = u
    · subst b
      simp [cloneOn, cloneMap, replaceVertex, hv]
    · simp [cloneOn, cloneMap, replaceVertex, hu, hv, hb]
  · by_cases hb : b = u
    · subst b
      simp [cloneOn, cloneMap, replaceVertex, hu, hv, ha]
    · simp [cloneOn, cloneMap, replaceVertex, ha, hb]

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.CloneBasics

-- BEGIN MODULE TMProof.CloneDegree

namespace TuranMatching.Clique.TMFresh
open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in
theorem edge_card_congr {H K : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel K.Adj]
    (he : H = K) : #H.edgeFinset = #K.edgeFinset := by
  have hh := congrArg (fun L : SimpleGraph V => L.edgeSet.ncard) he
  simpa only [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset] using hh

theorem cloneOn_degree_rep (S : Finset V) (v : V) (hv : v ∉ S)
    (hn : ∀ u ∈ S, ¬G.Adj v u) : (cloneOn G S v).degree v = G.degree v := by
  unfold SimpleGraph.degree
  congr 1
  ext x
  simp only [mem_neighborFinset]
  by_cases hx : x ∈ S
  · simp [cloneOn, cloneMap, hv, hx, hn x hx]
  · exact cloneOn_outside G S v hv hx

theorem cloneOn_degree_nonadj_le (S : Finset V) (v u : V) (hu : u ∉ S)
    (hn : ¬G.Adj u v) : (cloneOn G S v).degree u ≤ G.degree u := by
  apply Finset.card_le_card
  intro x hx
  simp only [mem_neighborFinset] at hx ⊢
  by_cases hxs : x ∈ S
  · simp [cloneOn, cloneMap, hu, hxs, hn] at hx
  · exact (cloneOn_outside G S v hu hxs).mp hx

theorem cloneOn_edges_le (S : Finset V) (v : V) (hv : v ∉ S)
    (hn : ∀ u ∈ S, ¬G.Adj v u) (hd : ∀ u ∈ S, G.degree u ≤ G.degree v) :
    #G.edgeFinset ≤ #(cloneOn G S v).edgeFinset := by
  induction S using Finset.induction_on with
  | empty =>
    rw [edge_card_congr (cloneOn_empty G v)]
  | @insert u S hu ih =>
    have hvS : v ∉ S := fun h => hv (Finset.mem_insert_of_mem h)
    have hnS : ∀ x ∈ S, ¬G.Adj v x := fun x hx => hn x (Finset.mem_insert_of_mem hx)
    have hdS : ∀ x ∈ S, G.degree x ≤ G.degree v := fun x hx => hd x (Finset.mem_insert_of_mem hx)
    have hfirst := ih hvS hnS hdS
    have hnvu : ¬G.Adj v u := hn u (Finset.mem_insert_self _ _)
    have hnuv : ¬G.Adj u v := fun h => hnvu h.symm
    have hdu := cloneOn_degree_nonadj_le G S v u hu hnuv
    have hdv := cloneOn_degree_rep G S v hvS hnS
    have hdold := hd u (Finset.mem_insert_self _ _)
    have hnot : ¬(cloneOn G S v).Adj v u := by
      rw [cloneOn_outside G S v hvS hu]
      exact hnvu
    have he := (cloneOn G S v).card_edgeFinset_replaceVertex_of_not_adj hnot
    have hbound : #G.edgeFinset ≤ #((cloneOn G S v).replaceVertex v u).edgeFinset := by omega
    rw [edge_card_congr (cloneOn_insert G S v u hu hvS)]
    exact hbound

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.CloneDegree

-- BEGIN MODULE TMProof.SubsetTwins

namespace TuranMatching.Clique.TMFresh
open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
def TwinnedOn (G : SimpleGraph V) (B : Finset V) : Prop :=
  ∀ a ∈ B, ∀ b ∈ B, ¬G.Adj a b → ∀ x, G.Adj a x ↔ G.Adj b x

theorem subset_twins (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset V) :
    ∃ f : V → V, (∀ x ∉ B, f x = x) ∧ (∀ x ∈ B, f x ∈ B) ∧
      #G.edgeFinset ≤ #(G.comap f).edgeFinset ∧ TwinnedOn (G.comap f) B := by
  classical
  induction B using Finset.strongInductionOn generalizing G
  rename_i B ih inst
  by_cases hB : B.Nonempty
  · obtain ⟨v, hv, hdeg⟩ := Finset.exists_max_image B (fun v => G.degree v) hB
    let T : Finset V := B.filter (G.Adj v)
    let S : Finset V := B.filter (fun x => x ≠ v ∧ ¬G.Adj v x)
    have hTB : T ⊆ B := Finset.filter_subset _ _
    have hSB : S ⊆ B := Finset.filter_subset _ _
    have hvT : v ∉ T := by simp [T]
    have hvS : v ∉ S := by simp [S]
    have hproper : T ⊂ B := Finset.ssubset_iff_subset_ne.mpr ⟨hTB, by
      intro he
      exact hvT (he.symm ▸ hv)⟩
    have hnS : ∀ u ∈ S, ¬G.Adj v u := by
      intro u hu
      exact (Finset.mem_filter.mp hu).2.2
    have hdS : ∀ u ∈ S, G.degree u ≤ G.degree v := fun u hu => hdeg u (hSB hu)
    let H := cloneOn G S v
    obtain ⟨f, hfix, hmap, hedge, htw⟩ := ih T hproper H
    let F : V → V := cloneMap S v ∘ f
    have hgraph : G.comap F = H.comap f := rfl
    have hTS (x : V) (hx : x ∈ T) : x ∉ S := by
      intro hs
      exact hnS x hs (Finset.mem_filter.mp hx).2
    have hcollapse (x : V) (hx : x ∈ B) (hxt : x ∉ T) : cloneMap S v x = v := by
      by_cases he : x = v
      · subst x
        simp [cloneMap]
      · have hn : ¬G.Adj v x := by
          intro ha
          exact hxt (Finset.mem_filter.mpr ⟨hx, ha⟩)
        have hs : x ∈ S := Finset.mem_filter.mpr ⟨hx, he, hn⟩
        simp [cloneMap, hs]
    refine ⟨F, ?_, ?_, ?_, ?_⟩
    · intro x hx
      have hxt : x ∉ T := fun ht => hx (hTB ht)
      have hxs : x ∉ S := fun hs => hx (hSB hs)
      simp [F, Function.comp_def, hfix x hxt, cloneMap, hxs]
    · intro x hx
      by_cases hxt : x ∈ T
      · have hf := hmap x hxt
        simpa [F, Function.comp_def, cloneMap, hTS _ hf] using hTB hf
      · have hf := hfix x hxt
        dsimp [F]
        rw [hf, hcollapse x hx hxt]
        exact hv
    · rw [edge_card_congr hgraph]
      exact (cloneOn_edges_le G S v hvS hnS hdS).trans hedge
    · intro a ha b hb hab x
      rw [hgraph] at hab ⊢
      by_cases hat : a ∈ T
      · by_cases hbt : b ∈ T
        · exact htw a hat b hbt hab x
        · have hfb := hfix b hbt
          have hfa := hmap a hat
          have hna := hTS _ hfa
          have hbv := hcollapse b hb hbt
          have hac : G.Adj v (f a) := (Finset.mem_filter.mp hfa).2
          have hh : (H.comap f).Adj a b := by
            change G.Adj (cloneMap S v (f a)) (cloneMap S v (f b))
            rw [hfb, hbv]
            simpa [cloneMap, hna] using hac.symm
          exact False.elim (hab hh)
      · by_cases hbt : b ∈ T
        · have hfa := hfix a hat
          have hfb := hmap b hbt
          have hnb := hTS _ hfb
          have hav := hcollapse a ha hat
          have hbc : G.Adj v (f b) := (Finset.mem_filter.mp hfb).2
          have hh : (H.comap f).Adj a b := by
            change G.Adj (cloneMap S v (f a)) (cloneMap S v (f b))
            rw [hfa, hav]
            simpa [cloneMap, hnb] using hbc
          exact False.elim (hab hh)
        · have hfa := hfix a hat
          have hfb := hfix b hbt
          change G.Adj (cloneMap S v (f a)) (cloneMap S v (f x)) ↔
            G.Adj (cloneMap S v (f b)) (cloneMap S v (f x))
          rw [hfa, hfb, hcollapse a ha hat, hcollapse b hb hbt]
  · have he : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
    subst B
    refine ⟨id, by simp, by simp, ?_, ?_⟩
    · have he : G.comap id = G := by ext a b; rfl
      rw [edge_card_congr he]
    · simp [TwinnedOn]

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.SubsetTwins

-- BEGIN MODULE TMProof.TwinClasses

namespace TuranMatching.Clique.TMFresh
open Finset SimpleGraph

variable {V : Type*} [DecidableEq V]

def twinClass (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset V) (v : V) : Finset V :=
  B.filter (fun x => ¬G.Adj v x)

def twinClasses (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset V) : Finset (Finset V) :=
  B.image (twinClass G B)

variable {G : SimpleGraph V} [DecidableRel G.Adj] {B : Finset V}

omit [DecidableEq V] in
theorem twinClass_self {v : V} (hv : v ∈ B) : v ∈ twinClass G B v := by
  simp [twinClass, hv]

omit [DecidableEq V] in
theorem twinClass_eq (ht : TwinnedOn G B) {v u : V} (hv : v ∈ B) (hu : u ∈ B)
    (hn : ¬G.Adj v u) : twinClass G B v = twinClass G B u := by
  ext x
  simp only [twinClass, Finset.mem_filter]
  exact and_congr_right fun _ => not_congr (ht v hv u hu hn x)

omit [DecidableEq V] in
theorem twinClass_eq_of_mem (ht : TwinnedOn G B) {v u : V} (hv : v ∈ B)
    (hu : u ∈ twinClass G B v) : twinClass G B v = twinClass G B u := by
  obtain ⟨huB, hn⟩ := Finset.mem_filter.mp hu
  exact twinClass_eq ht hv huB hn

theorem twinClasses_nonempty {C : Finset V} (hC : C ∈ twinClasses G B) : C.Nonempty := by
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hC
  exact ⟨v, twinClass_self hv⟩

theorem twinClasses_subset {C : Finset V} (hC : C ∈ twinClasses G B) : C ⊆ B := by
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hC
  exact Finset.filter_subset _ _

theorem twinClasses_cover (v : V) : v ∈ B ↔ ∃ C ∈ twinClasses G B, v ∈ C := by
  constructor
  · intro hv
    exact ⟨twinClass G B v, Finset.mem_image.mpr ⟨v, hv, rfl⟩, twinClass_self hv⟩
  · rintro ⟨C, hC, hv⟩
    exact twinClasses_subset hC hv

theorem twinClasses_identify (ht : TwinnedOn G B) {C : Finset V}
    (hC : C ∈ twinClasses G B) {v : V} (hv : v ∈ C) : C = twinClass G B v := by
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hC
  exact twinClass_eq_of_mem ht hu hv

theorem twinClasses_disjoint (ht : TwinnedOn G B) :
    Set.PairwiseDisjoint (twinClasses G B : Set (Finset V)) id := by
  intro C hC D hD hne
  apply Finset.disjoint_left.mpr
  intro v hv hv'
  exact hne ((twinClasses_identify ht hC hv).trans (twinClasses_identify ht hD hv').symm)

theorem twinClasses_twins (ht : TwinnedOn G B) {C : Finset V}
    (hC : C ∈ twinClasses G B) {a b : V} (ha : a ∈ C) (hb : b ∈ C) :
    ∀ x, G.Adj a x ↔ G.Adj b x := by
  have he := twinClasses_identify ht hC ha
  rw [he] at hb
  obtain ⟨hbB, hn⟩ := Finset.mem_filter.mp hb
  exact ht a (twinClasses_subset hC ha) b hbB hn

theorem twinClasses_cross (ht : TwinnedOn G B) {C D : Finset V}
    (hC : C ∈ twinClasses G B) (hD : D ∈ twinClasses G B) (hne : C ≠ D)
    {a b : V} (ha : a ∈ C) (hb : b ∈ D) : G.Adj a b := by
  by_contra hn
  have he := twinClass_eq ht (twinClasses_subset hC ha) (twinClasses_subset hD hb) hn
  exact hne ((twinClasses_identify ht hC ha).trans (he.trans (twinClasses_identify ht hD hb).symm))

theorem twinClasses_card (ht : TwinnedOn G B) {k : ℕ} (hk : G.CliqueFree (k + 1)) :
    #(twinClasses G B) ≤ k := by
  classical
  let R := twinClasses G B
  let rep : R → V := fun C => (twinClasses_nonempty C.property).choose
  have hrep (C : R) : rep C ∈ (C : Finset V) := (twinClasses_nonempty C.property).choose_spec
  have hinj : Function.Injective rep := by
    intro C D he
    apply Subtype.ext
    exact (twinClasses_identify ht C.property (hrep C)).trans
      (by rw [he]; exact (twinClasses_identify ht D.property (hrep D)).symm)
  let K : Finset V := Finset.univ.image rep
  have hK : G.IsClique K := by
    intro a ha b hb hab
    obtain ⟨C, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨D, _, rfl⟩ := Finset.mem_image.mp hb
    apply twinClasses_cross ht C.property D.property
    · intro he
      have he' : C = D := Subtype.ext he
      exact hab (congrArg rep he')
    · exact hrep C
    · exact hrep D
  have hcard : #K = #R := by
    dsimp [K]
    rw [Finset.card_image_of_injective _ hinj]
    simp
  dsimp only [R] at hcard
  by_contra hn
  have hle : k + 1 ≤ #K := by omega
  exact hk.mono hle K ⟨hK, rfl⟩

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.TwinClasses

-- BEGIN MODULE TMProof.TwinPartition

namespace TuranMatching.Clique.TMFresh
open Finset SimpleGraph

variable {V : Type*} [DecidableEq V]

structure TwinPartition (G : SimpleGraph V) (B : Finset V)
    (classes : Finset (Finset V)) (k : ℕ) : Prop where
  nonempty : ∀ C ∈ classes, C.Nonempty
  subset : ∀ C ∈ classes, C ⊆ B
  pairwise : Set.PairwiseDisjoint (classes : Set (Finset V)) id
  cover : ∀ v, v ∈ B ↔ ∃ C ∈ classes, v ∈ C
  twins : ∀ C ∈ classes, ∀ a ∈ C, ∀ b ∈ C, ∀ x, G.Adj a x ↔ G.Adj b x
  cross : ∀ C ∈ classes, ∀ D ∈ classes, C ≠ D → ∀ a ∈ C, ∀ b ∈ D, G.Adj a b
  card : classes.card ≤ k

theorem twinPartition_of_twinned {G : SimpleGraph V} [DecidableRel G.Adj] {B : Finset V}
    (ht : TwinnedOn G B) {k : ℕ} (hk : G.CliqueFree (k + 1)) :
    TwinPartition G B (twinClasses G B) k := by
  exact ⟨fun _ h => twinClasses_nonempty h, fun _ h => twinClasses_subset h,
    twinClasses_disjoint ht, twinClasses_cover,
    fun _ h _ ha _ hb => twinClasses_twins ht h ha hb,
    fun _ hC _ hD hne _ ha _ hb => twinClasses_cross ht hC hD hne ha hb,
    twinClasses_card ht hk⟩

variable [Fintype V]

theorem normalize_certificate (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset V) (blocks : Finset (Finset V)) (k s : ℕ)
    (hc : OddCertificate G B blocks s) (hk : G.CliqueFree (k + 1)) :
    ∃ H : SimpleGraph V, ∃ _ : DecidableRel H.Adj, ∃ classes : Finset (Finset V),
      OddCertificate H B blocks s ∧ H.CliqueFree (k + 1) ∧
      #G.edgeFinset ≤ #H.edgeFinset ∧ TwinPartition H B classes k := by
  classical
  obtain ⟨f, hfix, _, he, ht⟩ := subset_twins G B
  refine ⟨G.comap f, inferInstance, twinClasses (G.comap f) B, ?_,
    cliqueFree_comap hk f, he, twinPartition_of_twinned ht (cliqueFree_comap hk f)⟩
  apply hc.of_outside_eq
  intro u hu v hv
  simp [hfix u hu, hfix v hv]

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.TwinPartition

-- BEGIN MODULE TMProof.OptimalTwins

namespace TuranMatching.Clique.TMFresh
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem OptimalCertificate.transfer {G H : SimpleGraph V} {B : Finset V}
    {blocks bs : Finset (Finset V)} {k s : ℕ}
    (ho : OptimalCertificate G B blocks k s) (hc : OddCertificate H B bs s)
    (hk : H.CliqueFree (k+1)) (he : G.edgeSet.ncard ≤ H.edgeSet.ncard)
    (hs : blockSquare blocks ≤ blockSquare bs) : OptimalCertificate H B bs k s := by
  have heq : H.edgeSet.ncard = G.edgeSet.ncard := le_antisymm (ho.edge_max H bs hc hk) he
  refine ⟨hc,hk,?_,?_⟩
  · intro J cs hj hjk
    exact (ho.edge_max J cs hj hjk).trans he
  · intro J cs hj hjk heJ
    exact (ho.square_max J cs hj hjk (heJ.trans heq)).trans hs

theorem OptimalCertificate.normalize {G : SimpleGraph V} {B : Finset V}
    {blocks : Finset (Finset V)} {k s : ℕ}
    (ho : OptimalCertificate G B blocks k s) :
    ∃ H : SimpleGraph V, ∃ classes, OptimalCertificate H B blocks k s ∧
      TwinPartition H B classes k := by
  classical
  obtain ⟨H,_,classes,hc,hk,he,ht⟩ := normalize_certificate G B blocks k s
    ho.certificate ho.cliqueFree
  have he' : G.edgeSet.ncard ≤ H.edgeSet.ncard := by
    simpa only [← coe_edgeFinset, Set.ncard_coe_finset] using he
  exact ⟨H,classes,ho.transfer hc hk he' le_rfl,ht⟩

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.OptimalTwins

-- BEGIN MODULE TMProof.ClassSwitch

namespace TuranMatching.Clique.TMFresh
open Finset SimpleGraph

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
theorem TwinPartition.not_adj_same {G : SimpleGraph V} {B : Finset V}
    {classes : Finset (Finset V)} {k : ℕ} (ht : TwinPartition G B classes k)
    {C : Finset V} (hC : C ∈ classes) {a b : V} (ha : a ∈ C) (hb : b ∈ C) :
    ¬G.Adj a b := by
  intro h
  exact G.irrefl ((ht.twins C hC a ha b hb b).mp h)

omit [DecidableEq V] in
theorem TwinPartition.adj_of_not_mem {G : SimpleGraph V} {B : Finset V}
    {classes : Finset (Finset V)} {k : ℕ} (ht : TwinPartition G B classes k)
    {C : Finset V} (hC : C ∈ classes) {a b : V} (ha : a ∈ C)
    (hb : b ∈ B) (hbC : b ∉ C) : G.Adj a b := by
  obtain ⟨D, hD, hbD⟩ := (ht.cover b).mp hb
  apply ht.cross C hC D hD _ a ha b hbD
  intro he
  exact hbC (he.symm ▸ hbD)

def classSwitch (I J : Finset V) (i j x : V) : V :=
  if x ∈ I then j else if x ∈ J then i else x

theorem classSwitch_mem {G : SimpleGraph V} {B : Finset V}
    {classes : Finset (Finset V)} {k : ℕ} (ht : TwinPartition G B classes k)
    {I J : Finset V} (hI : I ∈ classes) (hJ : J ∈ classes)
    {i j x : V} (hi : i ∈ I) (hj : j ∈ J) (hx : x ∈ B) :
    classSwitch I J i j x ∈ B := by
  unfold classSwitch
  split_ifs
  · exact ht.subset J hJ hj
  · exact ht.subset I hI hi
  · exact hx

theorem classSwitch_adj {G : SimpleGraph V} {B : Finset V}
    {classes : Finset (Finset V)} {k : ℕ} (ht : TwinPartition G B classes k)
    {I J : Finset V} (hI : I ∈ classes) (hJ : J ∈ classes) (hne : I ≠ J)
    {i j a b : V} (hi : i ∈ I) (hj : j ∈ J) (ha : a ∈ B) (hb : b ∈ B) :
    G.Adj (classSwitch I J i j a) (classSwitch I J i j b) ↔ G.Adj a b := by
  have hij : G.Adj i j := ht.cross I hI J hJ hne i hi j hj
  by_cases haI : a ∈ I
  · by_cases hbI : b ∈ I
    · simp [classSwitch, haI, hbI, ht.not_adj_same hI haI hbI]
    · by_cases hbJ : b ∈ J
      · have hab := ht.cross I hI J hJ hne a haI b hbJ
        simp [classSwitch, haI, hbI, hbJ, hij.symm, hab]
      · have hab := ht.adj_of_not_mem hI haI hb hbI
        have hjb := ht.adj_of_not_mem hJ hj hb hbJ
        simp [classSwitch, haI, hbI, hbJ, hab, hjb]
  · by_cases haJ : a ∈ J
    · by_cases hbI : b ∈ I
      · have hab := ht.cross J hJ I hI hne.symm a haJ b hbI
        simp [classSwitch, haI, haJ, hbI, hij, hab]
      · by_cases hbJ : b ∈ J
        · simp [classSwitch, haI, haJ, hbI, hbJ, ht.not_adj_same hJ haJ hbJ]
        · have hab := ht.adj_of_not_mem hJ haJ hb hbJ
          have hib := ht.adj_of_not_mem hI hi hb hbI
          simp [classSwitch, haI, haJ, hbI, hbJ, hab, hib]
    · by_cases hbI : b ∈ I
      · have hab := (ht.adj_of_not_mem hI hbI ha haI).symm
        have haj := (ht.adj_of_not_mem hJ hj ha haJ).symm
        simp [classSwitch, haI, haJ, hbI, hab, haj]
      · by_cases hbJ : b ∈ J
        · have hab := (ht.adj_of_not_mem hJ hbJ ha haJ).symm
          have hai := (ht.adj_of_not_mem hI hi ha haI).symm
          simp [classSwitch, haI, haJ, hbI, hbJ, hab, hai]
        · simp [classSwitch, haI, haJ, hbI, hbJ]

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.ClassSwitch

-- BEGIN MODULE TMProof.BlockSwitch

namespace TuranMatching.Clique.TMFresh
open Finset SimpleGraph

variable {V : Type*} [DecidableEq V]

def switchCut (G : SimpleGraph V) (C : Finset V) (f : V → V) : SimpleGraph V where
  Adj a b := if a ∈ C then (if b ∈ C then G.Adj a b else G.Adj a (f b))
    else (if b ∈ C then G.Adj (f a) b else G.Adj a b)
  symm.symm a b := by
    by_cases ha : a ∈ C <;> by_cases hb : b ∈ C <;> simp [ha, hb, adj_comm]
  loopless.irrefl a := by by_cases ha : a ∈ C <;> simp [ha]

instance (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset V) (f : V → V) :
    DecidableRel (switchCut G C f).Adj := by
  unfold switchCut
  infer_instance

theorem switchCut_cliqueFree {G : SimpleGraph V} {C B : Finset V} {f : V → V}
    {k : ℕ} (hk : G.CliqueFree k)
    (hfix : ∀ x ∉ B, f x = x)
    (hpres : ∀ a ∈ B, ∀ b ∈ B, G.Adj a b → G.Adj (f a) (f b))
    (hsep : ∀ a ∈ C, ∀ b, b ∉ C → b ∉ B → ¬G.Adj a b) :
    (switchCut G C f).CliqueFree k := by
  classical
  intro K hK
  by_cases hex : ∃ c ∈ K, c ∈ C
  · obtain ⟨c, hcK, hcC⟩ := hex
    have hKB : ∀ a ∈ K, a ∉ C → a ∈ B := by
      intro a ha haC
      by_contra haB
      have hne : c ≠ a := by intro he; subst a; exact haC hcC
      have hadj := hK.isClique hcK ha hne
      have hadj' : G.Adj c (f a) := by simpa [switchCut, hcC, haC] using hadj
      rw [hfix a haB] at hadj'
      exact hsep c hcC a haC haB hadj'
    let g : V → V := fun a => if a ∈ C then a else f a
    have hmap : ∀ a ∈ K, ∀ b ∈ K, a ≠ b → G.Adj (g a) (g b) := by
      intro a ha b hb hab
      have hadj := hK.isClique ha hb hab
      by_cases haC : a ∈ C
      · by_cases hbC : b ∈ C
        · simpa [g, switchCut, haC, hbC] using hadj
        · simpa [g, switchCut, haC, hbC] using hadj
      · by_cases hbC : b ∈ C
        · simpa [g, switchCut, haC, hbC] using hadj
        · have hab' : G.Adj a b := by simpa [switchCut, haC, hbC] using hadj
          simpa [g, haC, hbC] using hpres a (hKB a ha haC) b (hKB b hb hbC) hab'
    have hinj : Set.InjOn g (K : Set V) := by
      intro a ha b hb he
      by_contra hn
      have hadj := hmap a ha b hb hn
      rw [he] at hadj
      exact G.irrefl hadj
    apply hk (K.image g)
    refine ⟨?_, (Finset.card_image_of_injOn hinj).trans hK.card_eq⟩
    intro a ha b hb hab
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
    exact hmap x hx y hy (fun he => hab (congrArg g he))
  · have hout : ∀ a ∈ K, a ∉ C := by
      intro a ha haC
      exact hex ⟨a, ha, haC⟩
    apply hk K
    refine ⟨?_, hK.card_eq⟩
    intro a ha b hb hab
    simpa [switchCut, hout a ha, hout b hb] using hK.isClique ha hb hab

theorem block_class_switch_cliqueFree {G : SimpleGraph V} {B C : Finset V}
    {classes : Finset (Finset V)} {k : ℕ} (ht : TwinPartition G B classes k)
    (hk : G.CliqueFree (k + 1)) {I J : Finset V}
    (hI : I ∈ classes) (hJ : J ∈ classes) (hne : I ≠ J)
    {i j : V} (hi : i ∈ I) (hj : j ∈ J)
    (hsep : ∀ a ∈ C, ∀ b, b ∉ C → b ∉ B → ¬G.Adj a b) :
    (switchCut G C (classSwitch I J i j)).CliqueFree (k + 1) := by
  apply switchCut_cliqueFree hk _ _ hsep
  · intro x hx
    have hxI : x ∉ I := fun h => hx (ht.subset I hI h)
    have hxJ : x ∉ J := fun h => hx (ht.subset J hJ h)
    simp [classSwitch, hxI, hxJ]
  · intro a ha b hb hab
    exact (classSwitch_adj ht hI hJ hne hi hj ha hb).mpr hab

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.BlockSwitch

-- BEGIN MODULE TMProof.EdgeCut

namespace TuranMatching.Clique.TMFresh
open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
def adjWeight (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V) : ℤ :=
  if G.Adj a b then 1 else 0

omit [DecidableEq V] in
theorem sum_adjWeight (G : SimpleGraph V) [DecidableRel G.Adj] (a : V) :
    ∑ b, adjWeight G a b = (G.degree a : ℤ) := by
  simp [adjWeight, SimpleGraph.degree, neighborFinset_eq_filter, Finset.sum_boole]

theorem sum_cross_symmetric (C : Finset V) (d : V → V → ℤ)
    (hsym : ∀ a b, d a b = d b a)
    (hzero : ∀ a b, (a ∈ C ↔ b ∈ C) → d a b = 0) :
    ∑ a, ∑ b, d a b = 2 * ∑ a ∈ C, ∑ b, d a b := by
  have hin (a : V) (ha : a ∈ C) : ∑ b, d a b = ∑ b ∈ Cᶜ, d a b := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro b _ hb
    have hbC : b ∈ C := by simpa using hb
    exact hzero a b (iff_of_true ha hbC)
  have hout (a : V) (ha : a ∈ Cᶜ) : ∑ b, d a b = ∑ b ∈ C, d a b := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro b _ hb
    have haC : a ∉ C := Finset.mem_compl.mp ha
    exact hzero a b (iff_of_false haC hb)
  have he : (∑ a ∈ Cᶜ, ∑ b, d a b) = ∑ a ∈ C, ∑ b, d a b := by
    calc
      _ = ∑ a ∈ Cᶜ, ∑ b ∈ C, d a b := Finset.sum_congr rfl hout
      _ = ∑ b ∈ C, ∑ a ∈ Cᶜ, d a b := Finset.sum_comm
      _ = ∑ b ∈ C, ∑ a ∈ Cᶜ, d b a := by
        apply Finset.sum_congr rfl
        intro b _
        exact Finset.sum_congr rfl (fun a _ => hsym a b)
      _ = ∑ b ∈ C, ∑ a, d b a := Finset.sum_congr rfl (fun b hb => (hin b hb).symm)
  have hall := Finset.sum_add_sum_compl C (fun a => ∑ b, d a b)
  rw [he] at hall
  linarith

theorem edges_le_of_cut_degrees (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (C : Finset V)
    (hsame : ∀ a b, (a ∈ C ↔ b ∈ C) → (H.Adj a b ↔ G.Adj a b))
    (hdeg : ∀ a ∈ C, G.degree a ≤ H.degree a) :
    #G.edgeFinset ≤ #H.edgeFinset := by
  let d : V → V → ℤ := fun a b => adjWeight H a b - adjWeight G a b
  have hsum := sum_cross_symmetric C d (by
    intro a b
    simp [d, adjWeight, adj_comm]) (by
    intro a b he
    simp [d, adjWeight, hsame a b he])
  have hd (a : V) : ∑ b, d a b = (H.degree a : ℤ) - G.degree a := by
    simp only [d, Finset.sum_sub_distrib, sum_adjWeight]
  simp only [hd] at hsum
  have hnon : 0 ≤ ∑ a ∈ C, ((H.degree a : ℤ) - G.degree a) := by
    apply Finset.sum_nonneg
    intro a ha
    exact sub_nonneg.mpr (by exact_mod_cast hdeg a ha)
  have hG : (∑ a, (G.degree a : ℤ)) = 2 * (#G.edgeFinset : ℤ) := by
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  have hH : (∑ a, (H.degree a : ℤ)) = 2 * (#H.edgeFinset : ℤ) := by
    exact_mod_cast H.sum_degrees_eq_twice_card_edges
  rw [Finset.sum_sub_distrib, hG, hH] at hsum
  have hle : (#G.edgeFinset : ℤ) ≤ #H.edgeFinset := by linarith
  exact_mod_cast hle

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.EdgeCut

-- BEGIN MODULE TMProof.BlockSwitchCount

namespace TuranMatching.Clique.TMFresh
open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

 theorem block_class_switch_degree {G : SimpleGraph V} [DecidableRel G.Adj]
    {B C : Finset V} {classes : Finset (Finset V)} {k : ℕ}
    (ht : TwinPartition G B classes k) (hCB : Disjoint C B)
    {I J : Finset V} (hI : I ∈ classes) (hJ : J ∈ classes) (hne : I ≠ J)
    {i j u : V} (hi : i ∈ I) (hj : j ∈ J) (hu : u ∈ C)
    (hall : ∀ x ∈ I, G.Adj u x) :
    ((switchCut G C (classSwitch I J i j)).degree u : ℤ) - G.degree u =
      if G.Adj u j then 0 else (J.card : ℤ) - I.card := by
  let H := switchCut G C (classSwitch I J i j)
  have hdis : Disjoint I J := ht.pairwise hI hJ hne
  have hIC {x : V} (hx : x ∈ I) : x ∉ C := by
    intro hc
    exact Finset.disjoint_left.mp hCB hc (ht.subset I hI hx)
  have hJC {x : V} (hx : x ∈ J) : x ∉ C := by
    intro hc
    exact Finset.disjoint_left.mp hCB hc (ht.subset J hJ hx)
  have huni {x : V} (hx : x ∈ J) : G.Adj u x ↔ G.Adj u j := by
    simpa only [adj_comm] using ht.twins J hJ x hx j hj u
  by_cases haj : G.Adj u j
  · rw [if_pos haj]
    have hp (x : V) : adjWeight H u x = adjWeight G u x := by
      by_cases hxI : x ∈ I
      · simp [H, adjWeight, switchCut, classSwitch, hu, hxI, hIC hxI, hall x hxI, haj]
      · by_cases hxJ : x ∈ J
        · have hux := (huni hxJ).mpr haj
          simp [H, adjWeight, switchCut, classSwitch, hu, hxI, hxJ, hJC hxJ, hall i hi, hux]
        · simp [H, adjWeight, switchCut, classSwitch, hu, hxI, hxJ]
    have he := Finset.sum_congr (s₁ := Finset.univ) rfl (fun x _ => hp x)
    rw [sum_adjWeight, sum_adjWeight] at he
    exact sub_eq_zero.mpr he
  · rw [if_neg haj]
    have hp (x : V) : adjWeight H u x - adjWeight G u x =
        (if x ∈ J then (1 : ℤ) else 0) - (if x ∈ I then 1 else 0) := by
      by_cases hxI : x ∈ I
      · have hxJ : x ∉ J := fun h => Finset.disjoint_left.mp hdis hxI h
        simp [H, adjWeight, switchCut, classSwitch, hu, hxI, hxJ, hIC hxI, hall x hxI, haj]
      · by_cases hxJ : x ∈ J
        · have hux : ¬G.Adj u x := fun h => haj ((huni hxJ).mp h)
          simp [H, adjWeight, switchCut, classSwitch, hu, hxI, hxJ, hJC hxJ, hall i hi, hux]
        · simp [H, adjWeight, switchCut, classSwitch, hu, hxI, hxJ]
    have he := Finset.sum_congr (s₁ := Finset.univ) rfl (fun x _ => hp x)
    simpa only [Finset.sum_sub_distrib, sum_adjWeight, Finset.sum_boole, Finset.filter_mem_eq_inter,
      Finset.univ_inter] using he

theorem block_class_switch_edges {G : SimpleGraph V} [DecidableRel G.Adj]
    {B C : Finset V} {classes : Finset (Finset V)} {k : ℕ}
    (ht : TwinPartition G B classes k) (hCB : Disjoint C B)
    {I J : Finset V} (hI : I ∈ classes) (hJ : J ∈ classes) (hne : I ≠ J)
    {i j : V} (hi : i ∈ I) (hj : j ∈ J) (hcard : I.card ≤ J.card)
    (hall : ∀ u ∈ C, ∀ x ∈ I, G.Adj u x) :
    #G.edgeFinset ≤ #(switchCut G C (classSwitch I J i j)).edgeFinset := by
  apply edges_le_of_cut_degrees G _ C
  · intro a b he
    by_cases ha : a ∈ C
    · have hb := he.mp ha
      simp [switchCut, ha, hb]
    · have hb : b ∉ C := fun hb => ha (he.mpr hb)
      simp [switchCut, ha, hb]
  · intro u hu
    have he := block_class_switch_degree ht hCB hI hJ hne hi hj hu (hall u hu)
    have hz : (0 : ℤ) ≤ ((switchCut G C (classSwitch I J i j)).degree u : ℤ) - G.degree u := by
      rw [he]
      split_ifs
      · rfl
      · exact sub_nonneg.mpr (by exact_mod_cast hcard)
    exact_mod_cast sub_nonneg.mp hz

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.BlockSwitchCount

-- BEGIN MODULE TMProof.BlockSwitchCertificate

namespace TuranMatching.Clique.TMFresh
open Finset SimpleGraph

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
theorem OddCertificate.block_separation {G : SimpleGraph V} {B C : Finset V}
    {blocks : Finset (Finset V)} {s : ℕ} (hc : OddCertificate G B blocks s)
    (hC : C ∈ blocks) : ∀ a ∈ C, ∀ b, b ∉ C → b ∉ B → ¬G.Adj a b := by
  intro a ha b hbC hbB
  obtain ⟨D, hD, hbD⟩ := (hc.cover b).mp hbB
  apply hc.edges C hC D hD _ a ha b hbD
  intro he
  exact hbC (he.symm ▸ hbD)

theorem block_switch_certificate {G : SimpleGraph V} {B C : Finset V}
    {blocks classes : Finset (Finset V)} {s k : ℕ} (hc : OddCertificate G B blocks s)
    (ht : TwinPartition G B classes k) {I J : Finset V}
    (hI : I ∈ classes) (hJ : J ∈ classes) (i j : V) :
    OddCertificate (switchCut G C (classSwitch I J i j)) B blocks s := by
  apply hc.of_outside_eq
  intro a ha b hb
  have haI : a ∉ I := fun h => ha (ht.subset I hI h)
  have haJ : a ∉ J := fun h => ha (ht.subset J hJ h)
  have hbI : b ∉ I := fun h => hb (ht.subset I hI h)
  have hbJ : b ∉ J := fun h => hb (ht.subset J hJ h)
  simp [switchCut, classSwitch, haI, haJ, hbI, hbJ]

theorem classSwitch_twins {G : SimpleGraph V} {B : Finset V}
    {classes : Finset (Finset V)} {k : ℕ} (ht : TwinPartition G B classes k)
    {I J D : Finset V} (hI : I ∈ classes) (hJ : J ∈ classes)
    (hD : D ∈ classes) (i j : V) {a b : V} (ha : a ∈ D) (hb : b ∈ D) (x : V) :
    G.Adj (classSwitch I J i j a) x ↔ G.Adj (classSwitch I J i j b) x := by
  by_cases hDI : D = I
  · subst D
    simp [classSwitch, ha, hb]
  · have haI : a ∉ I := fun h => Finset.disjoint_left.mp (ht.pairwise hD hI hDI) ha h
    have hbI : b ∉ I := fun h => Finset.disjoint_left.mp (ht.pairwise hD hI hDI) hb h
    by_cases hDJ : D = J
    · subst D
      simp [classSwitch, haI, hbI, ha, hb]
    · have haJ : a ∉ J := fun h => Finset.disjoint_left.mp (ht.pairwise hD hJ hDJ) ha h
      have hbJ : b ∉ J := fun h => Finset.disjoint_left.mp (ht.pairwise hD hJ hDJ) hb h
      simpa [classSwitch, haI, hbI, haJ, hbJ] using ht.twins D hD a ha b hb x

theorem block_switch_partition {G : SimpleGraph V} {B C : Finset V}
    {classes : Finset (Finset V)} {k : ℕ} (ht : TwinPartition G B classes k)
    (hCB : Disjoint C B) {I J : Finset V} (hI : I ∈ classes) (hJ : J ∈ classes)
    (i j : V) :
    TwinPartition (switchCut G C (classSwitch I J i j)) B classes k := by
  have hout {D : Finset V} (hD : D ∈ classes) {a : V} (ha : a ∈ D) : a ∉ C := by
    intro h
    exact Finset.disjoint_left.mp hCB h (ht.subset D hD ha)
  refine ⟨ht.nonempty, ht.subset, ht.pairwise, ht.cover, ?_, ?_, ht.card⟩
  · intro D hD a ha b hb x
    by_cases hx : x ∈ C
    · simpa [switchCut, hout hD ha, hout hD hb, hx] using
        classSwitch_twins ht hI hJ hD i j ha hb x
    · simpa [switchCut, hout hD ha, hout hD hb, hx] using ht.twins D hD a ha b hb x
  · intro D hD E hE hde a ha b hb
    simpa [switchCut, hout hD ha, hout hE hb] using ht.cross D hD E hE hde a ha b hb

theorem block_switch_missing {G : SimpleGraph V} {B C : Finset V}
    {classes : Finset (Finset V)} {k : ℕ} (ht : TwinPartition G B classes k)
    (hCB : Disjoint C B) {I J : Finset V} (hI : I ∈ classes)
    (i j u : V) (hu : u ∈ C) (hn : ¬G.Adj u j) :
    ∀ x ∈ I, ¬(switchCut G C (classSwitch I J i j)).Adj u x := by
  intro x hx
  have hxC : x ∉ C := fun h => Finset.disjoint_left.mp hCB h (ht.subset I hI hx)
  simpa [switchCut, classSwitch, hu, hx, hxC] using hn

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.BlockSwitchCertificate

-- BEGIN MODULE TMProof.MissingClass

namespace TuranMatching.Clique.TMFresh
open Finset SimpleGraph

variable {V : Type*} [DecidableEq V]

theorem TwinPartition.clique_representatives {G : SimpleGraph V} {B : Finset V}
    {classes : Finset (Finset V)} {k : ℕ} (ht : TwinPartition G B classes k) :
    ∃ K : Finset V, K ⊆ B ∧ G.IsClique K ∧ K.card = classes.card := by
  classical
  let rep : classes → V := fun C => (ht.nonempty C C.property).choose
  have hrep (C : classes) : rep C ∈ (C : Finset V) := (ht.nonempty C C.property).choose_spec
  have hinj : Function.Injective rep := by
    intro C D he
    apply Subtype.ext
    by_contra hn
    have hdis := ht.pairwise C.property D.property hn
    exact Finset.disjoint_left.mp hdis (hrep C) (he.symm ▸ hrep D)
  let K : Finset V := Finset.univ.image rep
  refine ⟨K, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨C, _, rfl⟩ := Finset.mem_image.mp hx
    exact ht.subset C C.property (hrep C)
  · intro a ha b hb hab
    obtain ⟨C, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨D, _, rfl⟩ := Finset.mem_image.mp hb
    apply ht.cross C C.property D D.property _ _ (hrep C) _ (hrep D)
    intro he
    exact hab (congrArg rep (Subtype.ext he))
  · dsimp [K]
    rw [Finset.card_image_of_injective _ hinj]
    simp

theorem TwinPartition.missing_class {G : SimpleGraph V} {B : Finset V}
    {classes : Finset (Finset V)} {k : ℕ} (ht : TwinPartition G B classes k)
    (hk : G.CliqueFree (k + 1)) (hcard : classes.card = k)
    {u : V} (hu : u ∉ B) : ∃ J ∈ classes, ∀ x ∈ J, ¬G.Adj u x := by
  classical
  by_contra hn
  have hall (x : V) (hx : x ∈ B) : G.Adj u x := by
    obtain ⟨C, hC, hxC⟩ := (ht.cover x).mp hx
    have hex : ∃ y ∈ C, G.Adj u y := by
      by_contra he
      apply hn
      refine ⟨C, hC, ?_⟩
      intro y hy hadj
      exact he ⟨y, hy, hadj⟩
    obtain ⟨y, hy, hadj⟩ := hex
    exact ((ht.twins C hC y hy x hxC u).mp hadj.symm).symm
  obtain ⟨K, hKB, hK, hsize⟩ := ht.clique_representatives
  have huK : u ∉ K := fun h => hu (hKB h)
  apply hk (insert u K)
  refine ⟨?_, ?_⟩
  · rw [Finset.coe_insert]
    exact hK.insert (fun x hx _ => hall x (hKB hx))
  · rw [Finset.card_insert_of_notMem huK, hsize, hcard]

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.MissingClass

-- BEGIN MODULE TMProof.RepairMissing

namespace TuranMatching.Clique.TMFresh
open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem repair_one_block (G : SimpleGraph V) [DecidableRel G.Adj]
    {B C : Finset V} {blocks classes : Finset (Finset V)} {s k : ℕ}
    (hc : OddCertificate G B blocks s) (hC : C ∈ blocks)
    (ht : TwinPartition G B classes k) (hk : G.CliqueFree (k + 1))
    (hcard : classes.card = k) {I : Finset V} (hI : I ∈ classes)
    (hmin : ∀ J ∈ classes, I.card ≤ J.card) :
    ∃ H : SimpleGraph V, ∃ _ : DecidableRel H.Adj,
      OddCertificate H B blocks s ∧ TwinPartition H B classes k ∧ H.CliqueFree (k + 1) ∧
      #G.edgeFinset ≤ #H.edgeFinset ∧ (∃ u ∈ C, ∀ x ∈ I, ¬H.Adj u x) ∧
      (∀ a ∉ C, ∀ b ∉ C, H.Adj a b ↔ G.Adj a b) := by
  classical
  by_cases hex : ∃ u ∈ C, ∀ x ∈ I, ¬G.Adj u x
  · exact ⟨G, inferInstance, hc, ht, hk, le_rfl, hex, fun _ _ _ _ => Iff.rfl⟩
  obtain ⟨i, hi⟩ := ht.nonempty I hI
  have hall : ∀ u ∈ C, ∀ x ∈ I, G.Adj u x := by
    intro u hu x hx
    have hui : G.Adj u i := by
      by_contra hn
      apply hex
      refine ⟨u, hu, ?_⟩
      intro z hz hadj
      exact hn (((ht.twins I hI z hz i hi u).mp hadj.symm).symm)
    exact ((ht.twins I hI i hi x hx u).mp hui.symm).symm
  obtain ⟨u, hu⟩ := hc.nonempty C hC
  have huB : u ∉ B := fun h => Finset.disjoint_left.mp (hc.disjoint C hC) hu h
  obtain ⟨J, hJ, hmiss⟩ := ht.missing_class hk hcard huB
  have hne : I ≠ J := by
    intro he
    exact hmiss i (he ▸ hi) (hall u hu i hi)
  obtain ⟨j, hj⟩ := ht.nonempty J hJ
  let H := switchCut G C (classSwitch I J i j)
  refine ⟨H, inferInstance,
    block_switch_certificate hc ht hI hJ i j,
    block_switch_partition ht (hc.disjoint C hC) hI hJ i j,
    block_class_switch_cliqueFree ht hk hI hJ hne hi hj (hc.block_separation hC),
    block_class_switch_edges ht (hc.disjoint C hC) hI hJ hne hi hj (hmin J hJ) hall,
    ⟨u, hu, block_switch_missing ht (hc.disjoint C hC) hI i j u hu (hmiss j hj)⟩, ?_⟩
  intro a ha b hb
  simp [H, switchCut, ha, hb]

theorem repair_all_blocks (G : SimpleGraph V) [DecidableRel G.Adj]
    {B : Finset V} {blocks classes : Finset (Finset V)} {s k : ℕ}
    (hc : OddCertificate G B blocks s) (ht : TwinPartition G B classes k)
    (hk : G.CliqueFree (k + 1)) (hcard : classes.card = k)
    {I : Finset V} (hI : I ∈ classes) (hmin : ∀ J ∈ classes, I.card ≤ J.card) :
    ∃ H : SimpleGraph V, ∃ _ : DecidableRel H.Adj,
      OddCertificate H B blocks s ∧ TwinPartition H B classes k ∧ H.CliqueFree (k + 1) ∧
      #G.edgeFinset ≤ #H.edgeFinset ∧ ∀ C ∈ blocks, ∃ u ∈ C, ∀ x ∈ I, ¬H.Adj u x := by
  classical
  have process (P : Finset (Finset V)) (hP : P ⊆ blocks) :
      ∃ H : SimpleGraph V, ∃ _ : DecidableRel H.Adj,
        OddCertificate H B blocks s ∧ TwinPartition H B classes k ∧ H.CliqueFree (k + 1) ∧
        #G.edgeFinset ≤ #H.edgeFinset ∧ ∀ C ∈ P, ∃ u ∈ C, ∀ x ∈ I, ¬H.Adj u x := by
    induction P using Finset.induction_on with
    | empty => exact ⟨G, inferInstance, hc, ht, hk, le_rfl, by simp⟩
    | @insert C P hCP ih =>
      obtain ⟨H, instH, hcH, htH, hkH, heH, hmH⟩ := ih (fun _ h => hP (Finset.mem_insert_of_mem h))
      obtain ⟨K, instK, hcK, htK, hkK, heK, hmK, hout⟩ :=
        repair_one_block H hcH (hP (Finset.mem_insert_self _ _)) htH hkH hcard hI hmin
      refine ⟨K, instK, hcK, htK, hkK, heH.trans heK, ?_⟩
      intro D hD
      rcases Finset.mem_insert.mp hD with rfl | hDP
      · exact hmK
      · obtain ⟨u, hu, hmu⟩ := hmH D hDP
        refine ⟨u, hu, ?_⟩
        intro x hx hadj
        have huC : u ∉ C := by
          intro huC
          have hDC : D ≠ C := by intro he; subst D; exact hCP hDP
          exact Finset.disjoint_left.mp (hcH.pairwise
            (hP (Finset.mem_insert_of_mem hDP)) (hP (Finset.mem_insert_self _ _)) hDC) hu huC
        have hxC : x ∉ C := by
          intro hxC
          exact Finset.disjoint_left.mp (hcH.disjoint C (hP (Finset.mem_insert_self _ _)))
            hxC (htH.subset I hI hx)
        exact hmu x hx ((hout u huC x hxC).mp hadj)
  exact process blocks (fun _ h => h)

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.RepairMissing

-- BEGIN MODULE TMProof.CliqueCap

namespace TuranMatching.Clique.TMFresh
open Finset SimpleGraph

variable {V : Type*} [DecidableEq V]

theorem TwinPartition.clique_card_bound {G : SimpleGraph V} {B : Finset V}
    {classes : Finset (Finset V)} {k : ℕ} (ht : TwinPartition G B classes k)
    {K : Finset V} (hKB : K ⊆ B) (hK : G.IsClique K)
    (allowed : Finset (Finset V))
    (hallowed : ∀ C ∈ classes, (∃ x ∈ K, x ∈ C) → C ∈ allowed) :
    K.card ≤ allowed.card := by
  classical
  have hc (x : K) : ∃ C ∈ classes, (x : V) ∈ C := (ht.cover x).mp (hKB x.property)
  let cls (x : K) : Finset V := (hc x).choose
  have hcls (x : K) : cls x ∈ classes ∧ (x : V) ∈ cls x := (hc x).choose_spec
  let f : K → allowed := fun x => ⟨cls x, hallowed _ (hcls x).1 ⟨x, x.property, (hcls x).2⟩⟩
  have hinj : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    by_contra hn
    have hxy := hK x.property y.property hn
    have hce : cls x = cls y := congrArg Subtype.val he
    have hy : (y : V) ∈ cls x := hce.symm ▸ (hcls y).2
    exact ht.not_adj_same (hcls x).1 (hcls x).2 hy hxy
  have hh := Fintype.card_le_of_injective f hinj
  simpa using hh

theorem TwinPartition.clique_card_avoid {G : SimpleGraph V} {B : Finset V}
    {classes : Finset (Finset V)} {k : ℕ} (ht : TwinPartition G B classes k)
    {I K : Finset V} (hI : I ∈ classes) (hKB : K ⊆ B) (hK : G.IsClique K)
    (havoid : ∀ x ∈ K, x ∉ I) : K.card < k := by
  have hh := ht.clique_card_bound hKB hK (classes.erase I) (by
    intro C hC hex
    apply Finset.mem_erase.mpr
    refine ⟨?_, hC⟩
    intro he
    obtain ⟨x, hx, hxC⟩ := hex
    exact havoid x hx (he ▸ hxC))
  have hsize := Finset.card_erase_add_one hI
  have hk := ht.card
  omega

theorem TwinPartition.clique_card_lt {G : SimpleGraph V} {B : Finset V}
    {classes : Finset (Finset V)} {k : ℕ} (ht : TwinPartition G B classes k)
    (hcard : classes.card < k) {K : Finset V} (hKB : K ⊆ B) (hK : G.IsClique K) :
    K.card < k :=
  (ht.clique_card_bound hKB hK classes (fun _ h _ => h)).trans_lt hcard

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.CliqueCap

-- BEGIN MODULE TMProof.RepairedOptimal

namespace TuranMatching.Clique.TMFresh
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem OptimalCertificate.repaired {G : SimpleGraph V} {B : Finset V}
    {blocks : Finset (Finset V)} {k s : ℕ} (ho : OptimalCertificate G B blocks k s)
    (hkpos : 0 < k) :
    ∃ H : SimpleGraph V, ∃ classes I, OptimalCertificate H B blocks k s ∧
      TwinPartition H B classes k ∧ I ⊆ B ∧
      (∀ C ∈ blocks, ∃ u ∈ C, ∀ x ∈ I, ¬H.Adj u x) ∧
      (∀ K : Finset V, K ⊆ B → H.IsClique K → (∀ x ∈ K, x ∉ I) → K.card < k) := by
  classical
  obtain ⟨H,classes,hopt,ht⟩ := ho.normalize
  by_cases hlt : classes.card < k
  · refine ⟨H,classes,∅,hopt,ht,empty_subset _,?_,?_⟩
    · intro C hC
      obtain ⟨u,hu⟩ := hopt.certificate.nonempty C hC
      exact ⟨u,hu,by simp⟩
    · intro K hKB hK _
      exact ht.clique_card_lt hlt hKB hK
  have hcard : classes.card = k := by have := ht.card; omega
  have hnon : classes.Nonempty := card_pos.mp (by omega)
  obtain ⟨I,hI,hmin⟩ := exists_min_image classes (fun C : Finset V => C.card) hnon
  obtain ⟨J,_,hcJ,htJ,hkJ,heJ,hwJ⟩ := repair_all_blocks H hopt.certificate ht
    hopt.cliqueFree hcard hI hmin
  have he : H.edgeSet.ncard ≤ J.edgeSet.ncard := by
    simpa only [← coe_edgeFinset,Set.ncard_coe_finset] using heJ
  refine ⟨J,classes,I,hopt.transfer hcJ hkJ he le_rfl,htJ,htJ.subset I hI,hwJ,?_⟩
  intro K hKB hK hav
  exact htJ.clique_card_avoid hI hKB hK hav

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.RepairedOptimal

-- BEGIN MODULE TMProof.MatchingCover

namespace TuranMatching.Clique.TMFresh
open SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem matching_edges_le_cover (M : G.Subgraph) (hM : M.IsMatching)
    (C : Finset V) (hC : ∀ u v, M.Adj u v → u ∈ C ∨ v ∈ C) :
    M.edgeSet.ncard ≤ C.card := by
  classical
  let D := {v : V // v ∈ M.verts ∧ v ∈ C}
  let f : D → M.edgeSet := fun v => hM.toEdge ⟨v, v.property.1⟩
  have hf : Function.Surjective f := by
    rintro ⟨e, he⟩
    induction e using Sym2.inductionOn with
    | _ u v =>
      rcases hC u v he with hu | hv
      · exact ⟨⟨u, he.fst_mem, hu⟩, hM.toEdge_eq_of_adj he⟩
      · exact ⟨⟨v, he.snd_mem, hv⟩, hM.toEdge_eq_toEdge_of_adj he |>.symm.trans (hM.toEdge_eq_of_adj he)⟩
  have hb : Fintype.card D ≤ Fintype.card {v // v ∈ C} :=
    Fintype.card_le_of_injective (fun v : D => (⟨v.val, v.property.2⟩ : {v // v ∈ C}))
      (fun a b h => Subtype.ext (congrArg (fun v : {v // v ∈ C} => (v.val : V)) h))
  have ha := Fintype.card_le_of_surjective f hf
  simpa only [Set.fintypeCard_eq_ncard, Fintype.card_coe] using ha.trans hb

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.MatchingCover

-- BEGIN MODULE TMProof.MatchingCard

namespace TuranMatching.Clique.TMFresh
open SimpleGraph
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem matching_vertex_card (M : G.Subgraph) (hM : M.IsMatching) :
    M.verts.ncard = 2 * M.edgeSet.ncard := by
  classical
  have hd (v : V) : M.spanningCoe.degree v = if v ∈ M.verts then 1 else 0 := by
    rw [Subgraph.degree_spanningCoe]
    split_ifs with hv
    · exact (Subgraph.isMatching_iff_forall_degree.mp hM) v hv
    · exact Subgraph.degree_of_notMem_verts hv
  have hs := M.spanningCoe.sum_degrees_eq_twice_card_edges
  simp only [hd] at hs
  have he : M.spanningCoe.edgeSet = M.edgeSet := rfl
  simpa [Set.ncard_eq_toFinset_card', Set.toFinset, SimpleGraph.edgeFinset, he] using hs

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.MatchingCard

-- BEGIN MODULE TMProof.MatchingPullback

namespace TuranMatching.Clique.TMFresh
open SimpleGraph
variable {V W : Type*} [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}

theorem matching_pullback (f : G ↪g H) (M : H.Subgraph) (hM : M.IsMatching)
    (hv : M.verts ⊆ Set.range f) :
    (M.comap f.toHom).IsMatching ∧ (M.comap f.toHom).edgeSet.ncard = M.edgeSet.ncard := by
  classical
  have hm : (M.comap f.toHom).IsMatching := by
    intro u hu
    obtain ⟨w, hw, huniq⟩ := hM hu
    obtain ⟨v, rfl⟩ := hv hw.snd_mem
    refine ⟨v, ⟨(f.map_rel_iff).mp hw.adj_sub, hw⟩, ?_⟩
    intro v' hv'
    exact f.injective (huniq _ hv'.2)
  refine ⟨hm, ?_⟩
  let g : (M.comap f.toHom).verts → M.verts := fun u => ⟨f u, u.property⟩
  have hg : Function.Bijective g := by
    constructor
    · intro u v h
      apply Subtype.ext
      exact f.injective (congrArg Subtype.val h)
    · rintro ⟨w, hw⟩
      obtain ⟨u, rfl⟩ := hv hw
      exact ⟨⟨u, hw⟩, rfl⟩
  have hc := Fintype.card_congr (Equiv.ofBijective g hg)
  simp only [Set.fintypeCard_eq_ncard] at hc
  rw [matching_vertex_card _ hm, matching_vertex_card _ hM] at hc
  omega

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.MatchingPullback

-- BEGIN MODULE TMProof.MatchingBounds

namespace TuranMatching.Clique.TMFresh
open SimpleGraph
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

theorem matchingNumber_le_half : matchingNumber G ≤ Fintype.card V / 2 := by
  apply (matchingNumber_le_iff G _).mpr
  intro M hM
  have hc : M.verts.ncard ≤ Fintype.card V := by simpa using (Set.ncard_le_ncard (Set.subset_univ M.verts))
  rw [matching_vertex_card M hM] at hc
  omega

theorem matchingNumber_le_cover (C : Finset V)
    (hC : ∀ u v, G.Adj u v → u ∈ C ∨ v ∈ C) : matchingNumber G ≤ C.card := by
  apply (matchingNumber_le_iff G _).mpr
  intro M hM
  exact matching_edges_le_cover M hM C (fun u v h => hC u v h.adj_sub)

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.MatchingBounds

-- BEGIN MODULE TMProof.MatchingFilter

namespace TuranMatching.Clique.TMFresh
open SimpleGraph
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

def filterMatching (M : G.Subgraph) (P : Sym2 V → Prop) : G.Subgraph where
  verts := {u | ∃ v, M.Adj u v ∧ P s(u,v)}
  Adj u v := M.Adj u v ∧ P s(u,v)
  adj_sub h := h.1.adj_sub
  edge_vert h := ⟨_, h⟩
  symm := ⟨fun _ _ h => ⟨h.1.symm, by simpa only [Sym2.eq_swap] using h.2⟩⟩

omit [Fintype V] in
theorem filterMatching_isMatching (M : G.Subgraph) (hM : M.IsMatching)
    (P : Sym2 V → Prop) : (filterMatching M P).IsMatching := by
  intro u hu
  obtain ⟨v, hv⟩ := hu
  refine ⟨v, hv, ?_⟩
  intro w hw
  exact hM.eq_of_adj_left hw.1 hv.1

omit [Fintype V] in
theorem filterMatching_edgeSet (M : G.Subgraph) (P : Sym2 V → Prop) :
    (filterMatching M P).edgeSet = M.edgeSet ∩ {e | P e} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v => rfl

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.MatchingFilter

-- BEGIN MODULE TMProof.MatchingDeletion

namespace TuranMatching.Clique.TMFresh
open SimpleGraph
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem matching_deletion_bound (M : G.Subgraph) (hM : M.IsMatching) (C : Finset V) :
    M.edgeSet.ncard ≤
      (filterMatching M (fun e => ∀ v ∈ e, v ∉ C)).edgeSet.ncard + C.card := by
  classical
  let P : Sym2 V → Prop := fun e => ∃ v ∈ e, v ∈ C
  have hc : (filterMatching M P).edgeSet.ncard ≤ C.card := by
    apply matching_edges_le_cover _ (filterMatching_isMatching M hM P) C
    intro u v h
    obtain ⟨x, hx, hxc⟩ := h.2
    rcases Sym2.mem_iff.mp hx with rfl | rfl
    · exact Or.inl hxc
    · exact Or.inr hxc
  have he : M.edgeSet \ (filterMatching M P).edgeSet =
      (filterMatching M (fun e => ∀ v ∈ e, v ∉ C)).edgeSet := by
    rw [filterMatching_edgeSet, filterMatching_edgeSet]
    ext e
    simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_ofPred_eq, P]
    aesop
  have hs : (filterMatching M P).edgeSet ⊆ M.edgeSet := by
    rw [filterMatching_edgeSet]
    exact Set.inter_subset_left
  have hh := Set.ncard_sdiff_add_ncard_of_subset hs
  rw [he] at hh
  omega

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.MatchingDeletion

-- BEGIN MODULE TMProof.UniversalExtension

namespace TuranMatching.Clique.TMFresh
open SimpleGraph
variable {V : Type*} [Fintype V]

def universalExtension (G : SimpleGraph V) (d : ℕ) : SimpleGraph (V ⊕ Fin d) where
  Adj x y := match x, y with
    | .inl u, .inl v => G.Adj u v
    | .inr u, .inr v => u ≠ v
    | _, _ => True
  symm := ⟨by intro x y h; cases x <;> cases y <;> simp_all [SimpleGraph.adj_comm, ne_comm]⟩
  loopless := ⟨by intro x; cases x <;> simp⟩

def oldEmbedding (G : SimpleGraph V) (d : ℕ) : G ↪g universalExtension G d where
  toFun := Sum.inl
  inj' := Sum.inl_injective
  map_rel_iff' := Iff.rfl

theorem universalExtension_no_perfect (G : SimpleGraph V) (d s : ℕ)
    (hG : matchingNumber G ≤ s) (hn : 2 * s + d < Fintype.card V)
    (M : (universalExtension G d).Subgraph) : ¬ M.IsPerfectMatching := by
  classical
  intro hM
  let C : Finset (V ⊕ Fin d) := Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩
  have hC : C.card = d := by simp [C]
  let N := filterMatching M (fun e => ∀ v ∈ e, v ∉ C)
  have hN : N.IsMatching := filterMatching_isMatching M hM.1 _
  have hv : N.verts ⊆ Set.range (oldEmbedding G d) := by
    intro x hx
    obtain ⟨y, hxy, hp⟩ := hx
    have hxC := hp x (Sym2.mem_mk_left x y)
    cases x with
    | inl u => exact ⟨u, rfl⟩
    | inr u => exact False.elim (hxC (by simp [C]))
  obtain ⟨hp, he⟩ := matching_pullback (oldEmbedding G d) N hN hv
  have hne : N.edgeSet.ncard ≤ s := by
    rw [← he]
    exact (matching_size_le G _ hp).trans hG
  have hd := matching_deletion_bound M hM.1 C
  change M.edgeSet.ncard ≤ N.edgeSet.ncard + C.card at hd
  rw [hC] at hd
  have hc := matching_vertex_card M hM.1
  rw [hM.2.verts_eq_univ] at hc
  simp only [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_fin] at hc
  omega

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.UniversalExtension

-- BEGIN MODULE TMProof.TutteUniversal

namespace TuranMatching.Clique.TMFresh
open SimpleGraph
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem tutte_violator_contains_universal (heven : Even (Nat.card V))
    {U : Set V} (hU : G.IsTutteViolator U) {z : V}
    (hz : ∀ x, x ≠ z → G.Adj x z) : z ∈ U := by
  classical
  by_contra hzu
  let H := ((⊤ : G.Subgraph).deleteVerts U).coe
  let z' : ((⊤ : G.Subgraph).deleteVerts U).verts := ⟨z, by simp [hzu]⟩
  have hreach (x : ((⊤ : G.Subgraph).deleteVerts U).verts) : H.Reachable x z' := by
    by_cases hx : x = z'
    · rw [hx]
    · apply SimpleGraph.Adj.reachable
      apply Subgraph.deleteVerts_adj.mpr
      refine ⟨x.property.1, x.property.2, z'.property.1, z'.property.2, ?_⟩
      exact hz x (fun he => hx (Subtype.ext he))
  have hpre : H.Preconnected := fun x y => (hreach x).trans (hreach y).symm
  let : Subsingleton H.ConnectedComponent := hpre.subsingleton_connectedComponent
  have hcard : H.oddComponents.ncard ≤ 1 := (Set.ncard_le_one (Set.toFinite _)).mpr (fun a _ b _ => Subsingleton.elim a b)
  change U.ncard < H.oddComponents.ncard at hU
  have hu0 : U.ncard = 0 := by omega
  have hue : U = ∅ := (Set.ncard_eq_zero (Set.toFinite _)).mp hu0
  have hn : Nat.card ((⊤ : G.Subgraph).deleteVerts U).verts = Nat.card V := by
    simp [hue]
  have he : Even H.oddComponents.ncard := by
    apply Nat.not_odd_iff_even.mp
    rw [H.odd_ncard_oddComponents, hn]
    exact Nat.not_odd_iff_even.mpr heven
  obtain ⟨m, hm⟩ := he
  omega

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.TutteUniversal

-- BEGIN MODULE TMProof.AugmentedBarrier

namespace TuranMatching.Clique.TMFresh
open SimpleGraph
variable {V : Type*} [Fintype V]

theorem augmented_barrier (G : SimpleGraph V) (d s : ℕ)
    (hG : matchingNumber G ≤ s) (hn : 2 * s + d < Fintype.card V)
    (heven : Even (Fintype.card V + d)) :
    ∃ U : Set (V ⊕ Fin d), (universalExtension G d).IsTutteViolator U ∧
      ∀ z : Fin d, Sum.inr z ∈ U := by
  have he : Even (Nat.card (V ⊕ Fin d)) := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_fin] using heven
  obtain ⟨U, hU⟩ := SimpleGraph.exists_isTutteViolator
    (universalExtension_no_perfect G d s hG hn) he
  refine ⟨U, hU, fun z => tutte_violator_contains_universal he hU ?_⟩
  intro x hx
  cases x with
  | inl v => trivial
  | inr v => exact fun h => hx (congrArg Sum.inr h)

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.AugmentedBarrier

-- BEGIN MODULE TMProof.ComponentIso

namespace TuranMatching.Clique.TMFresh
open SimpleGraph
variable {V W : Type*} [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}

noncomputable def componentSupportEquiv (f : G ≃g H) (C : G.ConnectedComponent) :
    C.supp ≃ (f.connectedComponentEquiv C).supp where
  toFun u := ⟨f u, by
    simpa only [ConnectedComponent.mem_supp_iff, Iso.connectedComponentEquiv_apply,
      ConnectedComponent.iso_image_comp_eq_map_iff_eq_comp] using u.property⟩
  invFun u := ⟨f.symm u, by
    simpa only [ConnectedComponent.mem_supp_iff, Iso.connectedComponentEquiv_apply,
      ConnectedComponent.iso_inv_image_comp_eq_iff_eq_map] using u.property⟩
  left_inv u := Subtype.ext (f.left_inv u)
  right_inv u := Subtype.ext (f.right_inv u)

omit [Fintype V] [Fintype W] in
theorem component_ncard_iso (f : G ≃g H) (C : G.ConnectedComponent) :
    C.supp.ncard = (f.connectedComponentEquiv C).supp.ncard := by
  simpa only [Nat.card_coe_set_eq] using Nat.card_congr (componentSupportEquiv f C)

omit [Fintype V] [Fintype W] in
theorem odd_components_ncard_iso (f : G ≃g H) : G.oddComponents.ncard = H.oddComponents.ncard := by
  have he (C : G.ConnectedComponent) : C ∈ G.oddComponents ↔
      f.connectedComponentEquiv C ∈ H.oddComponents := by
    change Odd C.supp.ncard ↔ Odd (f.connectedComponentEquiv C).supp.ncard
    rw [component_ncard_iso f C]
  let e := f.connectedComponentEquiv.subtypeEquiv he
  simpa only [Nat.card_coe_set_eq] using Nat.card_congr e

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.ComponentIso

-- BEGIN MODULE TMProof.OldRemainder

namespace TuranMatching.Clique.TMFresh
open SimpleGraph
variable {V : Type*} [Fintype V]

noncomputable def oldRemainderIso (G : SimpleGraph V) (d : ℕ)
    (U : Set (V ⊕ Fin d)) (hU : ∀ z : Fin d, Sum.inr z ∈ U) :
    G.induce {x | Sum.inl x ∉ U} ≃g
      ((⊤ : (universalExtension G d).Subgraph).deleteVerts U).coe := by
  let f : {x : V // Sum.inl x ∉ U} →
      ((⊤ : (universalExtension G d).Subgraph).deleteVerts U).verts :=
    fun x => ⟨Sum.inl x, by simpa using x.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      exact Subtype.ext (Sum.inl_injective (congrArg Subtype.val h))
    · rintro ⟨x, hx⟩
      cases x with
      | inl v => exact ⟨⟨v, hx.2⟩, rfl⟩
      | inr v => exact False.elim (hx.2 (hU v))
  exact { Equiv.ofBijective f hf with
    map_rel_iff' := by
      intro x y
      change ((⊤ : (universalExtension G d).Subgraph).deleteVerts U).Adj
        (Sum.inl x.val) (Sum.inl y.val) ↔ G.Adj x.val y.val
      rw [Subgraph.deleteVerts_adj]
      change (True ∧ Sum.inl x.val ∉ U ∧ True ∧ Sum.inl y.val ∉ U ∧ G.Adj x.val y.val) ↔ G.Adj x.val y.val
      exact ⟨fun h => h.2.2.2.2, fun h => ⟨True.intro, x.property, True.intro, y.property, h⟩⟩ }

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.OldRemainder

-- BEGIN MODULE TMProof.OldBarrier

namespace TuranMatching.Clique.TMFresh
open SimpleGraph
variable {V : Type*} [Fintype V]

noncomputable def barrierEquiv (d : ℕ) (U : Set (V ⊕ Fin d))
    (hU : ∀ z : Fin d, Sum.inr z ∈ U) : U ≃ ({x : V // Sum.inl x ∈ U} ⊕ Fin d) where
  toFun x := match x with
    | ⟨Sum.inl v, h⟩ => Sum.inl ⟨v, h⟩
    | ⟨Sum.inr v, _⟩ => Sum.inr v
  invFun x := match x with
    | Sum.inl v => ⟨Sum.inl v.val, v.property⟩
    | Sum.inr v => ⟨Sum.inr v, hU v⟩
  left_inv x := by rcases x with ⟨x,h⟩; cases x <;> rfl
  right_inv x := by cases x <;> rfl

theorem barrier_card (d : ℕ) (U : Set (V ⊕ Fin d))
    (hU : ∀ z : Fin d, Sum.inr z ∈ U) :
    U.ncard = {x : V | Sum.inl x ∈ U}.ncard + d := by
  classical
  let B : Set V := {x | Sum.inl x ∈ U}
  let e : U ≃ (B ⊕ Fin d) := barrierEquiv d U hU
  have h := Fintype.card_congr e
  rw [Fintype.card_sum, Fintype.card_fin, Set.fintypeCard_eq_ncard,
    Set.fintypeCard_eq_ncard] at h
  exact h

theorem old_barrier (G : SimpleGraph V) (d s : ℕ)
    (hG : matchingNumber G ≤ s) (hn : 2*s+d < Fintype.card V)
    (heven : Even (Fintype.card V+d)) :
    ∃ B : Set V, B.ncard + d < (G.induce Bᶜ).oddComponents.ncard := by
  obtain ⟨U, hu, hall⟩ := augmented_barrier G d s hG hn heven
  refine ⟨{x | Sum.inl x ∈ U}, ?_⟩
  have hi := odd_components_ncard_iso (oldRemainderIso G d U hall)
  change U.ncard < ((⊤ : (universalExtension G d).Subgraph).deleteVerts U).coe.oddComponents.ncard at hu
  rw [barrier_card d U hall] at hu
  exact hi.symm ▸ hu

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.OldBarrier

-- BEGIN MODULE TMProof.ComponentBlocks

namespace TuranMatching.Clique.TMFresh
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (B : Set V)

noncomputable def componentBlock (C : (G.induce Bᶜ).ConnectedComponent) : Finset V := by
  classical
  exact C.supp.toFinset.image Subtype.val

theorem mem_componentBlock (C : (G.induce Bᶜ).ConnectedComponent) (v : V) :
    v ∈ componentBlock G B C ↔ ∃ h : v ∉ B, (⟨v,h⟩ : ↥(Bᶜ)) ∈ C.supp := by
  classical
  simp only [componentBlock, Finset.mem_image, Set.mem_toFinset]
  constructor
  · rintro ⟨⟨w,hw⟩, hc, rfl⟩
    exact ⟨hw,hc⟩
  · rintro ⟨h,hc⟩
    exact ⟨⟨v,h⟩,hc,rfl⟩

theorem componentBlock_nonempty (C : (G.induce Bᶜ).ConnectedComponent) :
    (componentBlock G B C).Nonempty := by
  obtain ⟨v,hv⟩ := C.nonempty_supp
  exact ⟨v, (mem_componentBlock G B C v).mpr ⟨v.property,hv⟩⟩

theorem componentBlock_card (C : (G.induce Bᶜ).ConnectedComponent) :
    (componentBlock G B C).card = C.supp.ncard := by
  classical
  rw [componentBlock, Finset.card_image_of_injective _ Subtype.val_injective]
  exact (Set.ncard_eq_toFinset_card' C.supp).symm

theorem componentBlock_disjoint {C D : (G.induce Bᶜ).ConnectedComponent} (h : C ≠ D) :
    Disjoint (componentBlock G B C) (componentBlock G B D) := by
  classical
  rw [Finset.disjoint_left]
  intro v hv hw
  obtain ⟨hv,hc⟩ := (mem_componentBlock G B C v).mp hv
  obtain ⟨hw,hd⟩ := (mem_componentBlock G B D v).mp hw
  exact h (ConnectedComponent.eq_of_common_vertex hc hd)

theorem componentBlock_no_edge {C D : (G.induce Bᶜ).ConnectedComponent} (h : C ≠ D)
    {u v : V} (hu : u ∈ componentBlock G B C) (hv : v ∈ componentBlock G B D) :
    ¬ G.Adj u v := by
  obtain ⟨hu,hc⟩ := (mem_componentBlock G B C u).mp hu
  obtain ⟨hv,hd⟩ := (mem_componentBlock G B D v).mp hv
  intro hadj
  have hm := C.mem_supp_of_adj_mem_supp hc (show (G.induce Bᶜ).Adj ⟨u,hu⟩ ⟨v,hv⟩ from hadj)
  exact h (ConnectedComponent.eq_of_common_vertex hm hd)

noncomputable def componentBlocks : Finset (Finset V) := by
  classical
  exact Finset.univ.image (componentBlock G B)

theorem componentBlocks_cover (v : V) :
    v ∉ B ↔ ∃ C ∈ componentBlocks G B, v ∈ C := by
  classical
  constructor
  · intro hv
    let c := (G.induce Bᶜ).connectedComponentMk ⟨v,hv⟩
    exact ⟨componentBlock G B c, by unfold componentBlocks; exact Finset.mem_image.mpr ⟨c,Finset.mem_univ _,rfl⟩,
      (mem_componentBlock G B c v).mpr ⟨hv,rfl⟩⟩
  · rintro ⟨C,hC,hv⟩
    obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hC
    exact ((mem_componentBlock G B c v).mp hv).choose

theorem componentBlock_injective : Function.Injective (componentBlock G B) := by
  intro C D h
  by_contra hn
  obtain ⟨v,hv⟩ := componentBlock_nonempty G B C
  exact Finset.disjoint_left.mp (componentBlock_disjoint G B hn) hv (h ▸ hv)

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.ComponentBlocks

-- BEGIN MODULE TMProof.BlockPartition

namespace TuranMatching.Clique.TMFresh
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

structure BlockPartition (G : SimpleGraph V) (B : Finset V)
    (blocks : Finset (Finset V)) : Prop where
  nonempty : ∀ C ∈ blocks, C.Nonempty
  disjoint : ∀ C ∈ blocks, Disjoint C B
  pairwise : Set.PairwiseDisjoint (blocks : Set (Finset V)) id
  cover : ∀ v, v ∉ B ↔ ∃ C ∈ blocks, v ∈ C
  edges : ∀ C ∈ blocks, ∀ D ∈ blocks, C ≠ D →
    ∀ u ∈ C, ∀ v ∈ D, ¬ G.Adj u v

theorem componentBlocks_partition (G : SimpleGraph V) (B : Set V) [DecidablePred (· ∈ B)] :
    BlockPartition G B.toFinset (componentBlocks G B) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro C hC
    obtain ⟨c,_,rfl⟩ := mem_image.mp hC
    exact componentBlock_nonempty G B c
  · intro C hC
    obtain ⟨c,_,rfl⟩ := mem_image.mp hC
    apply Finset.disjoint_left.mpr
    intro v hv hb
    exact ((mem_componentBlock G B c v).mp hv).choose (Set.mem_toFinset.mp hb)
  · intro C hC D hD hne
    obtain ⟨c,_,rfl⟩ := mem_image.mp hC
    obtain ⟨d,_,rfl⟩ := mem_image.mp hD
    exact componentBlock_disjoint G B (fun h => hne (congrArg _ h))
  · intro v
    simpa only [Set.mem_toFinset] using componentBlocks_cover G B v
  · intro C hC D hD hne u hu v hv
    obtain ⟨c,_,rfl⟩ := mem_image.mp hC
    obtain ⟨d,_,rfl⟩ := mem_image.mp hD
    exact componentBlock_no_edge G B (fun h => hne (congrArg _ h)) hu hv

omit [Fintype V] [DecidableEq V] in
theorem BlockPartition.toOddCertificate {G : SimpleGraph V} {B : Finset V}
    {blocks : Finset (Finset V)} (h : BlockPartition G B blocks)
    (ho : ∀ C ∈ blocks, Odd C.card) :
    OddCertificate G B blocks (B.card + ∑ C ∈ blocks, (C.card-1)/2) :=
  ⟨h.nonempty,ho,h.disjoint,h.pairwise,h.cover,h.edges,rfl⟩

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.BlockPartition

-- BEGIN MODULE TMProof.MergePartition

namespace TuranMatching.Clique.TMFresh
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

noncomputable def mergeBlocks (blocks : Finset (Finset V)) (C D : Finset V) :=
  insert (C ∪ D) ((blocks.erase C).erase D)

omit [Fintype V] in
theorem BlockPartition.merge {B : Finset V} {blocks : Finset (Finset V)}
    (h : BlockPartition G B blocks) {C D : Finset V}
    (hC : C ∈ blocks) (hD : D ∈ blocks) :
    BlockPartition G B (mergeBlocks blocks C D) := by
  classical
  have hrest (E : Finset V) (he : E ∈ (blocks.erase C).erase D) :
      E ∈ blocks ∧ E ≠ C ∧ E ≠ D := by
    simp only [mem_erase] at he
    exact ⟨he.2.2,he.2.1,he.1⟩
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro E he
    rcases mem_insert.mp he with rfl | he
    · exact (h.nonempty C hC).mono subset_union_left
    · exact h.nonempty E (hrest E he).1
  · intro E he
    rcases mem_insert.mp he with rfl | he
    · exact Finset.disjoint_union_left.mpr ⟨h.disjoint C hC,h.disjoint D hD⟩
    · exact h.disjoint E (hrest E he).1
  · intro E he F hf hef
    rcases mem_insert.mp he with rfl | he <;> rcases mem_insert.mp hf with rfl | hf
    · exact False.elim (hef rfl)
    · obtain ⟨hf,hfc,hfd⟩ := hrest F hf
      exact Finset.disjoint_union_left.mpr ⟨h.pairwise hC hf hfc.symm,h.pairwise hD hf hfd.symm⟩
    · obtain ⟨he,hec,hed⟩ := hrest E he
      exact (Finset.disjoint_union_left.mpr ⟨h.pairwise hC he hec.symm,h.pairwise hD he hed.symm⟩).symm
    · exact h.pairwise (hrest E he).1 (hrest F hf).1 hef
  · intro v
    rw [h.cover]
    constructor
    · rintro ⟨E,he,hv⟩
      by_cases hc : E=C
      · subst E; exact ⟨C∪D,mem_insert_self _ _,mem_union_left _ hv⟩
      by_cases hd : E=D
      · subst E; exact ⟨C∪D,mem_insert_self _ _,mem_union_right _ hv⟩
      exact ⟨E,mem_insert_of_mem (mem_erase.mpr ⟨hd,mem_erase.mpr ⟨hc,he⟩⟩),hv⟩
    · rintro ⟨E,he,hv⟩
      rcases mem_insert.mp he with rfl | he
      · rcases mem_union.mp hv with hv | hv
        · exact ⟨C,hC,hv⟩
        · exact ⟨D,hD,hv⟩
      · exact ⟨E,(hrest E he).1,hv⟩
  · intro E he F hf hef u hu v hv
    rcases mem_insert.mp he with rfl | he <;> rcases mem_insert.mp hf with rfl | hf
    · exact False.elim (hef rfl)
    · obtain ⟨hf,hfc,hfd⟩ := hrest F hf
      rcases mem_union.mp hu with hu | hu
      · exact h.edges C hC F hf hfc.symm u hu v hv
      · exact h.edges D hD F hf hfd.symm u hu v hv
    · obtain ⟨he,hec,hed⟩ := hrest E he
      rcases mem_union.mp hv with hv | hv
      · exact h.edges E he C hC hec u hu v hv
      · exact h.edges E he D hD hed u hu v hv
    · exact h.edges E (hrest E he).1 F (hrest F hf).1 hef u hu v hv

omit [Fintype V] in
theorem BlockPartition.union_not_mem_rest {B : Finset V} {blocks : Finset (Finset V)}
    (h : BlockPartition G B blocks) {C D : Finset V} (hC : C ∈ blocks) :
    C ∪ D ∉ (blocks.erase C).erase D := by
  intro hm
  simp only [mem_erase] at hm
  obtain ⟨v,hv⟩ := h.nonempty C hC
  exact Finset.disjoint_left.mp (h.pairwise hC hm.2.2 hm.2.1.symm)
    hv (mem_union_left _ hv)

omit [Fintype V] in
theorem BlockPartition.merge_card {B : Finset V} {blocks : Finset (Finset V)}
    (h : BlockPartition G B blocks) {C D : Finset V}
    (hC : C ∈ blocks) (hD : D ∈ blocks) (hne : C ≠ D) :
    (mergeBlocks blocks C D).card + 1 = blocks.card := by
  classical
  rw [mergeBlocks, card_insert_of_notMem (h.union_not_mem_rest hC)]
  have heC := card_erase_add_one hC
  have heD := card_erase_add_one (mem_erase.mpr ⟨hne.symm,hD⟩)
  omega

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.MergePartition

-- BEGIN MODULE TMProof.SplitPartition

namespace TuranMatching.Clique.TMFresh
open SimpleGraph Finset
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

noncomputable def splitBlocks (blocks : Finset (Finset V)) (C L R : Finset V) :=
  insert L (insert R (blocks.erase C))

theorem BlockPartition.split {B : Finset V} {blocks : Finset (Finset V)}
    (h : BlockPartition G B blocks) {C L R : Finset V} (hC : C ∈ blocks)
    (hL : L.Nonempty) (hR : R.Nonempty) (hd : Disjoint L R) (hu : L ∪ R = C)
    (hsep : ∀ u ∈ L, ∀ v ∈ R, ¬ G.Adj u v) :
    BlockPartition G B (splitBlocks blocks C L R) := by
  classical
  have hlc : L ⊆ C := hu ▸ subset_union_left
  have hrc : R ⊆ C := hu ▸ subset_union_right
  have hrest (E : Finset V) (he : E ∈ blocks.erase C) : E ∈ blocks ∧ E ≠ C :=
    ⟨(mem_erase.mp he).2,(mem_erase.mp he).1⟩
  have hdl (E : Finset V) (he : E ∈ blocks.erase C) : Disjoint L E :=
    (h.pairwise hC (hrest E he).1 (hrest E he).2.symm).mono_left hlc
  have hdr (E : Finset V) (he : E ∈ blocks.erase C) : Disjoint R E :=
    (h.pairwise hC (hrest E he).1 (hrest E he).2.symm).mono_left hrc
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro E he
    rcases mem_insert.mp he with rfl | he
    · exact hL
    rcases mem_insert.mp he with rfl | he
    · exact hR
    · exact h.nonempty E (hrest E he).1
  · intro E he
    rcases mem_insert.mp he with rfl | he
    · exact (h.disjoint C hC).mono_left hlc
    rcases mem_insert.mp he with rfl | he
    · exact (h.disjoint C hC).mono_left hrc
    · exact h.disjoint E (hrest E he).1
  · intro E he F hf hne
    rcases mem_insert.mp he with rfl | heL
    · rcases mem_insert.mp hf with rfl | hf
      · exact False.elim (hne rfl)
      rcases mem_insert.mp hf with rfl | hf
      · exact hd
      · exact hdl F hf
    rcases mem_insert.mp heL with rfl | heR
    · rcases mem_insert.mp hf with rfl | hf
      · exact hd.symm
      rcases mem_insert.mp hf with rfl | hf
      · exact False.elim (hne rfl)
      · exact hdr F hf
    rcases mem_insert.mp hf with rfl | hf
    · exact (hdl E heR).symm
    rcases mem_insert.mp hf with rfl | hf
    · exact (hdr E heR).symm
    · exact h.pairwise (hrest E heR).1 (hrest F hf).1 hne
  · intro v
    rw [h.cover]
    constructor
    · rintro ⟨E,he,hv⟩
      by_cases hec : E=C
      · subst E
        rw [← hu] at hv
        rcases mem_union.mp hv with hv | hv
        · exact ⟨L,mem_insert_self _ _,hv⟩
        · exact ⟨R,mem_insert_of_mem (mem_insert_self _ _),hv⟩
      · exact ⟨E,mem_insert_of_mem (mem_insert_of_mem (mem_erase.mpr ⟨hec,he⟩)),hv⟩
    · rintro ⟨E,he,hv⟩
      rcases mem_insert.mp he with rfl | he
      · exact ⟨C,hC,hlc hv⟩
      rcases mem_insert.mp he with rfl | he
      · exact ⟨C,hC,hrc hv⟩
      · exact ⟨E,(hrest E he).1,hv⟩
  · intro E he F hf hne u hu' v hv
    rcases mem_insert.mp he with rfl | heL
    · rcases mem_insert.mp hf with rfl | hf
      · exact False.elim (hne rfl)
      rcases mem_insert.mp hf with rfl | hf
      · exact hsep u hu' v hv
      · exact h.edges C hC F (hrest F hf).1 (hrest F hf).2.symm u (hlc hu') v hv
    rcases mem_insert.mp heL with rfl | heR
    · rcases mem_insert.mp hf with rfl | hf
      · exact fun ha => hsep v hv u hu' ha.symm
      rcases mem_insert.mp hf with rfl | hf
      · exact False.elim (hne rfl)
      · exact h.edges C hC F (hrest F hf).1 (hrest F hf).2.symm u (hrc hu') v hv
    rcases mem_insert.mp hf with rfl | hf
    · exact h.edges E (hrest E heR).1 C hC (hrest E heR).2 u hu' v (hlc hv)
    rcases mem_insert.mp hf with rfl | hf
    · exact h.edges E (hrest E heR).1 C hC (hrest E heR).2 u hu' v (hrc hv)
    · exact h.edges E (hrest E heR).1 F (hrest F hf).1 hne u hu' v hv

theorem BlockPartition.subset_not_mem_rest {B : Finset V} {blocks : Finset (Finset V)}
    (h : BlockPartition G B blocks) {C L : Finset V} (hC : C ∈ blocks)
    (hL : L.Nonempty) (hlc : L ⊆ C) : L ∉ blocks.erase C := by
  intro hm
  obtain ⟨hne,hmem⟩ := mem_erase.mp hm
  obtain ⟨v,hv⟩ := hL
  exact Finset.disjoint_left.mp (h.pairwise hC hmem hne.symm) (hlc hv) hv

theorem BlockPartition.split_card {B : Finset V} {blocks : Finset (Finset V)}
    (h : BlockPartition G B blocks) {C L R : Finset V} (hC : C ∈ blocks)
    (hL : L.Nonempty) (hR : R.Nonempty) (hd : Disjoint L R) (hu : L ∪ R = C) :
    (splitBlocks blocks C L R).card = blocks.card+1 := by
  classical
  have hlc : L ⊆ C := hu ▸ subset_union_left
  have hrc : R ⊆ C := hu ▸ subset_union_right
  have hl := h.subset_not_mem_rest hC hL hlc
  have hr := h.subset_not_mem_rest hC hR hrc
  have hne : L ≠ R := by
    intro hh
    obtain ⟨v,hv⟩ := hL
    exact Finset.disjoint_left.mp hd hv (hh ▸ hv)
  rw [splitBlocks,card_insert_of_notMem (by simp [hne,hl]),card_insert_of_notMem hr]
  have hc := card_erase_add_one hC
  omega

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.SplitPartition

-- BEGIN MODULE TMProof.ReplaceInternal

namespace TuranMatching.Clique.TMFresh
open SimpleGraph Finset
variable {V : Type*} [DecidableEq V]

theorem BlockPartition.replace_internal {G H : SimpleGraph V} {B : Finset V}
    {blocks : Finset (Finset V)} (hp : BlockPartition G B blocks)
    {C : Finset V} (hC : C ∈ blocks)
    (hsep : ∀ u ∈ C, ∀ v, v ∉ C → v ∉ B → ¬H.Adj u v)
    (hout : ∀ u ∉ C, ∀ v ∉ C, H.Adj u v → G.Adj u v) :
    BlockPartition H B blocks := by
  refine ⟨hp.nonempty,hp.disjoint,hp.pairwise,hp.cover,?_⟩
  intro D hD E hE hde u hu v hv hadj
  have huB : u ∉ B := (hp.cover u).mpr ⟨D,hD,hu⟩
  have hvB : v ∉ B := (hp.cover v).mpr ⟨E,hE,hv⟩
  by_cases hd : D=C
  · subst D
    have hvC : v ∉ C := fun h => Finset.disjoint_left.mp (hp.pairwise hC hE hde) h hv
    exact hsep u hu v hvC hvB hadj
  by_cases he : E=C
  · subst E
    have huC : u ∉ C := fun h => Finset.disjoint_left.mp (hp.pairwise hD hC hde) hu h
    exact hsep v hv u huC huB hadj.symm
  have huC : u ∉ C := fun h => Finset.disjoint_left.mp (hp.pairwise hD hC hd) hu h
  have hvC : v ∉ C := fun h => Finset.disjoint_left.mp (hp.pairwise hE hC he) hv h
  exact hp.edges D hD E hE hde u hu v hv (hout u huC v hvC hadj)

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.ReplaceInternal

-- BEGIN MODULE TMProof.MergeGraph

namespace TuranMatching.Clique.TMFresh
open Finset SimpleGraph

variable {V : Type*} [DecidableEq V]

def mergeRowU (G : SimpleGraph V) (B C : Finset V) (u v x : V) : Prop :=
  x ≠ u ∧ x ≠ v ∧ if x ∈ B then G.Adj u x ∧ G.Adj v x
    else if x ∈ C then G.Adj v x else G.Adj u x

def mergeRowV (G : SimpleGraph V) (B : Finset V) (u v x : V) : Prop :=
  x ≠ u ∧ x ≠ v ∧ x ∈ B ∧ (G.Adj u x ∨ G.Adj v x)

def mergeGraph (G : SimpleGraph V) (B C : Finset V) (u v : V) : SimpleGraph V where
  Adj a b := if a = u then mergeRowU G B C u v b else if b = u then mergeRowU G B C u v a
    else if a = v then mergeRowV G B u v b else if b = v then mergeRowV G B u v a else G.Adj a b
  symm.symm a b := by
    by_cases ha : a = u <;> by_cases hb : b = u <;>
      by_cases hav : a = v <;> by_cases hbv : b = v <;>
      simp_all [mergeRowU, mergeRowV, adj_comm]
  loopless.irrefl a := by
    by_cases ha : a = u <;> by_cases hav : a = v <;> simp [ha, hav, mergeRowU, mergeRowV]

instance (G : SimpleGraph V) [DecidableRel G.Adj] (B C : Finset V) (u v : V) :
    DecidableRel (mergeGraph G B C u v).Adj := by
  unfold mergeGraph mergeRowU mergeRowV
  infer_instance

theorem mergeGraph_u (G : SimpleGraph V) (B C : Finset V) (u v x : V) :
    (mergeGraph G B C u v).Adj u x ↔ mergeRowU G B C u v x := by
  simp [mergeGraph]

theorem mergeGraph_v (G : SimpleGraph V) (B C : Finset V) {u v : V}
    (hne : u ≠ v) (x : V) :
    (mergeGraph G B C u v).Adj v x ↔ mergeRowV G B u v x := by
  by_cases hx : x = u
  · subst x
    simp [mergeGraph, mergeRowU, mergeRowV, hne, hne.symm]
  · simp [mergeGraph, hx, hne.symm]

theorem mergeGraph_away (G : SimpleGraph V) (B C : Finset V) {u v a b : V}
    (hau : a ≠ u) (hav : a ≠ v) (hbu : b ≠ u) (hbv : b ≠ v) :
    (mergeGraph G B C u v).Adj a b ↔ G.Adj a b := by
  simp [mergeGraph, hau, hav, hbu, hbv]

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.MergeGraph

-- BEGIN MODULE TMProof.MergeClique

namespace TuranMatching.Clique.TMFresh
open Finset SimpleGraph

variable {V : Type*} [DecidableEq V]

theorem clique_map_contradiction {G : SimpleGraph V} {k : ℕ} (hk : G.CliqueFree k)
    (K : Finset V) (hcard : K.card = k) (g : V → V)
    (hmap : ∀ a ∈ K, ∀ b ∈ K, a ≠ b → G.Adj (g a) (g b)) : False := by
  classical
  have hinj : Set.InjOn g (K : Set V) := by
    intro a ha b hb he
    by_contra hn
    have hh := hmap a ha b hb hn
    rw [he] at hh
    exact G.irrefl hh
  apply hk (K.image g)
  refine ⟨?_, (Finset.card_image_of_injOn hinj).trans hcard⟩
  intro a ha b hb hab
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
  exact hmap x hx y hy (fun he => hab (congrArg g he))

theorem mergeGraph_cliqueFree {G : SimpleGraph V} {B C I : Finset V} {u v : V} {k : ℕ}
    (hk : G.CliqueFree (k + 1)) (huC : u ∉ C) (hvu : u ≠ v)
    (hsep : ∀ c ∈ C, ∀ x, x ∉ C → x ∉ B → ¬G.Adj c x)
    (hmissU : ∀ x ∈ I, ¬G.Adj u x) (hmissV : ∀ x ∈ I, ¬G.Adj v x)
    (hcap : ∀ K : Finset V, K ⊆ B → G.IsClique K → (∀ x ∈ K, x ∉ I) → K.card < k) :
    (mergeGraph G B C u v).CliqueFree (k + 1) := by
  classical
  intro K hK
  let H := mergeGraph G B C u v
  by_cases hvK : v ∈ K
  · have hx (x : V) (hx : x ∈ K.erase v) : mergeRowV G B u v x := by
      obtain ⟨hxv, hxK⟩ := Finset.mem_erase.mp hx
      exact (mergeGraph_v G B C hvu x).mp (hK.isClique hvK hxK hxv.symm)
    have hsub : K.erase v ⊆ B := fun x h => (hx x h).2.2.1
    have hcl : G.IsClique (K.erase v) := by
      intro a ha b hb hab
      have hA := hx a ha
      have hB := hx b hb
      exact (mergeGraph_away G B C hA.1 hA.2.1 hB.1 hB.2.1).mp
        (hK.isClique (Finset.mem_of_mem_erase ha) (Finset.mem_of_mem_erase hb) hab)
    have hav : ∀ x ∈ K.erase v, x ∉ I := by
      intro x hxK hxI
      rcases (hx x hxK).2.2.2 with h | h
      · exact hmissU x hxI h
      · exact hmissV x hxI h
    have hh := hcap (K.erase v) hsub hcl hav
    have hc := Finset.card_erase_add_one hvK
    have he := hK.card_eq
    omega
  · have hnv (x : V) (hx : x ∈ K) : x ≠ v := fun he => hvK (he ▸ hx)
    by_cases hex : ∃ c ∈ K, c ∈ C
    · obtain ⟨c, hcK, hcC⟩ := hex
      have hcu : c ≠ u := fun he => huC (he ▸ hcC)
      have hplace (x : V) (hx : x ∈ K) (hxu : x ≠ u) : x ∈ C ∨ x ∈ B := by
        by_cases hxC : x ∈ C
        · exact Or.inl hxC
        · right
          by_contra hxB
          have hcx : c ≠ x := fun he => hxC (he ▸ hcC)
          have hh := hK.isClique hcK hx hcx
          have hh' := (mergeGraph_away G B C hcu (hnv c hcK) hxu (hnv x hx)).mp hh
          exact hsep c hcC x hxC hxB hh'
      let g : V → V := fun x => if x = u then v else x
      apply clique_map_contradiction hk K hK.card_eq g
      intro a ha b hb hab
      have hadj := hK.isClique ha hb hab
      have hurow {x : V} (hx : x ∈ K) (hxu : x ≠ u)
          (hadj : H.Adj u x) : G.Adj v x := by
        have hr := (mergeGraph_u G B C u v x).mp hadj
        rcases hplace x hx hxu with hxC | hxB
        · by_cases hb : x ∈ B
          · exact (if_pos hb ▸ hr.2.2).2
          · simpa [hb, hxC] using hr.2.2
        · exact (if_pos hxB ▸ hr.2.2).2
      by_cases hau : a = u
      · subst a
        have hbu : b ≠ u := hab.symm
        simpa [g, hbu] using hurow hb hbu hadj
      · by_cases hbu : b = u
        · subst b
          simpa [g, hau] using (hurow ha hau hadj.symm).symm
        · simpa [g, hau, hbu] using
            (mergeGraph_away G B C hau (hnv a ha) hbu (hnv b hb)).mp hadj
    · have hnotC (x : V) (hx : x ∈ K) : x ∉ C := fun h => hex ⟨x, hx, h⟩
      apply hk K
      refine ⟨?_, hK.card_eq⟩
      intro a ha b hb hab
      have hadj := hK.isClique ha hb hab
      have hurow {x : V} (hx : x ∈ K) (hadj : H.Adj u x) : G.Adj u x := by
        have hr := (mergeGraph_u G B C u v x).mp hadj
        by_cases hxB : x ∈ B
        · exact (if_pos hxB ▸ hr.2.2).1
        · simpa [hxB, hnotC x hx] using hr.2.2
      by_cases hau : a = u
      · subst a
        exact hurow hb hadj
      · by_cases hbu : b = u
        · subst b
          exact (hurow ha hadj.symm).symm
        · exact (mergeGraph_away G B C hau (hnv a ha) hbu (hnv b hb)).mp hadj

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.MergeClique

-- BEGIN MODULE TMProof.MergeCount

namespace TuranMatching.Clique.TMFresh
open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem mergeGraph_edge_count {G : SimpleGraph V} [DecidableRel G.Adj]
    {B C : Finset V} {u v : V} (hne : u ≠ v) (huv : ¬G.Adj u v)
    (_huB : u ∉ B) (hvB : v ∉ B)
    (huC : ∀ x ∈ C, ¬G.Adj u x)
    (hvout : ∀ x, x ∉ B → x ∉ C → ¬G.Adj v x) :
    #(mergeGraph G B C u v).edgeFinset = #G.edgeFinset := by
  have hvu : ¬G.Adj v u := fun h => huv h.symm
  let H := mergeGraph G B C u v
  have hpair (x : V) : adjWeight H u x + adjWeight H v x =
      adjWeight G u x + adjWeight G v x := by
    by_cases hxu : x = u
    · subst x
      simp [H, adjWeight, mergeGraph, mergeRowU, mergeRowV, hne.symm, huv, hvu]
    · by_cases hxv : x = v
      · subst x
        simp [H, adjWeight, mergeGraph, mergeRowU, mergeRowV, hne.symm, huv, hvB]
      · by_cases hxB : x ∈ B
        · by_cases ha : G.Adj u x <;> by_cases hb : G.Adj v x <;>
            simp [H, adjWeight, mergeGraph, mergeRowU, mergeRowV, hne.symm, hxu, hxv, hxB, ha, hb]
        · by_cases hxC : x ∈ C
          · have ha := huC x hxC
            by_cases hb : G.Adj v x <;>
              simp [H, adjWeight, mergeGraph, mergeRowU, mergeRowV, hne.symm, hxu, hxv, hxB, hxC, ha, hb]
          · have hb := hvout x hxB hxC
            by_cases ha : G.Adj u x <;>
              simp [H, adjWeight, mergeGraph, mergeRowU, mergeRowV, hne.symm, hxu, hxv, hxB, hxC, ha, hb]
  let d : V → V → ℤ := fun a b => adjWeight H a b - adjWeight G a b
  have hs : ∀ a b, d a b = d b a := by intro a b; simp [d, adjWeight, adj_comm]
  have hzero : ∀ a b, (a ∈ ({u, v} : Finset V) ↔ b ∈ ({u, v} : Finset V)) → d a b = 0 := by
    intro a b he
    by_cases ha : a ∈ ({u, v} : Finset V)
    · have hb := he.mp ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
        simp [d, H, adjWeight, mergeGraph, mergeRowU, mergeRowV, hne.symm, huv, hvu]
    · have hb : b ∉ ({u, v} : Finset V) := fun h => ha (he.mpr h)
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha hb
      simp [d, adjWeight, H, mergeGraph, ha.1, ha.2, hb.1, hb.2]
  have hcut : (∑ a ∈ ({u, v} : Finset V), ∑ b, d a b) = 0 := by
    rw [Finset.sum_insert (by simp [hne]), Finset.sum_singleton, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro x _
    dsimp [d]
    linarith [hpair x]
  have hsum := sum_cross_symmetric ({u, v} : Finset V) d hs hzero
  rw [hcut, mul_zero] at hsum
  have hd (a : V) : ∑ b, d a b = (H.degree a : ℤ) - G.degree a := by
    simp only [d, Finset.sum_sub_distrib, sum_adjWeight]
  simp only [hd, Finset.sum_sub_distrib] at hsum
  have hG : (∑ a, (G.degree a : ℤ)) = 2 * (#G.edgeFinset : ℤ) := by
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  have hH : (∑ a, (H.degree a : ℤ)) = 2 * (#H.edgeFinset : ℤ) := by
    exact_mod_cast H.sum_degrees_eq_twice_card_edges
  rw [hG, hH] at hsum
  have he : (#H.edgeFinset : ℤ) = #G.edgeFinset := by linarith
  exact_mod_cast he

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.MergeCount

-- BEGIN MODULE TMProof.MergeInterface

namespace TuranMatching.Clique.TMFresh
open Finset SimpleGraph

variable {V : Type*} [DecidableEq V]

theorem mergeGraph_v_nonB {G : SimpleGraph V} {B C : Finset V} {u v x : V}
    (hne : u ≠ v) (hx : x ∉ B) : ¬(mergeGraph G B C u v).Adj v x := by
  rw [mergeGraph_v G B C hne]
  simp [mergeRowV, hx]

theorem mergeGraph_missing {G : SimpleGraph V} {B C I : Finset V} {u v : V}
    (hne : u ≠ v) (hIB : I ⊆ B)
    (hu : ∀ x ∈ I, ¬G.Adj u x) (hv : ∀ x ∈ I, ¬G.Adj v x) :
    (∀ x ∈ I, ¬(mergeGraph G B C u v).Adj u x) ∧
    (∀ x ∈ I, ¬(mergeGraph G B C u v).Adj v x) := by
  constructor
  · intro x hx
    rw [mergeGraph_u]
    simp [mergeRowU, hIB hx, hu x hx]
  · intro x hx
    rw [mergeGraph_v G B C hne]
    simp [mergeRowV, hu x hx, hv x hx]

theorem mergeGraph_union_separation {G : SimpleGraph V} {B A C : Finset V} {u v : V}
    (huA : u ∈ A) (hvC : v ∈ C)
    (hsepA : ∀ a ∈ A, ∀ x, x ∉ A → x ∉ B → ¬G.Adj a x)
    (hsepC : ∀ a ∈ C, ∀ x, x ∉ C → x ∉ B → ¬G.Adj a x)
    {a b : V} (ha : a ∈ A ∪ C) (hav : a ≠ v)
    (hbB : b ∉ B) (hb : b ∉ A ∪ C) : ¬(mergeGraph G B C u v).Adj a b := by
  have hbA : b ∉ A := fun h => hb (Finset.mem_union_left _ h)
  have hbC : b ∉ C := fun h => hb (Finset.mem_union_right _ h)
  have hbu : b ≠ u := fun he => hbA (he.symm ▸ huA)
  have hbv : b ≠ v := fun he => hbC (he.symm ▸ hvC)
  by_cases hau : a = u
  · subst a
    rw [mergeGraph_u]
    simp [mergeRowU, hbB, hbC, hsepA u huA b hbA hbB]
  · rw [mergeGraph_away G B C hau hav hbu hbv]
    rcases Finset.mem_union.mp ha with haA | haC
    · exact hsepA a haA b hbA hbB
    · exact hsepC a haC b hbC hbB

theorem mergeGraph_outside_union {G : SimpleGraph V} {B A C : Finset V} {u v : V}
    (huA : u ∈ A) (hvC : v ∈ C) {a b : V}
    (ha : a ∉ A ∪ C) (hb : b ∉ A ∪ C) :
    (mergeGraph G B C u v).Adj a b ↔ G.Adj a b := by
  apply mergeGraph_away G B C
  · intro he; exact ha (he.symm ▸ Finset.mem_union_left C huA)
  · intro he; exact ha (he.symm ▸ Finset.mem_union_right A hvC)
  · intro he; exact hb (he.symm ▸ Finset.mem_union_left C huA)
  · intro he; exact hb (he.symm ▸ Finset.mem_union_right A hvC)

theorem mergeGraph_partition {G : SimpleGraph V} {B C : Finset V}
    {classes : Finset (Finset V)} {k : ℕ} (ht : TwinPartition G B classes k)
    {u v : V} (huB : u ∉ B) (hvB : v ∉ B) :
    TwinPartition (mergeGraph G B C u v) B classes k := by
  have hne {D : Finset V} (hD : D ∈ classes) {a : V} (ha : a ∈ D) : a ≠ u ∧ a ≠ v := by
    have haB := ht.subset D hD ha
    exact ⟨fun he => huB (he ▸ haB), fun he => hvB (he ▸ haB)⟩
  refine ⟨ht.nonempty, ht.subset, ht.pairwise, ht.cover, ?_, ?_, ht.card⟩
  · intro D hD a ha b hb x
    have haB := ht.subset D hD ha
    have hbB := ht.subset D hD hb
    have hau := (hne hD ha).1
    have hav := (hne hD ha).2
    have hbu := (hne hD hb).1
    have hbv := (hne hD hb).2
    have hAu : G.Adj u a ↔ G.Adj u b := by simpa only [adj_comm] using ht.twins D hD a ha b hb u
    have hAv : G.Adj v a ↔ G.Adj v b := by simpa only [adj_comm] using ht.twins D hD a ha b hb v
    by_cases hx : x = u
    · subst x
      simp [mergeGraph, mergeRowU, hau, hav, hbu, hbv, haB, hbB, hAu, hAv]
    · by_cases hxv : x = v
      · subst x
        simp [mergeGraph, mergeRowV, hau, hav, hbu, hbv, hx, haB, hbB, hAu, hAv]
      · simpa [mergeGraph, hau, hav, hbu, hbv, hx, hxv] using ht.twins D hD a ha b hb x
  · intro D hD E hE hde a ha b hb
    exact (mergeGraph_away G B C (hne hD ha).1 (hne hD ha).2
      (hne hE hb).1 (hne hE hb).2).mpr (ht.cross D hD E hE hde a ha b hb)

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.MergeInterface

-- BEGIN MODULE TMProof.MergeParity

namespace TuranMatching.Clique.TMFresh
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

omit [Fintype V] in
theorem BlockPartition.merge_even_odd_count {B : Finset V} {blocks : Finset (Finset V)}
    (h : BlockPartition G B blocks) {C D : Finset V}
    (hC : C ∈ blocks) (hD : D ∈ blocks) (he : Even C.card) (ho : Odd D.card) :
    ((mergeBlocks blocks C D).filter (fun E => Odd E.card)).card =
      (blocks.filter (fun E => Odd E.card)).card := by
  classical
  have hn : ¬ Odd C.card := Nat.not_odd_iff_even.mpr he
  have hne : C ≠ D := by intro hh; exact hn (hh ▸ ho)
  have hdisj : Disjoint C D := h.pairwise hC hD hne
  have hu : Odd (C ∪ D).card := by
    rw [card_union_of_disjoint hdisj]
    exact he.add_odd ho
  have hnm := h.union_not_mem_rest (D := D) hC
  have hd : D ∈ blocks.filter (fun E => Odd E.card) := mem_filter.mpr ⟨hD,ho⟩
  have hc : C ∉ blocks.filter (fun E => Odd E.card) := by simp [hn]
  rw [mergeBlocks, filter_insert, if_pos hu, card_insert_of_notMem]
  · simp only [filter_erase, erase_eq_of_notMem hc]
    exact card_erase_add_one hd
  · exact fun hh => hnm (mem_filter.mp hh).1

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.MergeParity

-- BEGIN MODULE TMProof.CertificateCard

namespace TuranMatching.Clique.TMFresh
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem OddCertificate.total_card {B : Finset V} {blocks : Finset (Finset V)} {s : ℕ}
    (hc : OddCertificate G B blocks s) :
    Fintype.card V = B.card + ∑ C ∈ blocks, C.card := by
  have he : B ∪ blocks.biUnion id = Finset.univ := by
    ext v
    simp only [mem_union, mem_biUnion, id_eq, mem_univ, iff_true]
    by_cases hv : v ∈ B
    · exact Or.inl hv
    · exact Or.inr ((hc.cover v).mp hv)
  have hd : Disjoint B (blocks.biUnion id) := by
    apply Finset.disjoint_left.mpr
    intro v hv hvb
    obtain ⟨C, hC, hvC⟩ := Finset.mem_biUnion.mp hvb
    exact Finset.disjoint_left.mp (hc.disjoint C hC) hvC hv
  have hb := Finset.card_biUnion hc.pairwise
  have hh := congrArg Finset.card he
  rw [Finset.card_union_of_disjoint hd, hb, Finset.card_univ] at hh
  exact hh.symm

theorem OddCertificate.card_identity {B : Finset V} {blocks : Finset (Finset V)} {s : ℕ}
    (hc : OddCertificate G B blocks s) :
    Fintype.card V + B.card = 2 * s + blocks.card := by
  have ho (C : Finset V) (hC : C ∈ blocks) : C.card = 2 * ((C.card - 1) / 2) + 1 := by
    obtain ⟨r, hr⟩ := hc.odd C hC
    omega
  have hs : (∑ C ∈ blocks, C.card) = 2 * (∑ C ∈ blocks, (C.card - 1) / 2) + blocks.card := by
    calc
      _ = ∑ C ∈ blocks, (2 * ((C.card - 1) / 2) + 1) := Finset.sum_congr rfl ho
      _ = _ := by simp [Finset.sum_add_distrib, Finset.mul_sum]
  have ht := hc.total_card
  have hbudget := hc.budget
  omega

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.CertificateCard

-- BEGIN MODULE TMProof.RaiseBudget

namespace TuranMatching.Clique.TMFresh
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

omit [Fintype V] [DecidableEq V] in
theorem OddCertificate.toBlockPartition {B : Finset V} {blocks : Finset (Finset V)} {s : ℕ}
    (h : OddCertificate G B blocks s) : BlockPartition G B blocks :=
  ⟨h.nonempty,h.disjoint,h.pairwise,h.cover,h.edges⟩

theorem OddCertificate.raise {B : Finset V} {blocks : Finset (Finset V)} {s : ℕ}
    (h : OddCertificate G B blocks s) (hsize : 3 ≤ blocks.card) :
    ∃ out, OddCertificate G B out (s+1) := by
  classical
  obtain ⟨C,hC⟩ := card_pos.mp (by omega : 0 < blocks.card)
  have hc := card_erase_add_one hC
  obtain ⟨D,hD'⟩ := card_pos.mp (by omega : 0 < (blocks.erase C).card)
  obtain ⟨hDC,hD⟩ := mem_erase.mp hD'
  have hd := card_erase_add_one hD'
  obtain ⟨E,hE'⟩ := card_pos.mp (by omega : 0 < ((blocks.erase C).erase D).card)
  obtain ⟨hED,hEC,hE⟩ := by simpa only [mem_erase] using hE'
  let bs := mergeBlocks blocks C D
  have hp := h.toBlockPartition
  have hp1 : BlockPartition G B bs := hp.merge hC hD
  have hCD : C ∪ D ∈ bs := mem_insert_self _ _
  have hEb : E ∈ bs := mem_insert_of_mem hE'
  have hCE : C ∪ D ≠ E := by
    intro heq
    exact hp.union_not_mem_rest hC (heq ▸ hE')
  let out := mergeBlocks bs (C ∪ D) E
  have hp2 : BlockPartition G B out := hp1.merge hCD hEb
  have hdisj1 : Disjoint C D := hp.pairwise hC hD hDC.symm
  have hdisj2 : Disjoint (C ∪ D) E := hp1.pairwise hCD hEb hCE
  have hu : Odd ((C ∪ D) ∪ E).card := by
    rw [card_union_of_disjoint hdisj2,
      card_union_of_disjoint hdisj1]
    exact ((h.odd C hC).add_odd (h.odd D hD)).add_odd (h.odd E hE)
  have hodd : ∀ F ∈ out, Odd F.card := by
    intro F hF
    rcases mem_insert.mp hF with rfl | hF
    · exact hu
    · simp only [mem_erase] at hF
      rcases mem_insert.mp hF.2.2 with heq | hF'
      · exact False.elim (hF.2.1 heq)
      · exact h.odd F (mem_erase.mp (mem_erase.mp hF').2).2
  let t := B.card + ∑ F ∈ out, (F.card-1)/2
  have ht : OddCertificate G B out t := hp2.toOddCertificate hodd
  have hcount1 := hp.merge_card hC hD hDC.symm
  have hcount2 := hp1.merge_card hCD hEb hCE
  have hi := h.card_identity
  have hi' := ht.card_identity
  have heq : t = s+1 := by dsimp [out,bs] at *; omega
  exact ⟨out,heq ▸ ht⟩

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.RaiseBudget

-- BEGIN MODULE TMProof.MergerCertificate

namespace TuranMatching.Clique.TMFresh
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

noncomputable def mergerBlocks (blocks : Finset (Finset V)) (A C : Finset V) (v : V) :=
  splitBlocks (mergeBlocks blocks A C) (A∪C) ((A∪C).erase v) {v}

theorem merger_certificate {B : Finset V} {blocks : Finset (Finset V)} {s : ℕ}
    (hc : OddCertificate G B blocks s) {A C : Finset V}
    (hA : A ∈ blocks) (hC : C ∈ blocks) (hAC : A ≠ C)
    {u v : V} (hu : u ∈ A) (hv : v ∈ C) :
    OddCertificate (mergeGraph G B C u v) B (mergerBlocks blocks A C v) s := by
  classical
  have hdisj : Disjoint A C := hc.pairwise hA hC hAC
  have hne : u ≠ v := by intro he; exact Finset.disjoint_left.mp hdisj hu (he.symm ▸ hv)
  have hp := hc.toBlockPartition
  let bs := mergeBlocks blocks A C
  have hp1 : BlockPartition G B bs := hp.merge hA hC
  have hACb : A∪C ∈ bs := mem_insert_self _ _
  have hp2 : BlockPartition (mergeGraph G B C u v) B bs := by
    apply hp1.replace_internal hACb
    · intro a ha b hb hbB
      by_cases hav : a=v
      · subst a; exact mergeGraph_v_nonB hne hbB
      · exact mergeGraph_union_separation hu hv (hc.block_separation hA)
          (hc.block_separation hC) ha hav hbB hb
    · intro a ha b hb hab
      exact (mergeGraph_outside_union hu hv ha hb).mp hab
  have hvU : v ∈ A∪C := mem_union_right _ hv
  have huU : u ∈ A∪C := mem_union_left _ hu
  have hL : ((A∪C).erase v).Nonempty := ⟨u,mem_erase.mpr ⟨hne,huU⟩⟩
  have hR : ({v} : Finset V).Nonempty := singleton_nonempty v
  have hd : Disjoint ((A∪C).erase v) {v} := by simp
  have he : (A∪C).erase v ∪ {v} = A∪C := by
    rw [union_singleton,insert_erase hvU]
  have hp3 : BlockPartition (mergeGraph G B C u v) B (mergerBlocks blocks A C v) := by
    apply hp2.split hACb hL hR hd he
    intro a ha b hb hab
    have hb' := mem_singleton.mp hb
    subst b
    have haB : a ∉ B := (hc.cover a).mpr (by
      rcases mem_union.mp (mem_erase.mp ha).2 with haA | haC
      · exact ⟨A,hA,haA⟩
      · exact ⟨C,hC,haC⟩)
    exact mergeGraph_v_nonB hne haB hab.symm
  have hoL : Odd ((A∪C).erase v).card := by
    have heven := (hc.odd A hA).add_odd (hc.odd C hC)
    have hcard := card_erase_add_one hvU
    rw [card_union_of_disjoint hdisj] at hcard
    obtain ⟨r,hr⟩ := heven
    exact ⟨r-1,by omega⟩
  have ho : ∀ F ∈ mergerBlocks blocks A C v, Odd F.card := by
    intro F hF
    rcases mem_insert.mp hF with rfl | hf1
    · exact hoL
    rcases mem_insert.mp hf1 with rfl | hf2
    · simp
    obtain ⟨hFU,hFbs⟩ := mem_erase.mp hf2
    rcases mem_insert.mp hFbs with hfU | hfrest
    · exact False.elim (hFU hfU)
    exact hc.odd F (mem_erase.mp (mem_erase.mp hfrest).2).2
  let t := B.card + ∑ F ∈ mergerBlocks blocks A C v, (F.card-1)/2
  have ht : OddCertificate (mergeGraph G B C u v) B (mergerBlocks blocks A C v) t :=
    hp3.toOddCertificate ho
  have hc1 := hp.merge_card hA hC hAC
  have hc2 := hp2.split_card hACb hL hR hd he
  have hi := hc.card_identity
  have hi' := ht.card_identity
  have hts : t=s := by dsimp [mergerBlocks,bs] at *; omega
  exact hts ▸ ht

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.MergerCertificate

-- BEGIN MODULE TMProof.PartitionSquares

namespace TuranMatching.Clique.TMFresh
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

omit [Fintype V] in
theorem BlockPartition.merge_square {B : Finset V} {blocks : Finset (Finset V)}
    (hp : BlockPartition G B blocks) {A C : Finset V}
    (hA : A ∈ blocks) (hC : C ∈ blocks) (hne : A ≠ C) :
    blockSquare (mergeBlocks blocks A C) + A.card^2 + C.card^2 =
      blockSquare blocks + (A∪C).card^2 := by
  classical
  unfold blockSquare mergeBlocks
  rw [sum_insert (hp.union_not_mem_rest hA)]
  have h1 := sum_erase_add (s := blocks) (fun E : Finset V => E.card^2) hA
  have h2 := sum_erase_add (s := blocks.erase A) (fun E : Finset V => E.card^2)
    (mem_erase.mpr ⟨hne.symm,hC⟩)
  omega

omit [Fintype V] in
theorem BlockPartition.split_square {B : Finset V} {blocks : Finset (Finset V)}
    (hp : BlockPartition G B blocks) {C L R : Finset V} (hC : C ∈ blocks)
    (hL : L.Nonempty) (hR : R.Nonempty) (hd : Disjoint L R) (hu : L∪R=C) :
    blockSquare (splitBlocks blocks C L R) + C.card^2 =
      blockSquare blocks + L.card^2 + R.card^2 := by
  classical
  have hlc : L ⊆ C := hu ▸ subset_union_left
  have hrc : R ⊆ C := hu ▸ subset_union_right
  have hl := hp.subset_not_mem_rest hC hL hlc
  have hr := hp.subset_not_mem_rest hC hR hrc
  have hne : L ≠ R := by
    intro he
    obtain ⟨v,hv⟩ := hL
    exact Finset.disjoint_left.mp hd hv (he ▸ hv)
  unfold blockSquare splitBlocks
  rw [sum_insert (by simp [hne,hl]),sum_insert hr]
  have hh := sum_erase_add (s := blocks) (fun E : Finset V => E.card^2) hC
  omega

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.PartitionSquares

-- BEGIN MODULE TMProof.MergerSquares

namespace TuranMatching.Clique.TMFresh
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

omit [Fintype V] in
theorem merger_square_increases {B : Finset V} {blocks : Finset (Finset V)} {s : ℕ}
    (hc : OddCertificate G B blocks s) {A C : Finset V}
    (hA : A ∈ blocks) (hC : C ∈ blocks) (hAC : A ≠ C)
    (ha : 3 ≤ A.card) (hcsize : 3 ≤ C.card) {v : V} (hv : v ∈ C) :
    blockSquare blocks < blockSquare (mergerBlocks blocks A C v) := by
  classical
  have hdAC : Disjoint A C := hc.pairwise hA hC hAC
  have hU : (A∪C).card = A.card+C.card := card_union_of_disjoint hdAC
  have hvU : v ∈ A∪C := mem_union_right _ hv
  have hlcard := card_erase_add_one hvU
  have hL : ((A∪C).erase v).Nonempty := card_pos.mp (by omega)
  have hR : ({v} : Finset V).Nonempty := singleton_nonempty v
  have hd : Disjoint ((A∪C).erase v) {v} := by simp
  have he : (A∪C).erase v ∪ {v} = A∪C := by rw [union_singleton,insert_erase hvU]
  have hp := hc.toBlockPartition
  have hp1 := hp.merge hA hC
  have h1 := hp.merge_square hA hC hAC
  have h2 := hp1.split_square (mem_insert_self _ _) hL hR hd he
  change blockSquare (mergerBlocks blocks A C v) + (A∪C).card^2 =
    blockSquare (mergeBlocks blocks A C) + ((A∪C).erase v).card^2 + ({v} : Finset V).card^2 at h2
  rw [card_singleton] at h2
  have hprod : 0 < (A.card-1)*(C.card-1) := Nat.mul_pos (by omega) (by omega)
  have hsubA : A.card-1+1=A.card := by omega
  have hsubC : C.card-1+1=C.card := by omega
  nlinarith

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.MergerSquares

-- BEGIN MODULE TMProof.OneLargeBlock

namespace TuranMatching.Clique.TMFresh
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem OptimalCertificate.no_two_large {B I : Finset V} {blocks : Finset (Finset V)} {k s : ℕ}
    (ho : OptimalCertificate G B blocks k s)
    (hw : ∀ C ∈ blocks, ∃ u ∈ C, ∀ x ∈ I, ¬G.Adj u x)
    (hcap : ∀ K : Finset V, K ⊆ B → G.IsClique K → (∀ x ∈ K, x ∉ I) → K.card < k)
    {A C : Finset V} (hA : A ∈ blocks) (hC : C ∈ blocks)
    (ha : 3 ≤ A.card) (hcsize : 3 ≤ C.card) : A=C := by
  classical
  by_contra hAC
  let hc := ho.certificate
  obtain ⟨u,hu,hmu⟩ := hw A hA
  obtain ⟨v,hv,hmv⟩ := hw C hC
  have hdisj : Disjoint A C := hc.pairwise hA hC hAC
  have huC : u ∉ C := fun h => Finset.disjoint_left.mp hdisj hu h
  have hne : u ≠ v := fun he => huC (he.symm ▸ hv)
  have huB : u ∉ B := (hc.cover u).mpr ⟨A,hA,hu⟩
  have hvB : v ∉ B := (hc.cover v).mpr ⟨C,hC,hv⟩
  have huv : ¬G.Adj u v := hc.edges A hA C hC hAC u hu v hv
  have hsep := hc.block_separation hC
  let H := mergeGraph G B C u v
  let bs := mergerBlocks blocks A C v
  have hcert : OddCertificate H B bs s := merger_certificate hc hA hC hAC hu hv
  have hcl : H.CliqueFree (k+1) := mergeGraph_cliqueFree ho.cliqueFree huC hne hsep hmu hmv hcap
  have he : H.edgeSet.ncard=G.edgeSet.ncard := by
    have he' := mergeGraph_edge_count hne huv huB hvB
      (fun x hx => hc.edges A hA C hC hAC u hu x hx)
      (fun x hxB hxC => hsep v hv x hxC hxB)
    simpa only [← coe_edgeFinset,Set.ncard_coe_finset] using he'
  have hs := ho.square_max H bs hcert hcl he
  have hi := merger_square_increases hc hA hC hAC ha hcsize hv
  exact (not_lt_of_ge hs) hi

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.OneLargeBlock

-- BEGIN MODULE TMProof.AbsorbEven

namespace TuranMatching.Clique.TMFresh
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem BlockPartition.absorb_even {B : Finset V} {blocks : Finset (Finset V)}
    (h : BlockPartition G B blocks)
    (ho : 0 < (blocks.filter (fun C => Odd C.card)).card) :
    ∃ out : Finset (Finset V), BlockPartition G B out ∧
      (∀ C ∈ out, Odd C.card) ∧ out.card = (blocks.filter (fun C => Odd C.card)).card := by
  classical
  have main : ∀ n : ℕ, ∀ bs : Finset (Finset V), bs.card = n →
      BlockPartition G B bs → 0 < (bs.filter (fun C => Odd C.card)).card →
      ∃ out : Finset (Finset V), BlockPartition G B out ∧
        (∀ C ∈ out, Odd C.card) ∧ out.card = (bs.filter (fun C => Odd C.card)).card := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro bs hn hp hpos
      by_cases hall : ∀ C ∈ bs, Odd C.card
      · exact ⟨bs,hp,hall,by rw [filter_eq_self.mpr hall]⟩
      push Not at hall
      obtain ⟨C,hC,hCe⟩ := hall
      obtain ⟨D,hDf⟩ := card_pos.mp hpos
      obtain ⟨hD,hDo⟩ := mem_filter.mp hDf
      have hCD : C ≠ D := by intro hh; exact hCe (hh ▸ hDo)
      have hcount := hp.merge_even_odd_count hC hD (Nat.not_odd_iff_even.mp hCe) hDo
      have hcard := hp.merge_card hC hD hCD
      have hlt : (mergeBlocks bs C D).card < n := by omega
      obtain ⟨out,hout,hodd,houtcard⟩ := ih _ hlt (mergeBlocks bs C D) rfl
        (hp.merge hC hD) (by omega)
      exact ⟨out,hout,hodd,houtcard.trans hcount⟩
  exact main blocks.card blocks rfl h ho

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.AbsorbEven

-- BEGIN MODULE TMProof.ComponentOddCount

namespace TuranMatching.Clique.TMFresh
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem componentBlocks_odd_count (G : SimpleGraph V) (B : Set V) :
    ((componentBlocks G B).filter (fun C => Odd C.card)).card =
      (G.induce Bᶜ).oddComponents.ncard := by
  classical
  have he : (componentBlocks G B).filter (fun C => Odd C.card) =
      ((G.induce Bᶜ).oddComponents.toFinset).image (componentBlock G B) := by
    ext C
    simp only [componentBlocks, mem_filter, mem_image, mem_univ, true_and,
      Set.mem_toFinset]
    constructor
    · rintro ⟨⟨c,rfl⟩,hc⟩
      exact ⟨c,by simpa only [oddComponents, Set.mem_ofPred_eq, componentBlock_card] using hc,rfl⟩
    · rintro ⟨c,hc,rfl⟩
      exact ⟨⟨c,rfl⟩,by simpa only [oddComponents, Set.mem_ofPred_eq, componentBlock_card] using hc⟩
  rw [he,card_image_of_injective _ (componentBlock_injective G B)]
  exact (Set.ncard_eq_toFinset_card' _).symm

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.ComponentOddCount

-- BEGIN MODULE TMProof.InitialOddCertificate

namespace TuranMatching.Clique.TMFresh
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem single_odd_certificate (G : SimpleGraph V) (s : ℕ)
    (hn : Fintype.card V = 2*s+1) :
    OddCertificate G ∅ {univ} s := by
  classical
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro C hC
    have : C = univ := mem_singleton.mp hC
    subst C
    exact card_pos.mp (by rw [card_univ,hn]; omega)
  · intro C hC
    have : C = univ := mem_singleton.mp hC
    subst C
    exact ⟨s,by simpa only [card_univ] using hn⟩
  · intro C hC; exact disjoint_empty_right C
  · intro C hC D hD hne
    exact False.elim (hne ((mem_singleton.mp hC).trans (mem_singleton.mp hD).symm))
  · intro v; simp
  · intro C hC D hD hne
    exact False.elim (hne ((mem_singleton.mp hC).trans (mem_singleton.mp hD).symm))
  · simp only [card_empty, sum_singleton, card_univ, zero_add, hn]
    omega

theorem initial_odd_certificate (G : SimpleGraph V) (s : ℕ)
    (hG : matchingNumber G ≤ s) (hn : 2*s+1 ≤ Fintype.card V) :
    ∃ B blocks t, OddCertificate G B blocks t ∧ t ≤ s := by
  classical
  by_cases heq : Fintype.card V = 2*s+1
  · exact ⟨∅,{univ},s,single_odd_certificate G s heq,le_rfl⟩
  let d := Fintype.card V - 2*s - 2
  have hd : Fintype.card V = 2*s+d+2 := by dsimp [d]; omega
  have heven : Even (Fintype.card V+d) := ⟨s+d+1,by omega⟩
  obtain ⟨B,hB⟩ := old_barrier G d s hG (by omega) heven
  have hp := componentBlocks_partition G B
  have ho := componentBlocks_odd_count G B
  obtain ⟨out,hout,hodd,hcount⟩ := hp.absorb_even (by omega)
  let t := B.toFinset.card + ∑ C ∈ out, (C.card-1)/2
  have hc : OddCertificate G B.toFinset out t := hout.toOddCertificate hodd
  refine ⟨B.toFinset,out,t,hc,?_⟩
  have hi := hc.card_identity
  have hbn : B.toFinset.card = B.ncard := (Set.ncard_eq_toFinset_card' B).symm
  omega

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.InitialOddCertificate

-- BEGIN MODULE TMProof.ExactBudget

namespace TuranMatching.Clique.TMFresh
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem OddCertificate.extend_budget {B : Finset V} {blocks : Finset (Finset V)} {t s : ℕ}
    (h : OddCertificate G B blocks t) (hts : t ≤ s)
    (hn : 2*s+1 ≤ Fintype.card V) : ∃ out, OddCertificate G B out s := by
  have aux : ∀ r : ℕ, ∀ bs : Finset (Finset V), ∀ a : ℕ,
      OddCertificate G B bs a → 2*(a+r)+1 ≤ Fintype.card V →
      ∃ out, OddCertificate G B out (a+r) := by
    intro r
    induction r with
    | zero => intro bs a hc _; exact ⟨bs,by simpa using hc⟩
    | succ r ih =>
      intro bs a hc hsize
      have hid := hc.card_identity
      have hthree : 3 ≤ bs.card := by omega
      obtain ⟨next,hnext⟩ := hc.raise hthree
      obtain ⟨out,hout⟩ := ih next (a+1) hnext (by omega)
      exact ⟨out,by convert hout using 1; omega⟩
  obtain ⟨out,hout⟩ := aux (s-t) blocks t h (by omega)
  exact ⟨out,by convert hout using 1; omega⟩

theorem exact_odd_certificate (G : SimpleGraph V) (s : ℕ)
    (hG : matchingNumber G ≤ s) (hn : 2*s+1 ≤ Fintype.card V) :
    ∃ B blocks, OddCertificate G B blocks s := by
  obtain ⟨B,blocks,t,hc,ht⟩ := initial_odd_certificate G s hG hn
  obtain ⟨out,ho⟩ := hc.extend_budget ht hn
  exact ⟨B,out,ho⟩

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.ExactBudget

-- BEGIN MODULE TMProof.NormalCore

namespace TuranMatching.Clique.TMFresh
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem choose_large_block {B : Finset V} {blocks : Finset (Finset V)} {s : ℕ}
    (hc : OddCertificate G B blocks s) (hn : 2*s+1 ≤ Fintype.card V)
    (huniq : ∀ A ∈ blocks, ∀ C ∈ blocks, 3 ≤ A.card → 3 ≤ C.card → A=C) :
    ∃ A ∈ blocks, ∀ C ∈ blocks, C ≠ A → C.card=1 := by
  classical
  have hnon : blocks.Nonempty := by
    have hb : B.card ≤ s := by have := hc.budget; omega
    have hi := hc.card_identity
    exact card_pos.mp (by omega)
  by_cases hex : ∃ A ∈ blocks, 3 ≤ A.card
  · obtain ⟨A,hA,ha⟩ := hex
    refine ⟨A,hA,?_⟩
    intro C hC hne
    have ho := hc.odd C hC
    by_contra hn1
    have h3 : 3 ≤ C.card := by obtain ⟨r,hr⟩ := ho; omega
    exact hne (huniq C hC A hA h3 ha)
  · obtain ⟨A,hA⟩ := hnon
    refine ⟨A,hA,?_⟩
    intro C hC _
    have ho := hc.odd C hC
    have h3 : ¬3 ≤ C.card := fun h => hex ⟨C,hC,h⟩
    obtain ⟨r,hr⟩ := ho
    omega

omit [Fintype V] in
theorem normal_core_properties {B A : Finset V} {blocks : Finset (Finset V)} {s : ℕ}
    (hc : OddCertificate G B blocks s) (hA : A ∈ blocks)
    (hsmall : ∀ C ∈ blocks, C ≠ A → C.card=1) :
    B.card ≤ s ∧ (B∪A).card = 2*s-B.card+1 ∧
      (∀ v ∉ B∪A, ∀ w, G.Adj v w → w ∈ B) := by
  classical
  have hsum : (∑ C ∈ blocks,(C.card-1)/2) = (A.card-1)/2 := by
    apply sum_eq_single A
    · intro C hC hne
      rw [hsmall C hC hne]
      norm_num
    · exact fun h => False.elim (h hA)
  have hb := hc.budget
  rw [hsum] at hb
  have ho := hc.odd A hA
  have hcard : (B∪A).card = B.card+A.card := card_union_of_disjoint (hc.disjoint A hA).symm
  refine ⟨by omega,?_,?_⟩
  · obtain ⟨r,hr⟩ := ho
    omega
  · intro v hv w hadj
    have hvB : v ∉ B := fun h => hv (mem_union_left _ h)
    have hvA : v ∉ A := fun h => hv (mem_union_right _ h)
    obtain ⟨C,hC,hvC⟩ := (hc.cover v).mp hvB
    have hCA : C ≠ A := by intro he; exact hvA (he ▸ hvC)
    have hsingle := card_eq_one.mp (hsmall C hC hCA)
    obtain ⟨c,hcEq⟩ := hsingle
    have hvc : v=c := by simpa only [hcEq,mem_singleton] using hvC
    by_contra hwB
    obtain ⟨D,hD,hwD⟩ := (hc.cover w).mp hwB
    by_cases hDC : D=C
    · have hwc : w=c := by simpa only [hDC,hcEq,mem_singleton] using hwD
      exact G.irrefl ((hwc.trans hvc.symm) ▸ hadj)
    · exact hc.edges C hC D hD (fun h => hDC h.symm) v hvC w hwD hadj

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.NormalCore

-- BEGIN MODULE TMProof.CoreCount

namespace TuranMatching.Clique.TMFresh
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

def coreGraph (G : SimpleGraph V) (C : Finset V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ a ∈ C ∧ b ∈ C
  symm.symm a b h := by exact ⟨h.1.symm,h.2.2,h.2.1⟩
  loopless.irrefl a h := by exact G.irrefl h.1

theorem coreGraph_card (G : SimpleGraph V) (C : Finset V) :
    (coreGraph G C).edgeSet.ncard = (G.induce (C : Set V)).edgeSet.ncard := by
  classical
  have hs : (coreGraph G C).support ⊆ (C : Set V) := by
    intro v hv
    obtain ⟨w,hw⟩ := hv
    exact hw.2.1
  have he : (coreGraph G C).induce (C : Set V) = G.induce (C : Set V) := by
    ext a b
    exact ⟨fun h => h.1, fun h => ⟨h,a.property,b.property⟩⟩
  have hh := (coreGraph G C).card_edgeFinset_induce_of_support_subset hs
  simp only [← Set.ncard_coe_finset,coe_edgeFinset] at hh
  rw [he] at hh
  exact hh.symm

theorem edges_core_formula (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset V)
    (hind : ∀ a ∉ C, ∀ b ∉ C, ¬G.Adj a b) :
    (G.edgeSet.ncard : ℤ) = (G.induce (C : Set V)).edgeSet.ncard +
      ∑ a ∈ Cᶜ, (G.degree a : ℤ) := by
  classical
  let H := coreGraph G C
  let d : V → V → ℤ := fun a b => adjWeight G a b - adjWeight H a b
  have hsum := sum_cross_symmetric Cᶜ d (by
    intro a b
    simp [d,adjWeight,adj_comm]) (by
    intro a b hab
    by_cases ha : a ∈ C
    · have hb : b ∈ C := by simpa using (not_congr hab).mp (by simpa using ha)
      simp [d,adjWeight,H,coreGraph,ha,hb]
    · have hb : b ∉ C := by simpa using hab.mp (by simpa using ha)
      simp [d,adjWeight,H,coreGraph,ha,hind a ha b hb])
  have hz (a : V) (ha : a ∈ Cᶜ) : ∑ b, d a b = (G.degree a : ℤ) := by
    have ha' : a ∉ C := mem_compl.mp ha
    simp only [d,Finset.sum_sub_distrib,sum_adjWeight]
    have he : H.degree a = 0 := by
      rw [← Nat.cast_eq_zero (R := ℤ), ← sum_adjWeight H a]
      simp [adjWeight,H,coreGraph,ha']
    simp [he]
  have hG : (∑ a, (G.degree a : ℤ)) = 2*(G.edgeSet.ncard : ℤ) := by
    simpa only [← coe_edgeFinset,Set.ncard_coe_finset] using
      (show (∑ a, (G.degree a : ℤ))=2*(#G.edgeFinset : ℤ) by exact_mod_cast G.sum_degrees_eq_twice_card_edges)
  have hH : (∑ a, (H.degree a : ℤ)) = 2*(H.edgeSet.ncard : ℤ) := by
    simpa only [← coe_edgeFinset,Set.ncard_coe_finset] using
      (show (∑ a, (H.degree a : ℤ))=2*(#H.edgeFinset : ℤ) by exact_mod_cast H.sum_degrees_eq_twice_card_edges)
  simp only [d,Finset.sum_sub_distrib,sum_adjWeight] at hsum
  have hout : (∑ a ∈ Cᶜ, ((G.degree a : ℤ)-H.degree a)) = ∑ a ∈ Cᶜ,(G.degree a : ℤ) := by
    apply Finset.sum_congr rfl
    intro a ha
    simpa only [d,Finset.sum_sub_distrib,sum_adjWeight] using hz a ha
  simp only [Finset.sum_sub_distrib] at hout
  rw [hG,hH,hout] at hsum
  have hc := coreGraph_card G C
  change H.edgeSet.ncard = _ at hc
  rw [hc] at hsum
  linarith

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.CoreCount

-- BEGIN MODULE TMProof.CoreBound

namespace TuranMatching.Clique.TMFresh
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem clique_free_turan_bound (G : SimpleGraph V) {k : ℕ}
    (hk : G.CliqueFree (k+1)) : G.edgeSet.ncard ≤ turanNum (Fintype.card V) k := by
  classical
  have h := hk.card_edgeFinset_le
  dsimp only at h
  rw [← card_edgeFinset_turanGraph] at h
  simpa only [← Set.ncard_coe_finset,coe_edgeFinset,turanNum] using h

theorem core_bound (G : SimpleGraph V) {k : ℕ} (hk : G.CliqueFree (k+1))
    (B C : Finset V) (hBC : B ⊆ C)
    (hnei : ∀ v ∉ C, ∀ w, G.Adj v w → w ∈ B) :
    (G.edgeSet.ncard : ℤ) ≤ turanNum C.card k + (Fintype.card V-C.card : ℕ)*B.card := by
  classical
  have hi : ∀ a ∉ C, ∀ b ∉ C, ¬G.Adj a b := by
    intro a ha b hb hab
    exact hb (hBC (hnei a ha b hab))
  have hf := edges_core_formula G C hi
  have hd (a : V) (ha : a ∈ Cᶜ) : G.degree a ≤ B.card := by
    apply Finset.card_le_card
    intro b hb
    exact hnei a (mem_compl.mp ha) b (by simpa using hb)
  have hs : (∑ a ∈ Cᶜ,(G.degree a : ℤ)) ≤ (Cᶜ.card : ℤ)*B.card := by
    calc
      _ ≤ ∑ a ∈ Cᶜ,(B.card : ℤ) := Finset.sum_le_sum (fun a ha => by exact_mod_cast hd a ha)
      _ = _ := by simp
  have ht := clique_free_turan_bound (G.induce (C : Set V))
    ((cliqueFree_induce_iff G (C : Set V) (k+1)).mpr hk.cliqueFreeOn)
  have hcard : Fintype.card (C : Set V) = C.card := Fintype.card_coe C
  rw [hcard] at ht
  have ht' : ((G.induce (C : Set V)).edgeSet.ncard : ℤ) ≤ turanNum C.card k := by exact_mod_cast ht
  have hc : Cᶜ.card = Fintype.card V-C.card := Finset.card_compl C
  rw [hc] at hs
  linarith

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.CoreBound

-- BEGIN MODULE TMProof.ResidueCount

namespace TuranMatching.Clique.TMFresh
open Finset SimpleGraph

noncomputable def residueFiberEquiv (n k : ℕ) (hk : 0 < k) :
    {i : Fin n // (i : ℕ) % k = n % k} ≃ Fin (n / k) where
  toFun i := ⟨(i : ℕ) / k, by
    have hi := i.val.isLt
    have hr := i.property
    have hn := Nat.mod_add_div n k
    have hx := Nat.mod_add_div (i : ℕ) k
    by_contra hh
    have hle : n / k ≤ (i : ℕ) / k := by omega
    have hmul := Nat.mul_le_mul_left k hle
    omega⟩
  invFun q := ⟨⟨n % k + k * q, by
    have hm := Nat.mul_lt_mul_of_pos_left q.isLt hk
    have hn := Nat.mod_add_div n k
    omega⟩, by simp [Nat.add_mod]⟩
  left_inv i := by
    apply Subtype.ext
    apply Fin.ext
    change n % k + k * ((i : ℕ) / k) = (i : ℕ)
    have hr := i.property
    have hx := Nat.mod_add_div (i : ℕ) k
    omega
  right_inv q := by
    apply Fin.ext
    change (n % k + k * (q : ℕ)) / k = (q : ℕ)
    rw [Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt (Nat.mod_lt _ hk), zero_add]

theorem residue_fiber_count (n k : ℕ) (hk : 0 < k) :
    #({i : Fin n | (i : ℕ) % k = n % k} : Finset (Fin n)) = n / k := by
  have he := Fintype.card_congr (residueFiberEquiv n k hk)
  simpa only [Fintype.card_subtype, Fintype.card_fin] using he

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.ResidueCount

-- BEGIN MODULE TMProof.TuranIncrement

namespace TuranMatching.Clique.TMFresh
open Finset SimpleGraph

theorem turan_double_sum (n k : ℕ) :
    (∑ i : Fin n, ∑ j : Fin n, if (i : ℕ) % k ≠ (j : ℕ) % k then (1 : ℤ) else 0) =
      2 * (turanNum n k : ℤ) := by
  have he (i : Fin n) : (∑ j : Fin n, if (i : ℕ) % k ≠ (j : ℕ) % k then (1 : ℤ) else 0) =
      ((turanGraph n k).degree i : ℤ) := sum_adjWeight (turanGraph n k) i
  simp only [he]
  exact_mod_cast (turanGraph n k).sum_degrees_eq_twice_card_edges

theorem turan_increment (n k : ℕ) (hk : 0 < k) :
    (turanNum (n + 1) k : ℤ) = turanNum n k + n - (n / k : ℕ) := by
  have hf := residue_fiber_count n k hk
  have heq : (∑ i : Fin n, if (i : ℕ) % k = n % k then (1 : ℤ) else 0) = (n / k : ℕ) := by
    rw [Finset.sum_boole, hf]
  have hne : (∑ i : Fin n, if (i : ℕ) % k ≠ n % k then (1 : ℤ) else 0) =
      (n : ℤ) - (n / k : ℕ) := by
    have hs : (∑ i : Fin n, if (i : ℕ) % k ≠ n % k then (1 : ℤ) else 0) +
        (∑ i : Fin n, if (i : ℕ) % k = n % k then (1 : ℤ) else 0) = n := by
      rw [← Finset.sum_add_distrib]
      have hp (i : Fin n) : (if (i : ℕ) % k ≠ n % k then (1 : ℤ) else 0) +
          (if (i : ℕ) % k = n % k then (1 : ℤ) else 0) = 1 := by split_ifs <;> omega
      simp only [hp, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [heq] at hs
    linarith
  have hall := turan_double_sum (n + 1) k
  simp only [Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last] at hall
  simp only [ne_self_iff_false, if_false, add_zero, Finset.sum_add_distrib] at hall
  have hsym : (∑ i : Fin n, if n % k ≠ (i : ℕ) % k then (1 : ℤ) else 0) =
      ∑ i : Fin n, if (i : ℕ) % k ≠ n % k then (1 : ℤ) else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [ne_comm]
  rw [hsym, hne, turan_double_sum] at hall
  linarith

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.TuranIncrement

-- BEGIN MODULE TMProof.BigGraphCount

namespace TuranMatching.Clique.TMFresh
open Finset SimpleGraph

def bigColor (k s x : ℕ) : ℕ := if x < s then x % (k - 1) else k - 1

theorem big_double_sum (n k s : ℕ) :
    (∑ i : Fin n, ∑ j : Fin n, if bigColor k s i ≠ bigColor k s j then (1 : ℤ) else 0) =
      2 * (gNum n k s : ℤ) := by
  have he (i : Fin n) : (∑ j : Fin n, if bigColor k s i ≠ bigColor k s j then (1 : ℤ) else 0) =
      ((bigGraph n k s).degree i : ℤ) := sum_adjWeight (bigGraph n k s) i
  simp only [he]
  exact_mod_cast (bigGraph n k s).sum_degrees_eq_twice_card_edges

theorem big_increment (n k s : ℕ) (hk : 2 ≤ k) (hs : s ≤ n) :
    (gNum (n + 1) k s : ℤ) = gNum n k s + s := by
  have hkpos : 0 < k - 1 := by omega
  have hp (i : Fin n) : (if bigColor k s i ≠ bigColor k s n then (1 : ℤ) else 0) =
      if (i : ℕ) < s then 1 else 0 := by
    by_cases hi : (i : ℕ) < s
    · have hm := Nat.mod_lt (i : ℕ) hkpos
      simp [bigColor, hi, Nat.not_lt.mpr hs, ne_of_lt hm]
    · simp [bigColor, hi, Nat.not_lt.mpr hs]
  have hcross : (∑ i : Fin n, if bigColor k s i ≠ bigColor k s n then (1 : ℤ) else 0) = s := by
    simp only [hp, Finset.sum_boole, Fin.card_filter_val_lt, min_eq_right hs]
  have hsym : (∑ i : Fin n, if bigColor k s n ≠ bigColor k s i then (1 : ℤ) else 0) =
      ∑ i : Fin n, if bigColor k s i ≠ bigColor k s n then (1 : ℤ) else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [ne_comm]
  have hall := big_double_sum (n + 1) k s
  simp only [Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last] at hall
  simp only [ne_self_iff_false, if_false, add_zero, Finset.sum_add_distrib] at hall
  rw [hsym, hcross, big_double_sum] at hall
  linarith

theorem big_base (k s : ℕ) : gNum s k s = turanNum s (k - 1) := by
  have he : bigGraph s k s = turanGraph s (k - 1) := by
    ext a b
    simp [bigGraph, bigClass, turanGraph]
  exact edge_card_congr he

theorem gNum_formula (n k s : ℕ) (hk : 2 ≤ k) (hs : s ≤ n) :
    (gNum n k s : ℤ) = turanNum s (k - 1) + (s : ℤ) * (n - s : ℕ) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hs
  induction d with
  | zero => simp [big_base]
  | succ d ih =>
    specialize ih (by omega)
    have he := big_increment (s + d) k s hk (by omega)
    simp only [Nat.add_sub_cancel_left] at ih ⊢
    simp only [Nat.cast_add, Nat.cast_one] at ih ⊢
    rw [show s + (d + 1) = (s + d) + 1 by omega, he, ih]
    ring

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.BigGraphCount

-- BEGIN MODULE TMProof.TuranBalanced

namespace TuranMatching.Clique.TMFresh
open Finset SimpleGraph

theorem turan_add_int (n k : ℕ) :
    (turanNum (n + k) k : ℤ) = turanNum n k + (n : ℤ) * (k - 1 : ℕ) + k.choose 2 := by
  exact_mod_cast (card_edgeFinset_turanGraph_add (n := n) (r := k))

theorem turan_balanced_aux (q r k : ℕ) (hk : 2 ≤ k) (hr : r < k - 1) :
    (turanNum ((k - 1) * q + r + q) k : ℤ) =
      turanNum ((k - 1) * q + r) (k - 1) + (((k - 1) * q + r : ℕ) : ℤ) * q := by
  have hrk : r < k := by omega
  have hc : k.choose 2 = (k - 1).choose 2 + (k - 1) := by
    have h := Nat.choose_succ_succ (k - 1) 1
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ k), Nat.choose_one_right, Nat.add_comm] using h
  have hkz : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by omega
  have hkzz : ((k - 1 - 1 : ℕ) : ℤ) = (k : ℤ) - 2 := by omega
  induction q with
  | zero =>
    simp [turanNum, card_edgeFinset_turanGraph, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hrk]
  | succ q ih =>
    let a := (k - 1) * q + r
    have h1 : (k - 1) * (q + 1) + r = a + (k - 1) := by dsimp [a]; ring
    have h2 : (k - 1) * (q + 1) + r + (q + 1) = (a + q) + k := by
      rw [h1]
      omega
    change (turanNum ((k - 1) * (q + 1) + r + (q + 1)) k : ℤ) = _
    rw [h2, h1, turan_add_int, turan_add_int]
    change (turanNum (a + q) k : ℤ) = turanNum a (k - 1) + (a : ℤ) * q at ih
    rw [ih]
    push_cast
    rw [hc]
    push_cast
    rw [hkz, hkzz]
    ring

theorem turan_balanced_bridge (s k : ℕ) (hk : 2 ≤ k) :
    (turanNum (s + s / (k - 1)) k : ℤ) =
      turanNum s (k - 1) + (s : ℤ) * (s / (k - 1) : ℕ) := by
  have hp : 0 < k - 1 := by omega
  have he := turan_balanced_aux (s / (k - 1)) (s % (k - 1)) k hk (Nat.mod_lt s hp)
  simpa only [Nat.div_add_mod] using he

theorem gNum_balanced_formula (n k s : ℕ) (hk : 2 ≤ k) (hs : s ≤ n) :
    (gNum n k s : ℤ) = turanNum (s + s / (k - 1)) k +
      (s : ℤ) * ((n : ℤ) - s - (s / (k - 1) : ℕ)) := by
  rw [gNum_formula n k s hk hs, turan_balanced_bridge s k hk]
  have hn : ((n - s : ℕ) : ℤ) = (n : ℤ) - s := by omega
  rw [hn]
  ring

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.TuranBalanced

-- BEGIN MODULE TMProof.DiscreteEndpoints

namespace TuranMatching.Clique.TMFresh
open Finset SimpleGraph

theorem discrete_strict_convex_max (f : ℕ → ℤ) (N : ℕ)
    (hc : ∀ i, i + 2 ≤ N → f (i + 1) - f i < f (i + 2) - f (i + 1)) :
    ∀ b, b ≤ N → f b ≤ max (f 0) (f N) := by
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (Finset.range (N + 1)) f ⟨0, by simp⟩
  have hmN : m ≤ N := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hm
  have hend : m = 0 ∨ m = N := by
    by_contra hn
    have hm0 : 0 < m := by omega
    have hmLt : m < N := by omega
    have hp := hmax (m - 1) (by simp only [Finset.mem_range]; omega)
    have hn' := hmax (m + 1) (by simp only [Finset.mem_range]; omega)
    have hh := hc (m - 1) (by omega)
    have h1 : m - 1 + 1 = m := by omega
    have h2 : m - 1 + 2 = m + 1 := by omega
    rw [h1, h2] at hh
    omega
  intro b hb
  have hbm := hmax b (by simp only [Finset.mem_range]; omega)
  rcases hend with rfl | rfl
  · exact hbm.trans (le_max_left _ _)
  · exact hbm.trans (le_max_right _ _)

theorem turan_delta_mono (n k : ℕ) (hk : 0 < k) :
    (turanNum (n + 1) k : ℤ) - turanNum n k ≤
      turanNum (n + 2) k - turanNum (n + 1) k := by
  have hq : (n + 1) / k ≤ n / k + 1 := by
    calc
      _ ≤ (n + k) / k := Nat.div_le_div_right (by omega)
      _ = n / k + 1 := Nat.add_div_right _ hk
  have h1 := turan_increment n k hk
  have h2 := turan_increment (n + 1) k hk
  simp only [Nat.add_assoc, Nat.reduceAdd, Nat.cast_add, Nat.cast_one] at h2
  have hqz : (((n + 1) / k : ℕ) : ℤ) ≤ (n / k : ℕ) + 1 := by exact_mod_cast hq
  omega

theorem fCase4_strict_convex (n k s b : ℕ) (hk : 2 ≤ k) (hb : b + 2 ≤ s) :
    fCase4 n k s (b + 1) - fCase4 n k s b <
      fCase4 n k s (b + 2) - fCase4 n k s (b + 1) := by
  let N := 2 * s - b - 2
  have h0 : 2 * s - b + 1 = N + 3 := by dsimp [N]; omega
  have h1 : 2 * s - (b + 1) + 1 = N + 2 := by dsimp [N]; omega
  have h2 : 2 * s - (b + 2) + 1 = N + 1 := by dsimp [N]; omega
  have hdelta := turan_delta_mono (N + 1) k (by omega)
  simp only [Nat.add_assoc] at hdelta
  simp only [fCase4, h0, h1, h2, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  nlinarith

theorem balanced_quotient (s k : ℕ) (hk : 2 ≤ k) :
    (s + s / (k - 1)) / k = s / (k - 1) := by
  let m := s / (k - 1)
  let r := s % (k - 1)
  have hr : r < k := by dsimp [r]; have hh := Nat.mod_lt s (show 0 < k - 1 by omega); omega
  have hd : (k - 1) * m + r = s := Nat.div_add_mod _ _
  have he : s + m = k * m + r := by
    rw [← hd]
    have hkk : k = k - 1 + 1 := by omega
    nth_rw 2 [hkk]
    ring
  change (s + m) / k = m
  rw [he, Nat.mul_add_div (show 0 < k by omega), Nat.div_eq_of_lt hr, add_zero]

theorem fCase4_endpoint_le (n k s : ℕ) (hk : 2 ≤ k) (hn : 2 * s + 1 ≤ n) :
    fCase4 n k s (s - s / (k - 1)) ≤ (gNum n k s : ℤ) := by
  let m := s / (k - 1)
  have hm : m ≤ s := Nat.div_le_self _ _
  have hidx_aux (a b : ℕ) (hb : b ≤ a) : 2 * a - (a - b) + 1 = a + b + 1 := by omega
  have hidx : 2 * s - (s - m) + 1 = s + m + 1 := hidx_aux s m hm
  have hcast : ((s - m : ℕ) : ℤ) = (s : ℤ) - m := Nat.cast_sub hm
  have ht := turan_increment (s + m) k (show 0 < k by omega)
  have hquot : (s + m) / k = m := balanced_quotient s k hk
  rw [hquot] at ht
  have hform := gNum_balanced_formula n k s hk (by omega)
  change fCase4 n k s (s - m) ≤ _
  simp only [fCase4, hidx, hcast]
  rw [ht, hform]
  have hnon : 0 ≤ (m : ℤ) * ((n : ℤ) - s - m - 1) :=
    mul_nonneg (Nat.cast_nonneg _) (by omega)
  dsimp only [m] at hnon ⊢
  simp only [Nat.cast_add]
  nlinarith

theorem fCase4_endpoint_bound (n k s b : ℕ) (hk : 2 ≤ k) (hn : 2 * s + 1 ≤ n)
    (hb : b ≤ s - s / (k - 1)) :
    fCase4 n k s b ≤ max (turanNum (2 * s + 1) k : ℤ) (gNum n k s : ℤ) := by
  have hh := discrete_strict_convex_max (fCase4 n k s) (s - s / (k - 1))
    (fun i hi => fCase4_strict_convex n k s i hk (hi.trans (Nat.sub_le _ _))) b hb
  have hzero : fCase4 n k s 0 = (turanNum (2 * s + 1) k : ℤ) := by simp [fCase4]
  rw [hzero] at hh
  exact hh.trans (max_le_max le_rfl (fCase4_endpoint_le n k s hk hn))

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.DiscreteEndpoints

-- BEGIN MODULE TMProof.NormalBound

namespace TuranMatching.Clique.TMFresh
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem normal_bound (G : SimpleGraph V) {k s : ℕ} (hk : 2 ≤ k)
    (hn : 2*s+1 ≤ Fintype.card V) (hcl : G.CliqueFree (k+1))
    (B C : Finset V) (hBC : B ⊆ C) (hb : B.card ≤ s)
    (hsize : C.card=2*s-B.card+1)
    (hnei : ∀ v ∉ C, ∀ w, G.Adj v w → w ∈ B) :
    (G.edgeSet.ncard : ℤ) ≤ max (turanNum (2*s+1) k : ℤ) (gNum (Fintype.card V) k s : ℤ) := by
  classical
  let n := Fintype.card V
  let b := B.card
  let m := s/(k-1)
  have hm : m ≤ s := Nat.div_le_self _ _
  by_cases hcase : b ≤ s-m
  · have he := core_bound G hcl B C hBC hnei
    have hC : C.card ≤ n := Finset.card_le_univ C
    have hz : ((n-C.card : ℕ) : ℤ) = (n : ℤ)-2*s+b-1 := by dsimp [n,b] at *; omega
    have he' : (G.edgeSet.ncard : ℤ) ≤ fCase4 n k s b := by
      rw [hz,hsize] at he
      simpa only [fCase4,n,b,mul_comm] using he
    exact he'.trans (fCase4_endpoint_bound n k s b hk hn hcase)
  · have hsz : C.card ≤ s+m := by dsimp [b] at hcase; omega
    have hsn : s+m ≤ (univ : Finset V).card := by rw [card_univ]; omega
    obtain ⟨D,hCD,_,hDcard⟩ := exists_subsuperset_card_eq (subset_univ C) hsz hsn
    have hBD : B ⊆ D := hBC.trans hCD
    have hneD : ∀ v ∉ D, ∀ w, G.Adj v w → w ∈ B := by
      intro v hv w ha
      exact hnei v (fun h => hv (hCD h)) w ha
    have he := core_bound G hcl B D hBD hneD
    rw [hDcard] at he
    have hz : ((n-(s+m) : ℕ) : ℤ) = (n : ℤ)-s-m := by dsimp [n] at *; omega
    have hnon : 0 ≤ (n : ℤ)-s-m := by dsimp [n] at *; omega
    have hb' : (B.card : ℤ) ≤ s := by exact_mod_cast hb
    have hmul := mul_le_mul_of_nonneg_left hb' hnon
    have hg := gNum_balanced_formula n k s hk (by omega)
    have he' : (G.edgeSet.ncard : ℤ) ≤ (gNum n k s : ℤ) := by
      change (G.edgeSet.ncard : ℤ) ≤ turanNum (s+m) k + (n-(s+m) : ℕ)*B.card at he
      rw [hz] at he
      change (gNum n k s : ℤ) = turanNum (s+m) k + (s : ℤ)*((n : ℤ)-s-m) at hg
      nlinarith
    exact he'.trans (le_max_right _ _)

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.NormalBound

-- BEGIN MODULE TMProof.UpperBound

namespace TuranMatching.Clique.TMFresh
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem upper_bound (G : SimpleGraph V) {k s : ℕ} (hk : 2 ≤ k)
    (hn : 2*s+1 ≤ Fintype.card V) (hcl : G.CliqueFree (k+1))
    (hmatch : matchingNumber G ≤ s) :
    G.edgeSet.ncard ≤ max (turanNum (2*s+1) k) (gNum (Fintype.card V) k s) := by
  classical
  obtain ⟨B,blocks,hc⟩ := exact_odd_certificate G s hmatch hn
  obtain ⟨P,bs,hopt,_⟩ := exists_optimal_certificate G B blocks k s hc hcl
  obtain ⟨H,classes,I,hH,_,_,hw,hcap⟩ := hopt.repaired (by omega)
  obtain ⟨A,hA,hsmall⟩ := choose_large_block hH.certificate hn
    (fun A hA C hC ha hc => hH.no_two_large hw hcap hA hC ha hc)
  obtain ⟨hb,hsize,hnei⟩ := normal_core_properties hH.certificate hA hsmall
  have hnorm := normal_bound H hk hn hH.cliqueFree B (B∪A) subset_union_left hb hsize hnei
  have he : G.edgeSet.ncard ≤ H.edgeSet.ncard := hH.edge_max G blocks hc hcl
  have he' : (G.edgeSet.ncard : ℤ) ≤ H.edgeSet.ncard := by exact_mod_cast he
  have hh := he'.trans hnorm
  exact_mod_cast hh

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.UpperBound

-- BEGIN MODULE TMProof.Attainment

namespace TuranMatching.Clique.TMFresh
open SimpleGraph Finset

 theorem bigGraph_cliqueFree (n k s : ℕ) (hk : 2 ≤ k) :
    (bigGraph n k s).CliqueFree (k + 1) := by
  classical
  have hb (i : Fin n) : bigClass k s i < k := by
    unfold bigClass
    split_ifs
    · have hm := Nat.mod_lt (i : ℕ) (show 0 < k - 1 by omega)
      omega
    · omega
  intro K hK
  let f : K → Fin k := fun i => ⟨bigClass k s (i : Fin n), hb (i : Fin n)⟩
  have hi : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    by_contra hn
    have hadj := hK.isClique a.property b.property hn
    exact hadj (congrArg Fin.val he)
  have hc := Fintype.card_le_of_injective f hi
  simp only [Fintype.card_coe, Fintype.card_fin] at hc
  have he := hK.card_eq
  omega

 theorem bigGraph_matching (n k s : ℕ) : matchingNumber (bigGraph n k s) ≤ s := by
  classical
  let C : Finset (Fin n) := univ.filter (fun i => (i : ℕ) < s)
  have hc : matchingNumber (bigGraph n k s) ≤ C.card :=
    matchingNumber_le_cover (bigGraph n k s) C (by
      intro u v huv
      by_cases hu : (u : ℕ) < s
      · exact Or.inl (by simp [C, hu])
      · right
        by_contra hv
        have hv' : ¬(v : ℕ) < s := by simpa [C] using hv
        exact huv (by simp [bigClass, hu, hv']))
  have hcard : C.card ≤ s := by
    simpa only [C, Fin.card_filter_val_lt] using (min_le_right n s)
  exact hc.trans hcard

 theorem matchingNumber_map_le {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (f : V ↪ W) : matchingNumber (G.map f) ≤ Fintype.card V / 2 := by
  classical
  apply (matchingNumber_le_iff (G.map f) _).mpr
  intro M hM
  have hv : M.verts ⊆ Set.range f := by
    intro u hu
    obtain ⟨v, huv, _⟩ := hM hu
    obtain ⟨a, b, _, ha, _⟩ := (SimpleGraph.map_adj f G u v).mp huv.adj_sub
    exact ⟨a, ha⟩
  have hc := Set.ncard_le_ncard hv
  rw [matching_vertex_card M hM, Set.ncard_range_of_injective f.injective] at hc
  simpa only [Nat.card_eq_fintype_card] using (show M.edgeSet.ncard ≤ Nat.card V / 2 by omega)

noncomputable def paddedTuran (n k s : ℕ) (hn : 2 * s + 1 ≤ n) : SimpleGraph (Fin n) :=
  (turanGraph (2 * s + 1) k).map (Fin.castLEEmb hn)

 theorem paddedTuran_admissible (n k s : ℕ) (hk : 2 ≤ k) (hn : 2 * s + 1 ≤ n) :
    Admissible k s (paddedTuran n k s hn) := by
  constructor
  · exact SimpleGraph.cliqueFree_map_iff.mpr (turanGraph_cliqueFree (by omega : 0 < k))
  · have hh := matchingNumber_map_le (turanGraph (2 * s + 1) k) (Fin.castLEEmb hn)
    simp only [Fintype.card_fin] at hh
    change matchingNumber (paddedTuran n k s hn) ≤ s
    exact hh.trans (by omega)

 theorem paddedTuran_edges (n k s : ℕ) (hn : 2 * s + 1 ≤ n)
    [DecidableRel (paddedTuran n k s hn).Adj] :
    #(paddedTuran n k s hn).edgeFinset = turanNum (2 * s + 1) k := by
  classical
  have he := card_edgeFinset_map (Fin.castLEEmb hn) (turanGraph (2 * s + 1) k)
  simp only [← Set.ncard_coe_finset, coe_edgeFinset] at he
  unfold paddedTuran turanNum
  rw [← Set.ncard_coe_finset, coe_edgeFinset, ← Set.ncard_coe_finset, coe_edgeFinset]
  exact he

 theorem attaining_graph (n k s : ℕ) (hk : 2 ≤ k) (hn : 2 * s + 1 ≤ n) :
    ∃ G : SimpleGraph (Fin n), ∃ _ : DecidableRel G.Adj,
      Admissible k s G ∧ #G.edgeFinset = max (turanNum (2 * s + 1) k) (gNum n k s) := by
  classical
  by_cases h : turanNum (2 * s + 1) k ≤ gNum n k s
  · refine ⟨bigGraph n k s, inferInstance, ⟨bigGraph_cliqueFree n k s hk, bigGraph_matching n k s⟩, ?_⟩
    exact (max_eq_right h).symm
  · refine ⟨paddedTuran n k s hn, inferInstance, paddedTuran_admissible n k s hk hn, ?_⟩
    rw [paddedTuran_edges, max_eq_left (by omega)]

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.Attainment

-- BEGIN MODULE TMProof.NativeConclusion

namespace TuranMatching.Clique.TMFresh
open SimpleGraph Finset

theorem native_theorem_1_1 (n k s : ℕ) (hk : 2 ≤ k) (hn : 2 * s + 1 ≤ n) :
    (∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], Admissible k s G →
        #G.edgeFinset ≤ max (turanNum (2 * s + 1) k) (gNum n k s)) ∧
    ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj), Admissible k s G ∧
        #G.edgeFinset = max (turanNum (2 * s + 1) k) (gNum n k s) := by
  constructor
  · intro G inst hG
    have hh := upper_bound G hk (by simpa using hn) hG.1 hG.2
    simpa only [Fintype.card_fin, ← Set.ncard_coe_finset, coe_edgeFinset] using hh
  · exact attaining_graph n k s hk hn

end TuranMatching.Clique.TMFresh
-- END MODULE TMProof.NativeConclusion

-- BEGIN MODULE Canonical
open SimpleGraph Finset

namespace TuranMatching.Clique

theorem theorem_1_1 (n k s : ℕ) (hk : 2 ≤ k) (hn : 2 * s + 1 ≤ n) :
    (∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], Admissible k s G →
        #G.edgeFinset ≤ max (turanNum (2 * s + 1) k) (gNum n k s)) ∧
    ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj), Admissible k s G ∧
        #G.edgeFinset = max (turanNum (2 * s + 1) k) (gNum n k s) := by
  exact TMFresh.native_theorem_1_1 n k s hk hn

end TuranMatching.Clique
-- END MODULE Canonical

open SimpleGraph Finset TuranMatching.Clique

theorem solution (n k s : ℕ) (hk : 2 ≤ k) (hn : 2 * s + 1 ≤ n) :
    (∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], Admissible k s G →
        #G.edgeFinset ≤ max (turanNum (2 * s + 1) k) (gNum n k s)) ∧
    ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj), Admissible k s G ∧
        #G.edgeFinset = max (turanNum (2 * s + 1) k) (gNum n k s) := by
  exact TuranMatching.Clique.theorem_1_1 n k s hk hn
