-- Prove2me | solution 1 for SingleExpBisect.Main.lemma_5_1_combinatorial
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T10:17:46.933181+00:00
-- url     : https://prove2.me/submissions/4927c09a-3654-44bc-9440-557d5c43b2b7

/- Cut-edge, submodularity, and attainment lemmas adapted from Secousses, Prove2Me submission 797eedb1-a223-4590-b528-4b3d16d0ab3c (Apache-2.0). -/
import Mathlib
import Theorems.Thm_SingleExpBisect_Main_lemma_2_1_combinatorial
import Definitions.Def_SingleExpBisect_Main_Graphs

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

private lemma max_size {n : ℕ} {P : Finset (Fin n) → Prop} {A : Finset (Fin n)}
    (hA : P A) : ∃ B, P B ∧ ∀ C, P C → B ⊆ C → B = C := by
  classical
  let f := Finset.univ.filter P
  have hf (D) : D ∈ f ↔ P D := by simp [f]
  obtain ⟨B,hB,hh⟩ := f.exists_max_image Finset.card ⟨A,(hf _).mpr hA⟩
  exact ⟨B,(hf _).mp hB,fun C hC hBC => Finset.eq_of_subset_of_card_le hBC (hh C ((hf C).mpr hC))⟩

private lemma split_cut {n : ℕ} (G : SimpleGraph (Fin n)) (A B : Finset (Fin n))
    (hd : Disjoint A B) (hc : ∀ u ∈ A, ∀ v ∈ B, ¬ G.Adj u v) :
    cutSize G (A ∪ B) = cutSize G A + cutSize G B := by
  classical
  have eq : cutEdges G (A ∪ B) = cutEdges G A ∪ cutEdges G B := by
    ext e; induction e using Sym2.ind with
    | _ u v =>
      simp only [mem_cutEdges_mk, Finset.mem_union]
      have h1 := hc u
      have h2 := hc v
      have h3 : G.Adj u v → G.Adj v u := SimpleGraph.Adj.symm
      by_cases h : G.Adj u v
      · have e1 : u ∈ A → v ∉ B := fun hA hB => h1 hA v hB h
        have e2 : v ∈ A → u ∉ B := fun hA hB => h2 hA u hB h.symm
        tauto
      · tauto
  have hdis : Disjoint (cutEdges G A) (cutEdges G B) := by
    apply Finset.disjoint_left.mpr
    intro e h1 h2
    induction e using Sym2.ind with
    | _ u v =>
      obtain ⟨ha,ho⟩ := (mem_cutEdges_mk ..).mp h1
      obtain ⟨_,hp⟩ := (mem_cutEdges_mk ..).mp h2
      have e1 : u ∈ A → v ∉ B := fun hu hv => hc u hu v hv ha
      have e2 : v ∈ A → u ∉ B := fun hv hu => hc v hv u hu ha.symm
      have e3 : u ∈ A → u ∉ B := fun h => Finset.disjoint_left.mp hd h
      have e4 : v ∈ A → v ∉ B := fun h => Finset.disjoint_left.mp hd h
      tauto
  unfold cutSize; rw [eq, Finset.card_union_of_disjoint hdis]

private lemma closed_piece {n : ℕ} (G : SimpleGraph (Fin n)) (R : Finset (Fin n)) (v : Fin n) (hv : v ∈ R) :
    ∃ K ⊆ R, v ∈ K ∧ (G.induce (K : Set _)).Connected ∧
      ∀ u ∈ K, ∀ z ∈ R, G.Adj u z → z ∈ K := by
  classical
  have hs : (G.induce (({v} : Finset _) : Set _)).Connected := by
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨⟨v,Finset.mem_singleton_self _⟩,?_⟩; rintro ⟨x,hx⟩
    obtain rfl := Finset.mem_singleton.mp hx; exact .refl _
  obtain ⟨K,⟨hk,hv',hc⟩,hm⟩ := max_size (P:=fun K => K ⊆ R ∧ v ∈ K ∧ (G.induce (K : Set _)).Connected)
    ⟨Finset.singleton_subset_iff.mpr hv,Finset.mem_singleton_self v,hs⟩
  refine ⟨K,hk,hv',hc,?_⟩
  intro u hu z hz hed
  have hh : (G.induce ((K : Set _) ∪ {z})).Connected :=
    SimpleGraph.connected_induce_union hc.preconnected SimpleGraph.Preconnected.of_subsingleton hu (Set.mem_singleton _) hed
  have eq : (↑(insert z K) : Set _) = (K : Set _) ∪ {z} := by ext;simp [or_comm]
  have h' := hm (insert z K) ⟨Finset.insert_subset hz hk,Finset.mem_insert_of_mem hv',eq ▸ hh⟩ (Finset.subset_insert ..)
  exact h' ▸ Finset.mem_insert_self _ _

private lemma profit_piece {n : ℕ} (G : SimpleGraph (Fin n)) (B R : Finset (Fin n))
    (hprof : cutSize G R < (R ∩ B).card) :
    ∃ K ⊆ R, (G.induce (K : Set _)).Connected ∧ cutSize G K ≤ cutSize G R ∧ cutSize G K < (K ∩ B).card := by
  classical
  induction R using Finset.strongInductionOn with
  | _ R ih =>
    have hp : (R ∩ B).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨v,hv⟩ := hp
    obtain ⟨K,hK,hvK,hc,hcl⟩ := closed_piece G R v (Finset.mem_inter.mp hv).1
    let J := R \ K
    have dj : Disjoint K J := Finset.disjoint_left.mpr fun _ hk hj => (Finset.mem_sdiff.mp hj).2 hk
    have he : K ∪ J = R := Finset.union_sdiff_of_subset hK
    have cout := split_cut G K J dj (fun u hu z hz ha => (Finset.mem_sdiff.mp hz).2 (hcl u hu z (Finset.mem_sdiff.mp hz).1 ha))
    rw [he] at cout
    by_cases hk : cutSize G K < (K ∩ B).card
    · exact ⟨K,hK,hc,by omega,hk⟩
    · have sz : (K ∩ B).card + (J ∩ B).card = (R ∩ B).card := by
        rw [←Finset.card_union_of_disjoint (dj.mono Finset.inter_subset_left Finset.inter_subset_left),
          ←Finset.union_inter_distrib_right,he]
      have hJ : J ⊂ R := Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset,fun e =>
        (Finset.mem_sdiff.mp (e.symm ▸ (Finset.mem_inter.mp hv).1)).2 hvK⟩
      obtain ⟨D,hd,hDC,hco,hprof'⟩ := ih J hJ (by omega)
      exact ⟨D,hd.trans hJ.le,hDC,by omega,hprof'⟩

private lemma compl_cut {n : ℕ} (H : SimpleGraph (Fin n)) (A : Finset (Fin n)) :
    cutSize H Aᶜ = cutSize H A := by
  unfold cutSize;congr 1
  ext e;induction e using Sym2.ind with
  | _ a b => simp only [mem_cutEdges_mk,Finset.mem_compl];tauto

private lemma orient_break {n : ℕ} (H : SimpleGraph (Fin n)) (X B : Finset (Fin n)) (k : ℕ)
    (hx : X.card ≤ 2*k+1) (h : ¬ IsEdgeUnbreakable H Finset.univ B (2*k) k) :
    ∃ A : Finset (Fin n), cutSize H A ≤ k ∧ 2*k < (A ∩ B).card ∧ (A ∩ X).card ≤ k := by
  classical
  unfold IsEdgeUnbreakable at h;push_neg at h
  obtain ⟨A,_,hc,hB,hB'⟩ := h
  by_cases hX : (A ∩ X).card ≤ k
  · exact ⟨A,hc,hB,hX⟩
  · have e (D : Finset (Fin n)) : Aᶜ ∩ D = D \ A := by ext i;simp [and_comm]
    have hs := Finset.card_sdiff_add_card_inter X A
    rw [Finset.inter_comm X A] at hs
    exact ⟨Aᶜ,(compl_cut H A).le.trans hc,(e B).symm ▸ hB',by rw [e];omega⟩

private lemma delete_cross {n : ℕ} (H : SimpleGraph (Fin n)) (A X : Finset (Fin n)) :
    cutSize (restrictMinus H (Finset.univ \ (X \ (X \ A))) ∅) (A \ X) ≤ cutSize H A := by
  apply Finset.card_le_card
  intro e;induction e using Sym2.ind with
  | _ a b =>
    simp only [mem_cutEdges_mk,Finset.mem_sdiff]
    intro ⟨hadj,hcross⟩
    obtain ⟨hg,ha,hb,_⟩ := hadj
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at ha hb
    exact ⟨hg,by tauto⟩

private theorem find_important {n : ℕ} (H : SimpleGraph (Fin n)) (X B : Finset (Fin n)) (k : ℕ)
    (hX : X ⊆ B) (hx : X.card ≤ 2*k+1) (hbreak : ¬ IsEdgeUnbreakable H Finset.univ B (2*k) k) :
    ∃ (Z : Finset (Fin n)) (r : Fin n) (D : Finset (Fin n)),
      Z ⊆ X ∧ (X \ Z).card ≤ k ∧ r ∈ B \ X ∧
      let H' := restrictMinus H (Finset.univ \ (X \ Z)) ∅
      IsImportantConnCut H' {r} Z D ∧ cutSize H' D ≤ k ∧ cutSize H' D < (D ∩ B).card := by
  classical
  obtain ⟨A,hc,hb,hax⟩ := orient_break H X B k hx hbreak
  let Z := X \ A
  let H' := restrictMinus H (Finset.univ \ (X \ Z)) ∅
  have hz : X \ Z = A ∩ X := by ext i;simp only [Z,Finset.mem_inter,Finset.mem_sdiff];tauto
  have hco : cutSize H' (A \ X) ≤ k := (delete_cross H A X).trans hc
  have hsz : k < ((A \ X) ∩ B).card := by
    have h := Finset.card_sdiff_add_card_inter (A ∩ B) X
    have e1 : (A ∩ B) \ X = (A \ X) ∩ B := by ext;simp;tauto
    have e2 : (A ∩ B) ∩ X = A ∩ X := by ext i;simp only [Finset.mem_inter];constructor <;> aesop
    rw [e1,e2] at h;omega
  obtain ⟨K,hK,hconn,hk,hprof⟩ := profit_piece H' B (A \ X) (lt_of_le_of_lt hco hsz)
  obtain ⟨r,hr⟩ := Finset.card_pos.mp (Nat.zero_lt_of_lt hprof)
  obtain ⟨hrK,hrB⟩ := Finset.mem_inter.mp hr
  have hKZ : Disjoint K Z := Finset.disjoint_left.mpr (fun u hu hz => (Finset.mem_sdiff.mp (hK hu)).2 (Finset.mem_sdiff.mp hz).1)
  have hsrc : (H'.induce (({r} : Finset _) : Set _)).Connected := by
    rw [SimpleGraph.connected_iff_exists_forall_reachable];refine ⟨⟨r,Finset.mem_singleton_self _⟩,?_⟩
    rintro ⟨u,hu⟩;obtain rfl := Finset.mem_singleton.mp hu;exact .refl _
  have hrK' := Finset.singleton_subset_iff.mpr hrK
  obtain ⟨D,hi,hd,hcost⟩ := (lemma_2_1_combinatorial n H' {r} Z (hKZ.mono_left hrK') hsrc).1 K ⟨hrK',hKZ,hconn⟩
  exact ⟨Z,r,D,Finset.sdiff_subset,hz ▸ hax,Finset.mem_sdiff.mpr ⟨hrB,(Finset.mem_sdiff.mp (hK hrK)).2⟩,
    hi,hcost.trans (hk.trans hco),lt_of_le_of_lt hcost (lt_of_lt_of_le hprof
      (Finset.card_le_card (Finset.inter_subset_inter_right hd)))⟩

private lemma comp_closed {n : ℕ} {G : SimpleGraph (Fin n)} {X K : Finset (Fin n)}
    (hc : IsComponent G X K) {u v : Fin n} (hu : u ∈ K) (hv : v ∈ X) (ha : G.Adj u v) : v ∈ K := by
  classical
  have H : (G.induce ((K : Set (Fin n)) ∪ {v})).Connected := by
    apply SimpleGraph.connected_induce_union hc.2.1.preconnected _ hu (Set.mem_singleton v) ha
    exact SimpleGraph.Preconnected.of_subsingleton
  have HH : (G.induce (↑(insert v K) : Set (Fin n))).Connected := by
    have hset : (↑(insert v K) : Set (Fin n)) = (K : Set _) ∪ {v} := by ext; simp [or_comm]
    rw [hset]
    exact H
  have hx : insert v K ⊆ X := Finset.insert_subset hv hc.1
  have he := hc.2.2 (insert v K) (Finset.subset_insert _ _) hx HH
  exact he ▸ Finset.mem_insert_self v K


private lemma edge_grow {n : ℕ} (G : SimpleGraph (Fin n)) {X C : Finset (Fin n)}
    (h : X ⊂ C) (hx : X.Nonempty) (hc : (G.induce (C : Set _)).Connected) :
    ∃ a ∈ X, ∃ b ∈ C, b ∉ X ∧ G.Adj a b := by
  classical
  obtain ⟨a,ha⟩ := hx
  obtain ⟨b,hb,hbn⟩ := Finset.exists_of_ssubset h
  obtain ⟨p⟩ := hc ⟨a,h.le ha⟩ ⟨b,hb⟩
  obtain ⟨e,_,he,he'⟩ := p.exists_boundary_dart {u | u.val ∈ X} ha hbn
  exact ⟨e.fst.val,he,e.snd.val,e.snd.property,he',e.adj⟩

private lemma nbr_mem {n : ℕ} (H : SimpleGraph (Fin n)) (K : Finset (Fin n)) (v : Fin n) :
    v ∈ nbr H K ↔ v ∉ K ∧ ∃ u ∈ K, H.Adj u v := by simp [nbr]

private lemma nbr_component {n : ℕ} (H : SimpleGraph (Fin n)) (B K : Finset (Fin n))
    (hk : IsComponent H (Finset.univ \ B) K) : nbr H K ⊆ B := by
  intro v hv
  obtain ⟨hn,u,hu,h⟩ := (nbr_mem ..).mp hv
  by_contra hno
  exact hn (comp_closed hk hu (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hno⟩) h)

private lemma enclosure {n : ℕ} (H : SimpleGraph (Fin n)) (B K : Finset (Fin n))
    (hc : (H.induce (K : Set _)).Connected) (hd : Disjoint K B) :
    ∃ K₀, IsComponent H (Finset.univ \ B) K₀ ∧ K ⊆ K₀ := by
  have hK : K ⊆ Finset.univ \ B := fun i hi => Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,Finset.disjoint_left.mp hd hi⟩
  obtain ⟨K₀,⟨hu,hk0,hc0⟩,hm⟩ := max_size (P:=fun D => K ⊆ D ∧ D ⊆ Finset.univ \ B ∧ (H.induce (D : Set _)).Connected)
    ⟨Finset.Subset.refl _,hK,hc⟩
  exact ⟨K₀,⟨hk0,hc0,fun D hKD hd hc => (hm D ⟨hu.trans hKD,hd,hc⟩ hKD).symm⟩,hu⟩

private def blocks {n : ℕ} (G : SimpleGraph (Fin n)) (D Y Q P : Finset (Fin n)) : Prop :=
  P ⊆ D ∧ ∀ U ⊆ D, (G.induce (U : Set _)).Connected →
    (U ∩ Y).Nonempty → (U ∩ Q).Nonempty → (U ∩ P).Nonempty

private lemma minimum_block {n : ℕ} (H : SimpleGraph (Fin n)) (D Y Q : Finset (Fin n))
    (hy : Y ⊆ D) : ∃ P, blocks H D Y Q P ∧ ∀ P', blocks H D Y Q P' → P.card ≤ P'.card := by
  classical
  let fs := Finset.univ.filter (blocks H D Y Q)
  have hf (P) : P ∈ fs ↔ blocks H D Y Q P := by simp [fs]
  have hY : blocks H D Y Q Y := ⟨hy,fun _ _ _ h _ => h⟩
  obtain ⟨P,hp,hm⟩ := fs.exists_min_image Finset.card ⟨Y,(hf Y).mpr hY⟩
  exact ⟨P,(hf P).mp hp,fun P' h => hm P' ((hf P').mpr h)⟩

private lemma boundary_exchange {n : ℕ} (H : SimpleGraph (Fin n)) (D Y B P K₀ : Finset (Fin n))
    (hk0 : IsComponent H (Finset.univ \ B) K₀)
    (hp : blocks H D Y (D ∩ B) P)
    (hmin : ∀ P', blocks H D Y (D ∩ B) P' → P.card ≤ P'.card) :
    (P ∩ K₀).card ≤ ((nbr H K₀ ∩ D) \ P).card := by
  classical
  let F := (nbr H K₀ ∩ D) \ P
  let P' := (P \ K₀) ∪ F
  have hsep : blocks H D Y (D ∩ B) P' := by
    refine ⟨Finset.union_subset (Finset.sdiff_subset.trans hp.1) (Finset.sdiff_subset.trans Finset.inter_subset_right),?_⟩
    intro U hU hconn hY hB
    obtain ⟨p,hp'⟩ := hp.2 U hU hconn hY hB
    obtain ⟨pu,pP⟩ := Finset.mem_inter.mp hp'
    by_cases pk : p ∈ K₀
    · obtain ⟨q,hq⟩ := hB
      obtain ⟨qu,qDB⟩ := Finset.mem_inter.mp hq
      have qnot : q ∉ K₀ := fun h => (Finset.mem_sdiff.mp (hk0.1 h)).2 (Finset.mem_inter.mp qDB).2
      have hstrict : (K₀ ∩ U) ⊂ U := Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_right,
        fun e => qnot ((Finset.mem_inter.mp (e.symm ▸ qu)).1)⟩
      obtain ⟨a,ha,b,bu,bout,hab⟩ := edge_grow H hstrict ⟨p,Finset.mem_inter.mpr ⟨pk,pu⟩⟩ hconn
      have bk : b ∉ K₀ := fun h => bout (Finset.mem_inter.mpr ⟨h,bu⟩)
      have bn : b ∈ nbr H K₀ := (nbr_mem ..).mpr ⟨bk,a,(Finset.mem_inter.mp ha).1,hab⟩
      refine ⟨b,Finset.mem_inter.mpr ⟨bu,?_⟩⟩
      by_cases bP : b ∈ P
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨bP,bk⟩)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨bn,hU bu⟩,bP⟩)
    · exact ⟨p,Finset.mem_inter.mpr ⟨pu,Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨pP,pk⟩)⟩⟩
  have h := (hmin P' hsep).trans (Finset.card_union_le ..)
  have c := Finset.card_sdiff_add_card_inter P K₀
  change _ ≤ F.card
  omega

private lemma cut_endpoints {n : ℕ} (H : SimpleGraph (Fin n)) (D : Finset (Fin n)) :
    ∃ Y ⊆ D, Y.card ≤ cutSize H D ∧ ∀ u ∈ D, ∀ v ∉ D, H.Adj u v → u ∈ Y := by
  classical
  let Y := D.filter fun u => ∃ v ∉ D, H.Adj u v
  have hf (u) : u ∈ Y ↔ u ∈ D ∧ ∃ v ∉ D, H.Adj u v := Finset.mem_filter
  refine ⟨Y,Finset.filter_subset _ _,?_,fun u hu v hv ha => (hf u).mpr ⟨hu,v,hv,ha⟩⟩
  let f := fun u : ↑Y => ((hf u.val).mp u.property).2.choose
  have spec (u : ↑Y) : f u ∉ D ∧ H.Adj u.val (f u) := ((hf u.val).mp u.property).2.choose_spec
  let edge := fun u : ↑Y => s(u.val,f u)
  have he (u : ↑Y) : edge u ∈ cutEdges H D := (mem_cutEdges_mk ..).mpr ⟨(spec u).2,Or.inl ⟨((hf _).mp u.property).1,(spec u).1⟩⟩
  have inj : Function.Injective edge := by
    intro u v h
    rcases Sym2.eq_iff.mp h with ⟨h,_⟩ | ⟨h,_⟩
    · exact Subtype.ext h
    · exact False.elim ((spec v).1 (h ▸ ((hf _).mp u.property).1))
  have card := Fintype.card_le_of_injective (fun u : ↑Y => (⟨edge u,he u⟩ : ↑(cutEdges H D))) (fun _ _ h => inj (congrArg Subtype.val h))
  simpa [cutSize] using card

private lemma private_region {n : ℕ} (H : SimpleGraph (Fin n)) (X Z D : Finset (Fin n)) (r : Fin n)
    (hr : r ∉ X) (hi : IsConnCut (restrictMinus H (Finset.univ \ (X \ Z)) ∅) {r} Z D) :
    Disjoint D X := by
  classical
  let H' := restrictMinus H (Finset.univ \ (X \ Z)) ∅
  have hrD := hi.1 (Finset.mem_singleton_self r)
  apply Finset.disjoint_left.mpr
  intro u hu hx
  have huz : u ∉ Z := Finset.disjoint_left.mp hi.2.1 hu
  have hne : ({u} : Finset _) ≠ D := fun e => hr ((Finset.mem_singleton.mp (e.symm ▸ hrD)).symm ▸ hx)
  obtain ⟨v,hv,w,_,_,ha⟩ := edge_grow H' (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.singleton_subset_iff.mpr hu,hne⟩)
    (Finset.singleton_nonempty u) hi.2.2
  have eq := Finset.mem_singleton.mp hv
  exact (Finset.mem_sdiff.mp ha.2.1).2 (eq ▸ Finset.mem_sdiff.mpr ⟨hx,huz⟩)

private lemma prof_shrink {n : ℕ} (H : SimpleGraph (Fin n)) (X B D W : Finset (Fin n)) (k : ℕ)
    (hXB : X ⊆ B) (hDX : Disjoint D X) (hw : W ⊆ X) (hwk : W.card ≤ k)
    (had : adh H B ≤ 2*k)
    (hc : cutSize (restrictMinus H (Finset.univ \ W) ∅) D ≤ k)
    (hprof : cutSize (restrictMinus H (Finset.univ \ W) ∅) D < (D ∩ B).card) :
    ∃ B' : Finset (Fin n), X ⊆ B' ∧ B'.card < B.card ∧ adh H B' ≤ 2*k := by
  classical
  let H' := restrictMinus H (Finset.univ \ W) ∅
  obtain ⟨Y,hy,hycard,hyedge⟩ := cut_endpoints H' D
  obtain ⟨P,hp,hmin⟩ := minimum_block H D Y (D ∩ B) hy
  have hpc := hmin Y ⟨hy,fun _ _ _ h _ => h⟩
  let B' := (B \ D) ∪ P
  have hXB' : X ⊆ B' := fun v h => Finset.mem_union_left _ (Finset.mem_sdiff.mpr
    ⟨hXB h,fun d => Finset.disjoint_left.mp hDX d h⟩)
  have hBD : ∀ {v}, v ∈ B' → v ∈ D → v ∈ P := by
    intro v hv hd
    obtain h | h := Finset.mem_union.mp hv
    · exact False.elim ((Finset.mem_sdiff.mp h).2 hd)
    · exact h
  have hG {u v} (hu : u ∈ D) (hv : v ∉ W) (h : H.Adj u v) : H'.Adj u v :=
    ⟨h,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,fun w => Finset.disjoint_left.mp hDX hu (hw w)⟩,
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hv⟩,by simp⟩
  refine ⟨B',hXB',?_,?_⟩
  · have hh := Finset.card_union_le (B \ D) P
    have he := Finset.card_sdiff_add_card_inter B D
    rw [Finset.inter_comm B D] at he
    change ((B \ D) ∪ P).card < B.card
    change Y.card ≤ cutSize (restrictMinus H (Finset.univ \ W) ∅) D at hycard
    omega
  · apply Finset.sup_le
    intro K hK
    have hk : IsComponent H (Finset.univ \ B') K := (Finset.mem_filter.mp hK).2
    have hnot {u} (hu : u ∈ K) : u ∉ B' := (Finset.mem_sdiff.mp (hk.1 hu)).2
    have hn := nbr_component H B' K hk
    by_cases hKB : (K ∩ B).Nonempty
    · obtain ⟨b,hb⟩ := hKB
      obtain ⟨bk,bb⟩ := Finset.mem_inter.mp hb
      have bd : b ∈ D := by
        by_contra h
        exact hnot bk (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨bb,h⟩))
      obtain ⟨V,hV,bv,hconn,hclosed⟩ := closed_piece H (K ∩ D) b (Finset.mem_inter.mpr ⟨bk,bd⟩)
      have hVK : V ⊆ K := hV.trans Finset.inter_subset_left
      have hVD : V ⊆ D := hV.trans Finset.inter_subset_right
      have noY {u} (hu : u ∈ V) : u ∉ Y := by
        intro hyu
        obtain ⟨p,hh⟩ := hp.2 V hVD hconn ⟨u,Finset.mem_inter.mpr ⟨hu,hyu⟩⟩
          ⟨b,Finset.mem_inter.mpr ⟨bv,Finset.mem_inter.mpr ⟨bd,bb⟩⟩⟩
        exact hnot (hVK (Finset.mem_inter.mp hh).1) (Finset.mem_union_right _ (Finset.mem_inter.mp hh).2)
      have eq : V = K := by
        by_contra hne
        obtain ⟨u,hu,z,hz,hnv,hadj⟩ := edge_grow H (Finset.ssubset_iff_subset_ne.mpr ⟨hVK,hne⟩) ⟨b,bv⟩ hk.2.1
        by_cases zd : z ∈ D
        · exact hnv (hclosed u hu z (Finset.mem_inter.mpr ⟨hz,zd⟩) hadj)
        · have zw : z ∉ W := fun h => hnot hz (hXB' (hw h))
          exact noY hu (hyedge u (hVD hu) z zd (hG (hVD hu) zw hadj))
      have sub : nbr H K ⊆ P ∪ W := by
        intro z hz; obtain ⟨_,u,hu,hadj⟩ := (nbr_mem ..).mp hz
        by_cases zd : z ∈ D
        · exact Finset.mem_union_left _ (hBD (hn hz) zd)
        · apply Finset.mem_union_right
          by_contra zw
          have huv : u ∈ V := eq.symm ▸ hu
          exact noY huv (hyedge u (hVD huv) z zd (hG (hVD huv) zw hadj))
      have hh := (Finset.card_le_card sub).trans (Finset.card_union_le ..)
      change Y.card ≤ cutSize (restrictMinus H (Finset.univ \ W) ∅) D at hycard
      omega
    · have hdKB : Disjoint K B := Finset.disjoint_left.mpr (fun u hu hb => hKB ⟨u,Finset.mem_inter.mpr ⟨hu,hb⟩⟩)
      obtain ⟨K₀,hk0,hKK⟩ := enclosure H B K hk.2.1 hdKB
      let N := nbr H K
      let N₀ := nbr H K₀
      let F := (N₀ ∩ D) \ P
      have hF : F ⊆ N₀ := Finset.sdiff_subset.trans Finset.inter_subset_left
      have sub1 : N \ B ⊆ P ∩ K₀ := by
        intro v hv
        obtain ⟨hnv,hvb⟩ := Finset.mem_sdiff.mp hv
        obtain ⟨_,u,hu,hadj⟩ := (nbr_mem ..).mp hnv
        have vP : v ∈ P := (Finset.mem_union.mp (hn hnv)).resolve_left (fun h => hvb (Finset.mem_sdiff.mp h).1)
        exact Finset.mem_inter.mpr ⟨vP,comp_closed hk0 (hKK hu) (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hvb⟩) hadj⟩
      have sub2 : N ∩ B ⊆ N₀ \ F := by
        intro v hv
        obtain ⟨hnv,hvb⟩ := Finset.mem_inter.mp hv
        obtain ⟨_,u,hu,hadj⟩ := (nbr_mem ..).mp hnv
        have hn0 : v ∈ N₀ := (nbr_mem ..).mpr ⟨fun h => (Finset.mem_sdiff.mp (hk0.1 h)).2 hvb,u,hKK hu,hadj⟩
        exact Finset.mem_sdiff.mpr ⟨hn0,fun h => (Finset.mem_sdiff.mp h).2
          (hBD (hn hnv) (Finset.mem_inter.mp (Finset.mem_sdiff.mp h).1).2)⟩
      have h₁ := Finset.card_le_card sub1
      have h₂ := Finset.card_le_card sub2
      have h₃ : (P ∩ K₀).card ≤ F.card := boundary_exchange H D Y B P K₀ hk0 hp hmin
      have h₄ := Finset.card_sdiff_add_card_inter N B
      have h₅ := Finset.card_sdiff_add_card_eq_card hF
      have h₆ : N₀.card ≤ adh H B := Finset.le_sup (f:=fun C => (nbr H C).card) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk0⟩)
      change N.card ≤ _
      omega

theorem solution {n : ℕ} (H : SimpleGraph (Fin n)) (k : ℕ) (X B : Finset (Fin n))
    (hXB : X ⊆ B) (hX : X.card ≤ 2*k+1) (hadh : adh H B ≤ 2*k) :
    IsEdgeUnbreakable H Finset.univ B (2*k) k ∨
      ∃ B' : Finset (Fin n), X ⊆ B' ∧ B'.card < B.card ∧ adh H B' ≤ 2*k := by
  classical
  by_cases hb : IsEdgeUnbreakable H Finset.univ B (2*k) k
  · exact Or.inl hb
  · apply Or.inr
    obtain ⟨Z,r,D,hZ,hk,hr,hi,hcost,hprof⟩ := find_important H X B k hXB hX hb
    have hd := private_region H X Z D r (Finset.mem_sdiff.mp hr).2 hi.1
    exact prof_shrink H X B D (X \ Z) k hXB hd Finset.sdiff_subset hk hadh hcost hprof
