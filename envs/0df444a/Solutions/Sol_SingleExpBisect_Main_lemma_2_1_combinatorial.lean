-- Prove2me | solution 1 for SingleExpBisect.Main.lemma_2_1_combinatorial
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T10:10:25.237818+00:00
-- url     : https://prove2.me/submissions/3f64fe5a-8bd0-410d-994a-876deae5534d

/- Cut-edge, submodularity, and attainment lemmas adapted from Secousses, Prove2Me submission 797eedb1-a223-4590-b528-4b3d16d0ab3c (Apache-2.0). -/
import Mathlib
import Definitions.Def_SingleExpBisect_Main_NodeData
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

/-- Submodularity of the cut function. -/
private lemma cut_submod {n : ℕ} (G : SimpleGraph (Fin n)) (X Y : Finset (Fin n)) :
    cutSize G (X ∪ Y) + cutSize G (X ∩ Y) ≤ cutSize G X + cutSize G Y := by
  unfold cutSize
  have h1 : cutEdges G (X ∪ Y) ∪ cutEdges G (X ∩ Y) ⊆ cutEdges G X ∪ cutEdges G Y := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      simp only [Finset.mem_union, mem_cutEdges_mk, Finset.mem_inter] at he ⊢
      tauto
  have h2 : cutEdges G (X ∪ Y) ∩ cutEdges G (X ∩ Y) ⊆ cutEdges G X ∩ cutEdges G Y := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      simp only [Finset.mem_union, mem_cutEdges_mk, Finset.mem_inter] at he ⊢
      tauto
  rw [← Finset.card_union_add_card_inter, ← Finset.card_union_add_card_inter (cutEdges G X)]
  exact Nat.add_le_add (Finset.card_le_card h1) (Finset.card_le_card h2)

private lemma max_size {n : ℕ} {P : Finset (Fin n) → Prop} {A : Finset (Fin n)}
    (hA : P A) : ∃ B, P B ∧ ∀ C, P C → B ⊆ C → B = C := by
  classical
  let f := Finset.univ.filter P
  have hf (D) : D ∈ f ↔ P D := by simp [f]
  obtain ⟨B,hB,hh⟩ := f.exists_max_image Finset.card ⟨A,(hf _).mpr hA⟩
  exact ⟨B,(hf _).mp hB,fun C hC hBC => Finset.eq_of_subset_of_card_le hBC (hh C ((hf C).mpr hC))⟩

private lemma extend_important {n : ℕ} (G : SimpleGraph (Fin n)) {S T C : Finset (Fin n)}
    (hC : IsConnCut G S T C) :
    ∃ D, IsImportantConnCut G S T D ∧ C ⊆ D ∧ cutSize G D ≤ cutSize G C := by
  have h : IsConnCut G S T C ∧ C ⊆ C ∧ cutSize G C ≤ cutSize G C :=
    ⟨hC,Finset.Subset.refl _,le_rfl⟩
  obtain ⟨D,hd,hm⟩ := max_size (P := fun D => IsConnCut G S T D ∧ C ⊆ D ∧ cutSize G D ≤ cutSize G C) h
  refine ⟨D,⟨hd.1,?_⟩,hd.2⟩
  intro E hde he
  by_contra! h
  have eq := hm E ⟨he,hd.2.1.trans hde.le,h.trans hd.2.2⟩ hde.le
  exact hde.ne eq

private lemma connected_part {n : ℕ} (G : SimpleGraph (Fin n)) {S A : Finset (Fin n)}
    (hS : (G.induce (S : Set _)).Connected) (hSA : S ⊆ A) :
    ∃ C, S ⊆ C ∧ C ⊆ A ∧ (G.induce (C : Set _)).Connected ∧ cutSize G C ≤ cutSize G A := by
  classical
  obtain ⟨C,⟨hSC,hCA,hC⟩,hm⟩ := max_size (P:= fun C => S ⊆ C ∧ C ⊆ A ∧
    (G.induce (C : Set _)).Connected) ⟨Finset.Subset.refl _,hSA,hS⟩
  have hclosed {a b} (ha : a ∈ C) (hb : b ∈ A) (he : G.Adj a b) : b ∈ C := by
    have hc : (G.induce ((C : Set _) ∪ {b})).Connected :=
      SimpleGraph.connected_induce_union hC.preconnected SimpleGraph.Preconnected.of_subsingleton ha (Set.mem_singleton b) he
    have eq : (↑(insert b C) : Set _) = (C : Set _) ∪ {b} := by ext; simp [or_comm]
    have h' := hm (insert b C) ⟨hSC.trans (Finset.subset_insert ..),Finset.insert_subset hb hCA,eq ▸ hc⟩
      (Finset.subset_insert ..)
    exact h' ▸ Finset.mem_insert_self _ _
  refine ⟨C,hSC,hCA,hC,Finset.card_le_card ?_⟩
  intro e; induction e using Sym2.ind with
  | _ a b =>
    simp only [mem_cutEdges_mk]
    rintro ⟨h, (⟨ha,hb⟩ | ⟨hb,ha⟩)⟩
    · exact ⟨h,Or.inl ⟨hCA ha,fun hu => hb (hclosed ha hu h)⟩⟩
    · exact ⟨h,Or.inr ⟨hCA hb,fun hu => ha (hclosed hb hu h.symm)⟩⟩

private noncomputable def mincut {n : ℕ} (G : SimpleGraph (Fin n)) (S T : Finset (Fin n)) :=
  sInf {j : ℕ | ∃ X : Finset (Fin n), S ⊆ X ∧ Disjoint X T ∧ cutSize G X = j}

private lemma min_le {n : ℕ} (G : SimpleGraph (Fin n)) {S T X : Finset (Fin n)}
    (h : S ⊆ X) (hd : Disjoint X T) : mincut G S T ≤ cutSize G X := Nat.sInf_le ⟨X,h,hd,rfl⟩

private lemma central_cut {n : ℕ} (G : SimpleGraph (Fin n)) {S T : Finset (Fin n)}
    (hs : (G.induce (S : Set _)).Connected) (hd : Disjoint S T) :
    ∃ X, IsConnCut G S T X ∧ cutSize G X = mincut G S T ∧
      ∀ Y, IsConnCut G S T Y → cutSize G Y ≤ mincut G S T → X ⊆ Y → X = Y := by
  have ⟨A,ha,hat,hcut⟩ := Nat.sInf_mem (s:={j : ℕ | ∃ X : Finset (Fin n), S ⊆ X ∧ Disjoint X T ∧ cutSize G X = j})
    ⟨cutSize G S,S,Finset.Subset.refl _,hd,rfl⟩
  obtain ⟨C,hsc,hca,hc,hb⟩ := connected_part G hs ha
  have hdC := hat.mono_left hca
  have hC : IsConnCut G S T C ∧ cutSize G C ≤ mincut G S T := ⟨⟨hsc,hdC,hc⟩,hb.trans hcut.le⟩
  obtain ⟨X,⟨hx,hh⟩,hm⟩ := max_size (P:=fun X => IsConnCut G S T X ∧ cutSize G X ≤ mincut G S T) hC
  exact ⟨X,hx,le_antisymm hh (min_le G hx.1 hx.2.1),fun Y hy hk => hm Y ⟨hy,hk⟩⟩

private lemma central_subset {n : ℕ} (G : SimpleGraph (Fin n)) {S T X C : Finset (Fin n)}
    (hs : (G.induce (S : Set _)).Connected) (hx : IsConnCut G S T X)
    (hxcut : cutSize G X = mincut G S T) (hc : IsImportantConnCut G S T C) : X ⊆ C := by
  classical
  obtain ⟨⟨u,hu⟩⟩ := hs.nonempty
  have hmin := min_le G (Finset.subset_inter hx.1 hc.1.1) (hx.2.1.mono_left (Finset.inter_subset_left (s₂:=C)))
  have hcut := cut_submod G X C
  have hun : IsConnCut G S T (X ∪ C) := by
    refine ⟨hx.1.trans Finset.subset_union_left,Finset.disjoint_union_left.mpr ⟨hx.2.1,hc.1.2.1⟩,?_⟩
    rw [Finset.coe_union]
    exact SimpleGraph.induce_union_connected hx.2.2.preconnected hc.1.2.2.preconnected ⟨u,hx.1 hu,hc.1.1 hu⟩
  by_contra hno
  have hne : C ⊂ X ∪ C := Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_right,fun eq => hno (eq ▸ Finset.subset_union_left)⟩
  have hh := hc.2 _ hne hun
  omega

private noncomputable def cuts {n : ℕ} (G : SimpleGraph (Fin n)) (S T : Finset (Fin n)) (k : ℕ) :=
  Finset.univ.filter (fun C => IsImportantConnCut G S T C ∧ cutSize G C ≤ k)

private lemma mc {n : ℕ} {G : SimpleGraph (Fin n)} {S T C : Finset (Fin n)} {k : ℕ} :
    C ∈ cuts G S T k ↔ IsImportantConnCut G S T C ∧ cutSize G C ≤ k := by simp [cuts]

private lemma del_cut {n : ℕ} (G : SimpleGraph (Fin n)) (a b : Fin n) (C : Finset (Fin n)) :
    cutEdges (G.deleteEdges {s(a,b)}) C = (cutEdges G C).erase s(a,b) := by
  ext e; induction e using Sym2.ind with
  | _ u v => simp only [mem_cutEdges_mk,Finset.mem_erase,SimpleGraph.deleteEdges_adj,Set.mem_singleton_iff];tauto

private lemma del_bound {n : ℕ} (G : SimpleGraph (Fin n)) (a b : Fin n) (C : Finset (Fin n)) :
    cutSize G C ≤ cutSize (G.deleteEdges {s(a,b)}) C + 1 := by
  unfold cutSize; rw [del_cut]
  by_cases h : s(a,b) ∈ cutEdges G C
  · rw [Finset.card_erase_add_one h]
  · rw [Finset.erase_eq_of_notMem h]; omega

private lemma same_inside {n : ℕ} (G : SimpleGraph (Fin n)) (a b : Fin n) (C : Finset (Fin n))
    (hb : b ∉ C) : (G.deleteEdges {s(a,b)}).induce (C : Set _) = G.induce (C : Set _) := by
  ext u v; change (G.deleteEdges {s(a,b)}).Adj u.val v.val ↔ G.Adj u.val v.val
  rw [SimpleGraph.deleteEdges_adj]
  refine ⟨And.left,fun h => ⟨h,?_⟩⟩
  intro hh
  obtain ⟨_,hh⟩ | ⟨hh,_⟩ := Sym2.eq_iff.mp (Set.mem_singleton_iff.mp hh)
  · exact hb (hh ▸ v.property)
  · exact hb (hh ▸ u.property)

private lemma del_important {n : ℕ} (G : SimpleGraph (Fin n)) {S T C : Finset (Fin n)}
    (hc : IsImportantConnCut G S T C) {a b : Fin n} (he : G.Adj a b) (ha : a ∈ C) (hb : b ∉ C) :
    IsImportantConnCut (G.deleteEdges {s(a,b)}) S T C ∧
      cutSize (G.deleteEdges {s(a,b)}) C + 1 = cutSize G C := by
  have hcost : cutSize (G.deleteEdges {s(a,b)}) C + 1 = cutSize G C := by
    unfold cutSize; rw [del_cut,Finset.card_erase_add_one ((mem_cutEdges_mk ..).mpr ⟨he,Or.inl ⟨ha,hb⟩⟩)]
  refine ⟨⟨⟨hc.1.1,hc.1.2.1,(same_inside G a b C hb) ▸ hc.1.2.2⟩,?_⟩,hcost⟩
  intro D hcd hd
  have hle : (G.deleteEdges {s(a,b)}).induce (D : Set _) ≤ G.induce (D : Set _) := fun u v h => h.1
  have hk := hc.2 D hcd ⟨hd.1,hd.2.1,hd.2.2.mono hle⟩
  have hb' := del_bound G a b D
  omega

private lemma edge_grow {n : ℕ} (G : SimpleGraph (Fin n)) {X C : Finset (Fin n)}
    (h : X ⊂ C) (hx : X.Nonempty) (hc : (G.induce (C : Set _)).Connected) :
    ∃ a ∈ X, ∃ b ∈ C, b ∉ X ∧ G.Adj a b := by
  classical
  obtain ⟨a,ha⟩ := hx
  obtain ⟨b,hb,hbn⟩ := Finset.exists_of_ssubset h
  obtain ⟨p⟩ := hc ⟨a,h.le ha⟩ ⟨b,hb⟩
  obtain ⟨e,_,he,he'⟩ := p.exists_boundary_dart {u | u.val ∈ X} ha hbn
  exact ⟨e.fst.val,he,e.snd.val,e.snd.property,he',e.adj⟩

private lemma min_del {n : ℕ} (G : SimpleGraph (Fin n)) (S T : Finset (Fin n)) (a b : Fin n)
    (hd : Disjoint S T) : mincut G S T ≤ mincut (G.deleteEdges {s(a,b)}) S T + 1 := by
  let H := G.deleteEdges {s(a,b)}
  have ⟨A,hA,hT,he⟩ := Nat.sInf_mem (s:={j : ℕ | ∃ X : Finset (Fin n), S ⊆ X ∧ Disjoint X T ∧ cutSize H X = j})
    ⟨cutSize H S,S,Finset.Subset.refl _,hd,rfl⟩
  exact (min_le G hA hT).trans ((del_bound G a b A).trans_eq (congrArg (·+1) he))

private lemma no_min {n : ℕ} (G : SimpleGraph (Fin n)) (S T : Finset (Fin n)) (k : ℕ)
    (hk : k < mincut G S T) : cuts G S T k = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro D hD
  obtain ⟨hi,hk'⟩ := mc.mp hD
  exact (Nat.not_le.mpr hk) ((min_le G hi.1.1 hi.1.2.1).trans hk')

private lemma count_core {n : ℕ} (r : ℕ) :
    ∀ (G : SimpleGraph (Fin n)) (S T : Finset (Fin n)) (k : ℕ),
      (G.induce (S : Set _)).Connected → Disjoint S T → 2*k - mincut G S T ≤ r →
      (cuts G S T k).card ≤ 2 ^ r := by
  classical
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro G S T k hs hd hr
    by_cases hk : k < mincut G S T
    · simp [no_min G S T k hk]
    have hl : mincut G S T ≤ k := by omega
    obtain ⟨X,hx,hcut,hmax⟩ := central_cut G hs hd
    by_cases hz : mincut G S T = 0
    · have hsub : cuts G S T k ⊆ {X} := by
        intro C hc
        have hi := (mc.mp hc).1
        have hh := central_subset G hs hx hcut hi
        by_contra he
        have hne : X ≠ C := fun eq => he (by simp [eq])
        obtain ⟨⟨v,hv⟩⟩ := hs.nonempty
        obtain ⟨a,ha,b,hb,hout,hed⟩ := edge_grow G (Finset.ssubset_iff_subset_ne.mpr ⟨hh,hne⟩)
          ⟨_,hx.1 hv⟩ hi.1.2.2
        have hpos : 0 < cutSize G X := Finset.card_pos.mpr ⟨_,(mem_cutEdges_mk ..).mpr ⟨hed,Or.inl ⟨ha,hout⟩⟩⟩
        omega
      have hh := Finset.card_le_card hsub
      simpa using hh.trans (show ({X} : Finset _).card ≤ 2^r by simp only [Finset.card_singleton]; exact Nat.succ_le_of_lt (pow_pos (by decide) r))
    have hpos : 0 < cutSize G X := by omega
    have hex : ∃ a ∈ X, ∃ b ∉ X, G.Adj a b := by
      obtain ⟨e,he⟩ := Finset.card_pos.mp hpos
      induction e using Sym2.ind with
      | _ a b =>
        obtain ⟨hadj,hmem⟩ := (mem_cutEdges_mk ..).mp he
        rcases hmem with ⟨ha,hb⟩ | ⟨hb,ha⟩
        · exact ⟨a,ha,b,hb,hadj⟩
        · exact ⟨b,hb,a,ha,hadj.symm⟩
    obtain ⟨a,ha,b,hb,hadj⟩ := hex
    let H := G.deleteEdges {s(a,b)}
    let U := insert b X
    have hsH : (H.induce (S : Set _)).Connected := (same_inside G a b S (fun h => hb (hx.1 h))) ▸ hs
    have hU : (G.induce (U : Set _)).Connected := by
      have e : (↑U : Set _) = (X : Set _) ∪ {b} := by ext; simp [U,or_comm]
      rw [e]; exact SimpleGraph.connected_induce_union hx.2.2.preconnected SimpleGraph.Preconnected.of_subsingleton
        ha (Set.mem_singleton b) hadj
    have hleft : (cuts H S T (k-1)).card ≤ 2^(r-1) := by
      have hm := min_del G S T a b hd
      apply ih (r-1) (by omega) H S T (k-1) hsH hd
      change 2*(k-1) - mincut (G.deleteEdges {s(a,b)}) S T ≤ r-1
      omega
    have hright : (cuts G U T k).card ≤ 2^(r-1) := by
      by_cases hdU : Disjoint U T
      · obtain ⟨A,hA,hcA,_⟩ := central_cut G hU hdU
        have hmin : mincut G S T < mincut G U T := by
          by_contra! h
          have hXA : X ⊆ A := (Finset.subset_insert b X).trans hA.1
          have eq := hmax A ⟨hx.1.trans hXA,hA.2⟩ (hcA.le.trans h) hXA
          exact hb (eq ▸ hA.1 (Finset.mem_insert_self ..))
        apply ih (r-1) (by omega) G U T k hU hdU
        omega
      · have hem : cuts G U T k = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro C hc; have hi := (mc.mp hc).1
          exact hdU (hi.1.2.1.mono_left hi.1.1)
        simp [hem]
    have sub : cuts G S T k ⊆ cuts H S T (k-1) ∪ cuts G U T k := by
      intro C hc
      obtain ⟨hi,hk'⟩ := mc.mp hc
      have hxc := central_subset G hs hx hcut hi
      by_cases hbc : b ∈ C
      · apply Finset.mem_union_right
        refine mc.mpr ⟨⟨⟨Finset.insert_subset hbc hxc,hi.1.2⟩,?_⟩,hk'⟩
        intro D hD hconn
        exact hi.2 D hD ⟨hi.1.1.trans hD.le,hconn.2⟩
      · apply Finset.mem_union_left
        obtain ⟨hdel,heq⟩ := del_important G hi hadj (hxc ha) hbc
        exact mc.mpr ⟨hdel,by dsimp [H]; omega⟩
    have hh := (Finset.card_le_card sub).trans (Finset.card_union_le ..)
    have hrpos : r ≠ 0 := by omega
    calc
      _ ≤ 2^(r-1) + 2^(r-1) := hh.trans (Nat.add_le_add hleft hright)
      _ = 2^r := by nth_rw 3 [show r = (r-1)+1 by omega]; rw [pow_succ]; omega

theorem solution :
    ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (S T : Finset (Fin n)),
      Disjoint S T → (H.induce (S : Set (Fin n))).Connected →
      (∀ C : Finset (Fin n), IsConnCut H S T C →
          ∃ D : Finset (Fin n), IsImportantConnCut H S T D ∧ C ⊆ D ∧ cutSize H D ≤ cutSize H C) ∧
        ∀ ℓ : ℕ, ((Finset.univ : Finset (Finset (Fin n))).filter
          (fun D => IsImportantConnCut H S T D ∧ cutSize H D ≤ ℓ)).card ≤ 4 ^ ℓ := by
  intro n H S T hd hs
  refine ⟨fun _ hc => extend_important H hc,?_⟩
  intro k
  have h := count_core (2*k) H S T k hs hd (Nat.sub_le ..)
  have hp : 2 ^ (2*k) = 4 ^ k := by rw [pow_mul]; norm_num
  exact h.trans_eq hp
