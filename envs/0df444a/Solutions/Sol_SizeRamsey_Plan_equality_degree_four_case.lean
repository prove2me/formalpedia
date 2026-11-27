-- Prove2me | solution 1 for SizeRamsey.Plan.equality_degree_four_case
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:31:08.063244+00:00
-- url     : https://prove2.me/submissions/5fc9c536-fa48-4e0c-a30a-14c107207a92

module
public import Definitions.Def_SizeRamsey_Equality_Common
public import Definitions.Def_SizeRamsey_Equality_Extension
public import Definitions.Def_SizeRamsey_Equality_DegreeFour
public import Theorems.Thm_SizeRamsey_Plan_attachment_sum
public import Theorems.Thm_SizeRamsey_Plan_classified_prescribed
public import Theorems.Thm_SizeRamsey_Plan_compGraph_connected
public import Theorems.Thm_SizeRamsey_Plan_component_attachment_card_ge_two
public import Theorems.Thm_SizeRamsey_Plan_component_edgeCount_le
public import Theorems.Thm_SizeRamsey_Plan_degree_four_reduction
public import Theorems.Thm_SizeRamsey_Plan_equality_max_degree_le_four
public import Theorems.Thm_SizeRamsey_Plan_equality_min_degree
public import Theorems.Thm_SizeRamsey_Plan_equality_residual_components
public import Theorems.Thm_SizeRamsey_Plan_equality_square_supported
public import Theorems.Thm_SizeRamsey_Plan_erase_degree
public import Theorems.Thm_SizeRamsey_Plan_erase_singleton_counts
public import Theorems.Thm_SizeRamsey_Plan_k33_extension_tau_le_two
public import Theorems.Thm_SizeRamsey_Plan_small_graph_data
public import Theorems.Thm_SizeRamsey_Plan_tau4_components
public import Theorems.Thm_SizeRamsey_tau4_iso
public import Theorems.Thm_SizeRamsey_tau4_le_card

section
@[expose] public section
namespace SizeRamsey.Plan
universe u
attribute [local instance] Classical.propDecidable
private theorem card_le_degree' {V : Type u} [Fintype V] (G : SimpleGraph V) (w : V)
    (s : Finset V) (hs : ∀ x ∈ s, G.Adj w x) : s.card ≤ G.degree w := by
  rw [← G.card_neighborFinset_eq_degree]
  exact Finset.card_le_card (fun x hx => (G.mem_neighborFinset w x).2 (hs x hx))
private theorem edgeCount_pos_of_adj {V : Type u} [Fintype V] (G : SimpleGraph V) {a b : V}
    (h : G.Adj a b) : 0 < edgeCount G := by
  unfold edgeCount
  exact Finset.card_pos.2 ⟨s(a, b), (G.mem_edgeFinset).2 h⟩
private theorem induce_singleton_edgeCount {V : Type u} (G : SimpleGraph V) (v : V) :
    edgeCount (G.induce (({v} : Finset V) : Set V)) = 0 := by
  have h : G.induce (({v} : Finset V) : Set V) = ⊥ := by
    ext a b
    simp only [SimpleGraph.bot_adj, iff_false]
    intro hab
    have ha := a.2
    have hb := b.2
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at ha hb
    exact hab.ne (Subtype.ext (ha.trans hb.symm))
  rw [h]
  unfold edgeCount
  simp
private theorem erase_pos_degree {V : Type u} [Fintype V] (G : SimpleGraph V) (v : V)
    (hmin : ∀ w, 2 ≤ G.degree w) (y : {x : V // x ∉ ({v} : Finset V)}) :
    0 < (erase G {v}).degree y := by
  have h := erase_degree G {v} y
  have h1 : (G.neighborFinset y.val ∩ {v}).card ≤ 1 :=
    (Finset.card_le_card Finset.inter_subset_right).trans (by simp)
  have := hmin y.val
  omega
private theorem two_component_contra {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hc : G.Connected) (ih : SmallerClassified G)
    (v : V) (hv : G.degree v = 4)
    (hmin : ∀ w, 2 ≤ G.degree w) (hsq : SquareSupported G)
    (hcnt : edgeCount (erase G {v}) + G.degree v = edgeCount G)
    (hτ : tau4 G = tau4 (erase G {v}) + 1)
    (hcomp : ∀ C : (erase G {v}).ConnectedComponent,
      4 * tau4 (compGraph (erase G {v}) C) = edgeCount (compGraph (erase G {v}) C))
    (hHc : ¬ (erase G {v}).Connected) (y₀ : {x : V // x ∉ ({v} : Finset V)}) : False := by
  have : Nonempty {x : V // x ∉ ({v} : Finset V)} := ⟨y₀⟩
  -- two distinct components
  have hnp : ¬ (erase G {v}).Preconnected := fun hp => hHc ⟨hp⟩
  obtain ⟨x₁, x₂, hx⟩ : ∃ x₁ x₂, ¬ (erase G {v}).Reachable x₁ x₂ := by
    unfold SimpleGraph.Preconnected at hnp
    push Not at hnp
    exact hnp
  have hC12 : (erase G {v}).connectedComponentMk x₁ ≠
      (erase G {v}).connectedComponentMk x₂ := fun h =>
    hx (SimpleGraph.ConnectedComponent.eq.1 h)
  have hsum := attachment_sum G {v}
  rw [induce_singleton_edgeCount, Finset.sum_singleton, hv] at hsum
  have hproper : ({v} : Finset V) ≠ Finset.univ := by
    intro h
    have hy : y₀.val ∈ (Finset.univ : Finset V) := Finset.mem_univ _
    rw [← h] at hy
    exact y₀.2 hy
  have hge : ∀ C, 2 ≤ (attachmentEdges G {v} C).card := fun C =>
    component_attachment_card_ge_two G hc hsq {v} (Finset.singleton_nonempty v) hproper C
  have hle : ∀ C, (attachmentEdges G {v} C).card ≤ 2 := by
    intro C
    obtain ⟨C', hC'⟩ : ∃ C', C' ≠ C := by
      by_cases h : (erase G {v}).connectedComponentMk x₁ = C
      · exact ⟨_, fun h' => hC12 (h.trans h'.symm)⟩
      · exact ⟨_, h⟩
    have hpair : (attachmentEdges G {v} C).card + (attachmentEdges G {v} C').card ≤
        ∑ D : (erase G {v}).ConnectedComponent, (attachmentEdges G {v} D).card := by
      calc _ = ∑ D ∈ {C, C'}, (attachmentEdges G {v} D).card :=
            (Finset.sum_pair hC'.symm).symm
        _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have := hge C'
    omega
  have hmem_att : ∀ (C : (erase G {v}).ConnectedComponent) (y : {x : V // x ∉ ({v} : Finset V)}),
      y ∈ C.supp → G.Adj y.val v → (y.val, v) ∈ attachmentEdges G {v} C := by
    intro C y hy hyv
    simp only [attachmentEdges, componentVerts, Finset.mem_filter, Finset.mem_product,
      Finset.mem_image, Set.mem_toFinset, Finset.mem_singleton]
    exact ⟨⟨⟨y, hy, rfl⟩, by simp⟩, hyv⟩
  -- an attachment vertex and a prescribed optimal transversal in each component
  have hchoice : ∀ C : (erase G {v}).ConnectedComponent, ∃ a : C.supp, G.Adj a.val.val v ∧
      ∃ T : Finset C.supp, a ∈ T ∧ c4Transversal (compGraph (erase G {v}) C) T ∧
        T.card = tau4 (compGraph (erase G {v}) C) := by
    intro C
    obtain ⟨p, hp⟩ := Finset.card_pos.1 (lt_of_lt_of_le two_pos (hge C))
    simp only [attachmentEdges, componentVerts, Finset.mem_filter, Finset.mem_product,
      Finset.mem_image, Set.mem_toFinset, Finset.mem_singleton] at hp
    obtain ⟨⟨⟨y, hy, hyp⟩, hp2⟩, hadj⟩ := hp
    have hyv : G.Adj y.val v := by rw [hyp, ← hp2]; exact hadj
    refine ⟨⟨y, hy⟩, hyv, ?_⟩
    have hdeg := erase_pos_degree G v hmin y
    obtain ⟨y', hy'⟩ := ((erase G {v}).degree_pos_iff_exists_adj y).1 hdeg
    have hy'C : y' ∈ C.supp := by
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hy ⊢
      rw [← hy]
      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hy').symm
    have hpos : 0 < edgeCount (compGraph (erase G {v}) C) :=
      edgeCount_pos_of_adj (compGraph (erase G {v}) C) (a := ⟨y, hy⟩) (b := ⟨y', hy'C⟩) hy'
    have hlt : edgeCount (compGraph (erase G {v}) C) < edgeCount G := by
      have := component_edgeCount_le (erase G {v}) C
      omega
    have hcl := ih (compGraph (erase G {v}) C) (compGraph_connected (erase G {v}) C) hpos hlt
      (hcomp C)
    exact classified_prescribed _ hcl ⟨y, hy⟩
  choose a ha T haT hT hTc using hchoice
  set L : (erase G {v}).ConnectedComponent → Finset V := fun C => (T C).image (fun y => y.val.val)
  set Tall := Finset.univ.biUnion L with hTall
  have hmemT : ∀ C (y : C.supp), y ∈ T C → y.val.val ∈ Tall := by
    intro C y hy
    rw [hTall, Finset.mem_biUnion]
    exact ⟨C, Finset.mem_univ _, Finset.mem_image.2 ⟨y, hy, rfl⟩⟩
  have hcard : Tall.card ≤ tau4 (erase G {v}) := by
    rw [tau4_components (erase G {v})]
    calc Tall.card ≤ ∑ C, (L C).card := Finset.card_biUnion_le
      _ ≤ ∑ C, (T C).card := Finset.sum_le_sum (fun C _ => Finset.card_image_le)
      _ = ∑ C, tau4 (compGraph (erase G {v}) C) := Finset.sum_congr rfl (fun C _ => hTc C)
  -- squares through `v` meet the chosen attachment vertex
  have key : ∀ u x w : V, G.Adj v u → G.Adj u x → G.Adj x w → G.Adj w v → u ≠ w →
      x ≠ v → u ∈ Tall ∨ w ∈ Tall := by
    intro u x w hvu hux hxw hwv huw hxv
    have hu : u ∉ ({v} : Finset V) := by simpa using hvu.ne.symm
    have hx' : x ∉ ({v} : Finset V) := by simpa using hxv
    have hw : w ∉ ({v} : Finset V) := by simpa using hwv.ne
    set C := (erase G {v}).connectedComponentMk ⟨u, hu⟩
    have hreach : (erase G {v}).Reachable ⟨u, hu⟩ ⟨w, hw⟩ :=
      (SimpleGraph.Adj.reachable (G := (erase G {v})) (u := ⟨u, hu⟩) (v := ⟨x, hx'⟩) hux).trans
        (SimpleGraph.Adj.reachable (G := (erase G {v})) (u := ⟨x, hx'⟩) (v := ⟨w, hw⟩) hxw)
    have huC : (⟨u, hu⟩ : {x : V // x ∉ ({v} : Finset V)}) ∈ C.supp := rfl
    have hwC : (⟨w, hw⟩ : {x : V // x ∉ ({v} : Finset V)}) ∈ C.supp :=
      (SimpleGraph.ConnectedComponent.eq.2 hreach).symm
    by_cases hau : (a C).val.val = u
    · left; rw [← hau]; exact hmemT C (a C) (haT C)
    by_cases haw : (a C).val.val = w
    · right; rw [← haw]; exact hmemT C (a C) (haT C)
    exfalso
    have hsub : ({(u, v), (w, v), ((a C).val.val, v)} : Finset (V × V)) ⊆
        attachmentEdges G {v} C := by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl
      · exact hmem_att C _ huC hvu.symm
      · exact hmem_att C _ hwC hwv
      · exact hmem_att C _ (a C).2 (ha C)
    have h3 : ({(u, v), (w, v), ((a C).val.val, v)} : Finset (V × V)).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp only [Finset.mem_singleton, Prod.mk.injEq, and_true]
        exact fun h => haw h.symm
      · simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, and_true]
        rintro (h | h)
        · exact huw h
        · exact hau h.symm
    have := Finset.card_le_card hsub
    have := hle C
    omega
  have htrans : c4Transversal G Tall := by
    intro f hf
    obtain ⟨hfi, h01, h12, h23, h30⟩ := hf
    have hne : ∀ i j : Fin 4, i ≠ j → f i ≠ f j := fun i j h e => h (hfi e)
    by_cases hzf : ∃ k, f k = v
    · obtain ⟨k, hk⟩ := hzf
      fin_cases k
      · subst hk
        rcases key (f 1) (f 2) (f 3) h01 h12 h23 h30 (hne 1 3 (by decide))
          (hne 2 0 (by decide)) with h | h
        exacts [⟨1, h⟩, ⟨3, h⟩]
      · subst hk
        rcases key (f 2) (f 3) (f 0) h12 h23 h30 h01 (hne 2 0 (by decide))
          (hne 3 1 (by decide)) with h | h
        exacts [⟨2, h⟩, ⟨0, h⟩]
      · subst hk
        rcases key (f 3) (f 0) (f 1) h23 h30 h01 h12 (hne 3 1 (by decide))
          (hne 0 2 (by decide)) with h | h
        exacts [⟨3, h⟩, ⟨1, h⟩]
      · subst hk
        rcases key (f 0) (f 1) (f 2) h30 h01 h12 h23 (hne 0 2 (by decide))
          (hne 1 3 (by decide)) with h | h
        exacts [⟨0, h⟩, ⟨2, h⟩]
    · push Not at hzf
      have hfD : ∀ i, f i ∉ ({v} : Finset V) := fun i => by simpa using hzf i
      let g : Fin 4 → {x : V // x ∉ ({v} : Finset V)} := fun i => ⟨f i, hfD i⟩
      set C := (erase G {v}).connectedComponentMk (g 0)
      have hg01 : (erase G {v}).Adj (g 0) (g 1) := h01
      have hg12 : (erase G {v}).Adj (g 1) (g 2) := h12
      have hg23 : (erase G {v}).Adj (g 2) (g 3) := h23
      have hC : ∀ i, g i ∈ C.supp := by
        intro i
        have r1 := hg01.reachable
        have r2 := r1.trans hg12.reachable
        have r3 := r2.trans hg23.reachable
        fin_cases i
        · rfl
        · exact (SimpleGraph.ConnectedComponent.eq.2 r1).symm
        · exact (SimpleGraph.ConnectedComponent.eq.2 r2).symm
        · exact (SimpleGraph.ConnectedComponent.eq.2 r3).symm
      let h : Fin 4 → C.supp := fun i => ⟨g i, hC i⟩
      have hh : IsC4Map (compGraph (erase G {v}) C) h :=
        ⟨fun i j e => hfi (congrArg (fun y : C.supp => y.val.val) e), h01, h12, h23, h30⟩
      obtain ⟨i, hi⟩ := hT C h hh
      exact ⟨i, hmemT C (h i) hi⟩
  have := tau4_le_card htrans
  omega
private theorem residual_labels {V : Type u} {n : ℕ} (G : SimpleGraph V) (v : V)
    {X : SimpleGraph (Fin n)} (e : erase G {v} ≃g X) :
    ∃ φ : Fin n → V, Function.Injective φ ∧ (∀ i, φ i ≠ v) ∧
      (∀ y, y ≠ v → ∃ i, φ i = y) ∧ ∀ i j, G.Adj (φ i) (φ j) ↔ X.Adj i j :=
  ⟨fun i => (e.symm i).1, fun _ _ h => e.symm.injective (Subtype.ext h),
    fun i => by simpa using (e.symm i).2,
    fun y hy => ⟨e ⟨y, by simpa using hy⟩, by simp⟩, fun _ _ => e.symm.map_adj_iff⟩
private theorem adj_all_of_card {V : Type u} [Fintype V] (G : SimpleGraph V) (v : V)
    (hv : G.degree v = 4) (s : Finset V) (hs : s.card ≤ 4)
    (hsub : ∀ y, G.Adj v y → y ∈ s) : ∀ y ∈ s, G.Adj v y := by
  have h1 : G.neighborFinset v ⊆ s := fun y hy => hsub y ((G.mem_neighborFinset v y).1 hy)
  have h2 : G.neighborFinset v = s :=
    Finset.eq_of_subset_of_card_le h1 (by rw [G.card_neighborFinset_eq_degree, hv]; exact hs)
  intro y hy
  rw [← h2] at hy
  exact (G.mem_neighborFinset v y).1 hy
private theorem not_adj_of_four {V : Type u} [Fintype V] {n : ℕ} (G : SimpleGraph V) (v : V)
    (hmax : ∀ w, G.degree w ≤ 4) {X : SimpleGraph (Fin n)} (φ : Fin n → V)
    (hinj : Function.Injective φ) (hφv : ∀ i, φ i ≠ v)
    (hadj : ∀ i j, G.Adj (φ i) (φ j) ↔ X.Adj i j) (j : Fin n) (T : Finset (Fin n))
    (hT : T.card = 4) (hTj : ∀ k ∈ T, X.Adj j k) : ¬ G.Adj v (φ j) := by
  intro hvj
  have hnot : v ∉ T.image φ := by
    intro h
    obtain ⟨k, -, hk⟩ := Finset.mem_image.1 h
    exact hφv k hk
  have h5 : (insert v (T.image φ)).card = 5 := by
    rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective _ hinj, hT]
  have hle := card_le_degree' G (φ j) (insert v (T.image φ)) (by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact hvj.symm
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx
      exact (hadj j k).2 (hTj k hk))
  have := hmax (φ j)
  omega
private theorem branch_c4 {V : Type u} [Fintype V] (G : SimpleGraph V) (v : V)
    (hv : G.degree v = 4) (e : erase G {v} ≃g SimpleGraph.cycleGraph 4) :
    Nonempty (G ≃g wheel5) := by
  obtain ⟨φ, hinj, hφv, hsurj, hadj⟩ := residual_labels G v e
  have hall := adj_all_of_card G v hv (Finset.univ.image φ)
    (Finset.card_image_le.trans (by simp)) (fun y hy => by
      obtain ⟨i, rfl⟩ := hsurj y hy.ne.symm
      exact Finset.mem_image_of_mem _ (Finset.mem_univ _))
  have hva : ∀ i, G.Adj v (φ i) := fun i => hall _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  have hav : ∀ i, G.Adj (φ i) v := fun i => (hva i).symm
  have hφv' : ∀ i, v ≠ φ i := fun i h => hφv i h.symm
  let ψ : Fin 5 → V := ![φ 0, φ 1, φ 2, φ 3, v]
  have hψi : Function.Injective ψ := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [ψ, hinj.eq_iff]
  have hψs : Function.Surjective ψ := by
    intro y
    by_cases hy : y = v
    · exact ⟨4, by simp [ψ, hy]⟩
    obtain ⟨i, rfl⟩ := hsurj y hy
    fin_cases i
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]
  have hmap : ∀ a b, G.Adj (ψ a) (ψ b) ↔ wheel5.Adj a b := by
    intro a b
    fin_cases a <;> fin_cases b <;> simp [ψ, hadj, hva, hav] <;> decide
  exact ⟨(⟨Equiv.ofBijective ψ ⟨hψi, hψs⟩, fun {a b} => hmap a b⟩ : wheel5 ≃g G).symm⟩
private theorem branch_wheel {V : Type u} [Fintype V] (G : SimpleGraph V) (v : V)
    (hv : G.degree v = 4) (hmax : ∀ w, G.degree w ≤ 4) (e : erase G {v} ≃g wheel5) :
    Nonempty (G ≃g octahedron) := by
  obtain ⟨φ, hinj, hφv, hsurj, hadj⟩ := residual_labels G v e
  have hhub : ¬ G.Adj v (φ 4) :=
    not_adj_of_four G v hmax φ hinj hφv hadj 4 {0, 1, 2, 3} (by decide) (by decide)
  have hall := adj_all_of_card G v hv (({0, 1, 2, 3} : Finset (Fin 5)).image φ)
    (Finset.card_image_le.trans (by decide)) (fun y hy => by
      obtain ⟨i, rfl⟩ := hsurj y hy.ne.symm
      fin_cases i
      · exact Finset.mem_image_of_mem _ (by decide)
      · exact Finset.mem_image_of_mem _ (by decide)
      · exact Finset.mem_image_of_mem _ (by decide)
      · exact Finset.mem_image_of_mem _ (by decide)
      · exact absurd hy hhub)
  have hva : ∀ i : Fin 5, i ≠ 4 → G.Adj v (φ i) := by
    intro i hi
    apply hall
    fin_cases i
    · exact Finset.mem_image_of_mem _ (by decide)
    · exact Finset.mem_image_of_mem _ (by decide)
    · exact Finset.mem_image_of_mem _ (by decide)
    · exact Finset.mem_image_of_mem _ (by decide)
    · exact absurd rfl hi
  have hv0 := hva 0 (by decide)
  have hv1 := hva 1 (by decide)
  have hv2 := hva 2 (by decide)
  have hv3 := hva 3 (by decide)
  have hhub' : ¬ G.Adj (φ 4) v := fun h => hhub h.symm
  have hφv' : ∀ i, v ≠ φ i := fun i h => hφv i h.symm
  let ψ : Fin 6 → V := ![v, φ 4, φ 0, φ 2, φ 1, φ 3]
  have hψi : Function.Injective ψ := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [ψ, hinj.eq_iff]
  have hψs : Function.Surjective ψ := by
    intro y
    by_cases hy : y = v
    · exact ⟨0, by simp [ψ, hy]⟩
    obtain ⟨i, rfl⟩ := hsurj y hy
    fin_cases i
    exacts [⟨2, rfl⟩, ⟨4, rfl⟩, ⟨3, rfl⟩, ⟨5, rfl⟩, ⟨1, rfl⟩]
  have hmap : ∀ a b, G.Adj (ψ a) (ψ b) ↔ octahedron.Adj a b := by
    intro a b
    fin_cases a <;> fin_cases b <;>
      simp [ψ, hadj, hv0, hv1, hv2, hv3, hv0.symm, hv1.symm, hv2.symm, hv3.symm, hhub,
        hhub'] <;> decide
  exact ⟨(⟨Equiv.ofBijective ψ ⟨hψi, hψs⟩, fun {a b} => hmap a b⟩ : octahedron ≃g G).symm⟩
private theorem branch_octahedron {V : Type u} [Fintype V] (G : SimpleGraph V) (v : V)
    (hv : G.degree v = 4) (hmax : ∀ w, G.degree w ≤ 4) (e : erase G {v} ≃g octahedron) :
    False := by
  obtain ⟨φ, hinj, hφv, hsurj, hadj⟩ := residual_labels G v e
  obtain ⟨w, hvw⟩ := (G.degree_pos_iff_exists_adj v).1 (by omega)
  obtain ⟨j, rfl⟩ := hsurj w hvw.ne.symm
  have key := not_adj_of_four G v hmax φ hinj hφv hadj
  fin_cases j
  · exact key 0 {2, 3, 4, 5} (by decide) (by decide) hvw
  · exact key 1 {2, 3, 4, 5} (by decide) (by decide) hvw
  · exact key 2 {0, 1, 4, 5} (by decide) (by decide) hvw
  · exact key 3 {0, 1, 4, 5} (by decide) (by decide) hvw
  · exact key 4 {0, 1, 2, 3} (by decide) (by decide) hvw
  · exact key 5 {0, 1, 2, 3} (by decide) (by decide) hvw
end SizeRamsey.Plan
end
end

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
universe u
attribute [local instance] Classical.propDecidable
namespace SizeRamsey.Plan
theorem _root_.solution
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hc : G.Connected)
    (hp : 0 < edgeCount G)
    (hm : edgeCount G ≤ 16)
    (ht : Tight G)
    (ih : SmallerClassified G)
    (h4 : ∃ v, G.degree v = 4) :
    Classified G := by
  obtain ⟨v, hv⟩ := h4
  have hmax := equality_max_degree_le_four G ht
  have hmin := equality_min_degree G hc hp ht
  have hsq := equality_square_supported G ht
  have ht' : 4 * tau4 G = edgeCount G := ht
  obtain ⟨hcnt, -, -⟩ := erase_singleton_counts G v
  obtain ⟨hred, -⟩ := degree_four_reduction G v (by omega)
  obtain ⟨hτ, hcomp⟩ := equality_residual_components G {v} 1 ht (by simpa using hred)
    (by omega)
  obtain ⟨w, hvw⟩ := (G.degree_pos_iff_exists_adj v).1 (by omega)
  let y₀ : {x : V // x ∉ ({v} : Finset V)} := ⟨w, by simpa using hvw.ne.symm⟩
  by_cases hHc : (erase G {v}).Connected
  swap
  · exact (two_component_contra G hc ih v hv hmin hsq hcnt hτ hcomp hHc y₀).elim
  obtain ⟨y₁, hy₁⟩ := ((erase G {v}).degree_pos_iff_exists_adj y₀).1
    (erase_pos_degree G v hmin y₀)
  have hpos := edgeCount_pos_of_adj _ hy₁
  have hcl := ih (erase G {v}) hHc hpos (by omega) (show 4 * tau4 (erase G {v}) =
    edgeCount (erase G {v}) by omega)
  rcases hcl with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact Or.inr (Or.inl (branch_c4 G v hv e))
  · exact Or.inr (Or.inr (Or.inr (branch_wheel G v hv hmax e)))
  · exfalso
    have h2 := k33_extension_tau_le_two G v ⟨e⟩ hv
    have h3 : tau4 (erase G {v}) = 2 := (tau4_iso e).trans small_graph_data.2.2.1.2.1
    omega
  · exact (branch_octahedron G v hv hmax e).elim
end SizeRamsey.Plan
