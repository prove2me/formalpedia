-- Prove2me | solution 1 for SizeRamsey.Plan.equality_mixed_degree_case
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:31:09.054115+00:00
-- url     : https://prove2.me/submissions/6b11709a-1442-4d0a-835c-c06701c8dec5

module
public import Definitions.Def_SizeRamsey_Equality_Common
public import Definitions.Def_SizeRamsey_Equality_Mixed
public import Theorems.Thm_SizeRamsey_Plan_attachment_sum
public import Theorems.Thm_SizeRamsey_Plan_classified_three_degree_two
public import Theorems.Thm_SizeRamsey_Plan_component_attachment_card_ge_two
public import Theorems.Thm_SizeRamsey_Plan_equality_min_degree
public import Theorems.Thm_SizeRamsey_Plan_equality_square_supported
public import Theorems.Thm_SizeRamsey_Plan_erase_degree
public import Theorems.Thm_SizeRamsey_Plan_erase_edgeCount
public import Theorems.Thm_SizeRamsey_Plan_mixed_reduction
public import Theorems.Thm_SizeRamsey_Plan_tight_subcubic_chordless
public import Theorems.Thm_SizeRamsey_Plan_universal
public import Theorems.Thm_SizeRamsey_edgeCount_eq_card

section
@[expose] public section
namespace SizeRamsey.Plan
universe u
attribute [local instance] Classical.propDecidable
private theorem b67_audit_cycle4_arrange (i j k : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hij' : ¬ (SimpleGraph.cycleGraph 4).Adj i j)
    (hik' : (SimpleGraph.cycleGraph 4).Adj i k) :
    ∃ l : Fin 4, Function.Bijective ![i,k,j,l] ∧
      ∀ x y : Fin 4,
        (SimpleGraph.cycleGraph 4).Adj (![i,k,j,l] x) (![i,k,j,l] y) ↔
        (SimpleGraph.cycleGraph 4).Adj x y := by
  have hh : ∀ i j k : Fin 4, i ≠ j → i ≠ k → j ≠ k →
      ¬ (SimpleGraph.cycleGraph 4).Adj i j →
      (SimpleGraph.cycleGraph 4).Adj i k →
      ∃ l : Fin 4, Function.Bijective ![i,k,j,l] ∧
        ∀ x y : Fin 4,
          (SimpleGraph.cycleGraph 4).Adj (![i,k,j,l] x) (![i,k,j,l] y) ↔
          (SimpleGraph.cycleGraph 4).Adj x y := by decide
  exact hh i j k hij hik hjk hij' hik'
private theorem b67_audit_mixed_opposite
    {V : Type*} [Fintype V] (G : SimpleGraph V) (u v : V)
    (a b t : {x : V // x ∉ ({u,v} : Finset V)})
    (_hab : a ≠ b) (_hat : a ≠ t) (hbt : b ≠ t)
    (hNu : ∀ x, G.Adj u x ↔ x = v ∨ x = t.val)
    (hNv : ∀ x, G.Adj v x ↔ x = u ∨ x = a.val ∨ x = b.val)
    (hatAdj : G.Adj a.val t.val)
    (hs : SquareSupported G)
    (e : erase G {u,v} ≃g SimpleGraph.cycleGraph 4) :
    ¬ G.Adj a.val b.val := by
  classical
  have hbv : b.val ≠ v := by
    intro h
    exact b.property (by simp [h])
  have hbtv : b.val ≠ t.val := fun h => hbt (Subtype.ext h)
  have htri : ∀ x y z : {x : V // x ∉ ({u,v} : Finset V)},
      G.Adj x.val y.val → G.Adj x.val z.val → ¬ G.Adj y.val z.val := by
    intro x y z hxy hxz hyz
    have hh : ∀ i j k : Fin 4,
        (SimpleGraph.cycleGraph 4).Adj i j →
        (SimpleGraph.cycleGraph 4).Adj i k →
        ¬ (SimpleGraph.cycleGraph 4).Adj j k := by decide
    exact hh (e x) (e y) (e z) (e.map_rel_iff.mpr hxy)
      (e.map_rel_iff.mpr hxz) (e.map_rel_iff.mpr hyz)
  intro habAdj
  obtain ⟨f, ⟨hinj, h01, h12, h23, h30⟩, hf0, hf1⟩ :=
    hs ((hNv b.val).mpr (Or.inr (Or.inr rfl)))
  have hxv : f 2 ≠ v := by
    rw [← hf0]
    exact hinj.ne (by decide)
  have hyb : f 3 ≠ b.val := by
    rw [← hf1]
    exact hinj.ne (by decide)
  have hy := (hNv (f 3)).mp (by simpa only [hf0] using h30.symm)
  rcases hy with hy | hy | hy
  · have hx := (hNu (f 2)).mp (by simpa only [hy] using h23.symm)
    rcases hx with hx | hx
    · exact hxv hx
    · have hbtAdj : G.Adj b.val t.val := by simpa only [hf1, hx] using h12
      exact htri a b t habAdj hatAdj hbtAdj
  · have hxu : f 2 ≠ u := by
      intro hx
      have hb := (hNu b.val).mp (by simpa only [hf1, hx] using h12.symm)
      exact hb.elim hbv hbtv
    let x : {x : V // x ∉ ({u,v} : Finset V)} := ⟨f 2, by simp [hxu, hxv]⟩
    exact htri a b x habAdj (by simpa only [hy] using h23.symm)
      (by simpa only [hf1] using h12)
  · exact hyb hy
private theorem b67_audit_mixed_normalize
    {V : Type*} [Fintype V] (G : SimpleGraph V) (u v : V)
    (a b t : {x : V // x ∉ ({u,v} : Finset V)})
    (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (hNu : ∀ x, G.Adj u x ↔ x = v ∨ x = t.val)
    (hNv : ∀ x, G.Adj v x ↔ x = u ∨ x = a.val ∨ x = b.val)
    (hatAdj : G.Adj a.val t.val)
    (hs : SquareSupported G)
    (e : erase G {u,v} ≃g SimpleGraph.cycleGraph 4) :
    ∃ q : Fin 4 → {x : V // x ∉ ({u,v} : Finset V)},
      Function.Bijective q ∧ q 0 = a ∧ q 1 = t ∧ q 2 = b ∧
      ∀ i j, G.Adj (q i).val (q j).val ↔
        (SimpleGraph.cycleGraph 4).Adj i j := by
  have hnab := b67_audit_mixed_opposite G u v a b t hab hat hbt hNu hNv hatAdj hs e
  obtain ⟨l, hp, hrel⟩ := b67_audit_cycle4_arrange (e a) (e b) (e t)
    (e.injective.ne hab) (e.injective.ne hat) (e.injective.ne hbt)
    (fun h => hnab (e.map_rel_iff.mp h)) (e.map_rel_iff.mpr hatAdj)
  refine ⟨fun i => e.symm (![e a, e t, e b, l] i), e.symm.bijective.comp hp,
    by simp, by simp, by simp, ?_⟩
  intro i j
  exact e.symm.map_rel_iff.trans (hrel i j)
private theorem b67_mixed_final_labels
    {V : Type u} [Fintype V] (G : SimpleGraph V) (u v : V)
    (huv : u ≠ v)
    (q : Fin 4 → {x : V // x ∉ ({u, v} : Finset V)})
    (hq : Function.Bijective q)
    (hR : ∀ i j, G.Adj (q i).val (q j).val ↔
      (SimpleGraph.cycleGraph 4).Adj i j)
    (hNu : ∀ x, G.Adj u x ↔ x = v ∨ x = (q 1).val)
    (hNv : ∀ x, G.Adj v x ↔ x = u ∨ x = (q 0).val ∨ x = (q 2).val) :
    Nonempty (G ≃g k33MinusEdge) := by
  classical
  have hqu : ∀ i, (q i).val ≠ u := by
    intro i
    have h := (q i).property
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h
    exact h.1
  have hqv : ∀ i, (q i).val ≠ v := by
    intro i
    have h := (q i).property
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h
    exact h.2
  have hqi : Function.Injective (fun i => (q i).val) :=
    fun i j h => hq.1 (Subtype.ext h)
  let f : Fin 6 → V := ![u, (q 0).val, (q 2).val, (q 3).val, v, (q 1).val]
  have hfi : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f, hqi.eq_iff]
  have hfs : Function.Surjective f := by
    intro x
    by_cases hxu : x = u
    · exact ⟨0, hxu.symm⟩
    by_cases hxv : x = v
    · exact ⟨4, hxv.symm⟩
    obtain ⟨i, hi⟩ := hq.2 ⟨x, by simp [hxu, hxv]⟩
    have hi' : (q i).val = x := congrArg Subtype.val hi
    fin_cases i
    · exact ⟨1, hi'⟩
    · exact ⟨5, hi'⟩
    · exact ⟨2, hi'⟩
    · exact ⟨3, hi'⟩
  have huN : ∀ x, G.Adj x u ↔ x = v ∨ x = (q 1).val := by
    intro x
    rw [G.adj_comm, hNu]
  have hvN : ∀ x, G.Adj x v ↔ x = u ∨ x = (q 0).val ∨ x = (q 2).val := by
    intro x
    rw [G.adj_comm, hNv]
  have hadj : ∀ i j, G.Adj (f i) (f j) ↔ k33MinusEdge.Adj i j := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [f, hNu, hNv, huN, hvN, hR, hqi.eq_iff, hqu, hqv,
        k33MinusEdge, graphOfEdges, SimpleGraph.fromRel,
        SimpleGraph.cycleGraph] <;> decide
  let e : k33MinusEdge ≃g G := {
    toEquiv := Equiv.ofBijective f ⟨hfi, hfs⟩
    map_rel_iff' := by intro i j; exact hadj i j }
  exact ⟨e.symm⟩
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
    (hmax : ∀ v, G.degree v ≤ 3)
    (hmix : ∃ u v,
      G.Adj u v ∧ G.degree u = 2 ∧ G.degree v = 3) :
    Nonempty (G ≃g k33MinusEdge) := by
  classical
  obtain ⟨u, v, huv, hdu, hdv⟩ := hmix
  have hsq := equality_square_supported G ht
  obtain ⟨f, hf, hf0, hf1⟩ := hsq huv
  have hdiag := tight_subcubic_chordless G ht hmax f hf
  obtain ⟨hfi, hf01, hf12, hf23, hf30⟩ := hf
  let a := f 2
  let t := f 3
  have hat : G.Adj a t := hf23
  have hva : G.Adj v a := hf1 ▸ hf12
  have htu : G.Adj t u := hf0 ▸ hf30
  have huvne : u ≠ v := huv.ne
  have haut : u ≠ t := by
    intro h
    have : (0 : Fin 4) = 3 := hfi (hf0.trans h)
    contradiction
  have huane : u ≠ a := by
    intro h
    have : (0 : Fin 4) = 2 := hfi (hf0.trans h)
    contradiction
  have hvat : v ≠ t := by
    intro h
    have : (1 : Fin 4) = 3 := hfi (hf1.trans h)
    contradiction
  have hva_ne : v ≠ a := hva.ne
  have hat_ne : a ≠ t := hat.ne
  have hnvt : ¬ G.Adj v t := by
    simpa only [hf1] using hdiag.2
  have hNu : G.neighborFinset u = {v, t} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · simpa using huv
      · simpa using htu.symm
    · rw [G.card_neighborFinset_eq_degree, hdu]
      simp [hvat]
  have hNvcard : (G.neighborFinset v \ {u, a}).card = 1 := by
    rw [Finset.card_sdiff_of_subset]
    · simp [G.card_neighborFinset_eq_degree, hdv, huane]
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · simpa using huv.symm
      · simpa using hva
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hNvcard
  have hbmem : b ∈ G.neighborFinset v \ {u, a} := by rw [hb]; simp
  obtain ⟨hbv, hbua⟩ := Finset.mem_sdiff.mp hbmem
  have hvb : G.Adj v b := by simpa using hbv
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hbua
  have hbune : b ≠ u := hbua.1
  have hbane : b ≠ a := hbua.2
  have hbtne : b ≠ t := by
    rintro rfl
    exact hnvt hvb
  have hNv : G.neighborFinset v = {u, a, b} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · simpa using huv.symm
      · simpa using hva
      · exact hbv
    · rw [G.card_neighborFinset_eq_degree, hdv]
      simp [huane, hbune.symm, hbane.symm]
  have hNu' : ∀ x, G.Adj u x ↔ x = v ∨ x = t := by
    intro x
    rw [← G.mem_neighborFinset, hNu]
    simp
  have hNv' : ∀ x, G.Adj v x ↔ x = u ∨ x = a ∨ x = b := by
    intro x
    rw [← G.mem_neighborFinset, hNv]
    simp
  let D : Finset V := {u, v}
  let H := erase G D
  have haD : a ∉ D := by simp [D, huane.symm, hva_ne.symm]
  have hbD : b ∉ D := by simp [D, hbune, hvb.ne.symm]
  have htD : t ∉ D := by simp [D, haut.symm, hvat.symm]
  let A : {x : V // x ∉ D} := ⟨a, haD⟩
  let B : {x : V // x ∉ D} := ⟨b, hbD⟩
  let T : {x : V // x ∉ D} := ⟨t, htD⟩
  have hmin := equality_min_degree G hc hp ht
  have hcut_le : ∀ x : {x : V // x ∉ D},
      (G.neighborFinset x.val ∩ D).card ≤ 1 := by
    intro x
    have hx : x.val ≠ u ∧ x.val ≠ v := by simpa [D] using x.property
    by_cases hxu : G.Adj x.val u
    · have hxt : x.val = t := (hNu' x.val).mp hxu.symm |>.resolve_left hx.2
      have hsub : G.neighborFinset x.val ∩ D ⊆ {u} := by
        intro y hy
        obtain ⟨hyN, hyD⟩ := Finset.mem_inter.mp hy
        have hxy : G.Adj x.val y := by simpa using hyN
        simp only [D, Finset.mem_insert, Finset.mem_singleton] at hyD
        rcases hyD with rfl | rfl
        · simp
        · exact (hnvt (hxt ▸ hxy.symm)).elim
      exact (Finset.card_le_card hsub).trans (by simp)
    · have hsub : G.neighborFinset x.val ∩ D ⊆ {v} := by
        intro y hy
        obtain ⟨hyN, hyD⟩ := Finset.mem_inter.mp hy
        have hxy : G.Adj x.val y := by simpa using hyN
        simp only [D, Finset.mem_insert, Finset.mem_singleton] at hyD
        rcases hyD with rfl | rfl
        · exact (hxu hxy).elim
        · simp
      exact (Finset.card_le_card hsub).trans (by simp)
  have hHnoiso : ∀ x, 0 < H.degree x := by
    intro x
    have hd := erase_degree G D x
    have hm := hmin x.val
    have hx := hcut_le x
    change H.degree x + _ = _ at hd
    omega
  have hHp : 0 < edgeCount H := by
    have hd := H.degree_le_card_edgeFinset A
    have hp := hHnoiso A
    rw [← edgeCount_eq_card] at hd
    omega
  obtain ⟨hlift, hcount⟩ := mixed_reduction G huv hdu hdv
  change tau4 G ≤ tau4 H + 1 at hlift
  change edgeCount H + 4 = edgeCount G at hcount
  have hHtight : Tight H := by
    have hA := universal H
    unfold Tight at ht ⊢
    omega
  have hDnonempty : D.Nonempty := by simp [D]
  have hDproper : D ≠ Finset.univ := by
    intro h
    exact haD (h.symm ▸ Finset.mem_univ a)
  have hcut2 : ∀ C : H.ConnectedComponent,
      2 ≤ (attachmentEdges G D C).card :=
    component_attachment_card_ge_two G hc hsq D hDnonempty hDproper
  have hcounts := erase_edgeCount G D
  have hdegs : ∑ x ∈ D, G.degree x = 5 := by simp [D, huvne, hdu, hdv]
  rw [hdegs] at hcounts
  change edgeCount H + 5 = edgeCount G + _ at hcounts
  have hinner : edgeCount (G.induce (D : Set V)) = 1 := by omega
  have hsum : ∑ C : H.ConnectedComponent, (attachmentEdges G D C).card = 3 := by
    have hs := attachment_sum G D
    have hs' : (∑ C : H.ConnectedComponent, (attachmentEdges G D C).card) + 2 = 5 := by
      simpa only [hinner, hdegs, Nat.mul_one] using hs
    omega
  have hcompeq : ∀ C C' : H.ConnectedComponent, C = C' := by
    intro C C'
    by_contra hne
    have hle : ∑ K ∈ ({C, C'} : Finset H.ConnectedComponent),
        (attachmentEdges G D K).card ≤
        ∑ K : H.ConnectedComponent, (attachmentEdges G D K).card :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    rw [Finset.sum_pair hne, hsum] at hle
    have hC := hcut2 C
    have hC' := hcut2 C'
    omega
  have hHconn : H.Connected :=
    (SimpleGraph.connected_iff_exists_forall_reachable H).mpr
      ⟨A, fun y => SimpleGraph.ConnectedComponent.exact
        (hcompeq (H.connectedComponentMk A) (H.connectedComponentMk y))⟩
  have hclassified : Classified H := ih H hHconn hHp (by omega) hHtight
  have hHmin := equality_min_degree H hHconn hHp hHtight
  have hdeg_attach : ∀ x : {x : V // x ∉ D},
      (G.Adj x.val u ∨ G.Adj x.val v) → H.degree x = 2 := by
    intro x hx
    have hex : (G.neighborFinset x.val ∩ D).Nonempty := by
      rcases hx with hx | hx
      · exact ⟨u, Finset.mem_inter.mpr ⟨by simpa using hx, by simp [D]⟩⟩
      · exact ⟨v, Finset.mem_inter.mpr ⟨by simpa using hx, by simp [D]⟩⟩
    have hpos := Finset.card_pos.mpr hex
    have hd := erase_degree G D x
    have hle := hmax x.val
    have hge := hHmin x
    change H.degree x + _ = _ at hd
    omega
  have hda : H.degree A = 2 := hdeg_attach A (Or.inr hva.symm)
  have hdb : H.degree B = 2 := hdeg_attach B (Or.inr hvb.symm)
  have hdt : H.degree T = 2 := hdeg_attach T (Or.inl htu)
  obtain ⟨e⟩ := classified_three_degree_two H hclassified A B T
    (by intro h; exact hbane (congrArg Subtype.val h).symm)
    (by intro h; exact hat_ne (congrArg Subtype.val h))
    (by intro h; exact hbtne (congrArg Subtype.val h))
    hda hdb hdt
  obtain ⟨q, hq, hq0, hq1, hq2, hqadj⟩ :=
    b67_audit_mixed_normalize G u v A B T
      (by intro h; exact hbane (congrArg Subtype.val h).symm)
      (by intro h; exact hat_ne (congrArg Subtype.val h))
      (by intro h; exact hbtne (congrArg Subtype.val h))
      hNu' hNv' hat hsq e
  apply b67_mixed_final_labels G u v huvne q hq hqadj
  · simpa only [hq1] using hNu'
  · simpa only [hq0, hq2] using hNv'
end SizeRamsey.Plan
