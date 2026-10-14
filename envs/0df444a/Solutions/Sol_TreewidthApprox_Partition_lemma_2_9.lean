-- Prove2me | solution 1 for TreewidthApprox.Partition.lemma_2_9
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:36:41.762875+00:00
-- url     : https://prove2.me/submissions/6afc1e65-1c16-41fb-9679-1c06da3b3d59

import Mathlib
import Definitions.Def_TreewidthApprox_Partition_Setting
import Theorems.Thm_TreewidthApprox_Partition_comp_subset_part

open TreewidthApprox.Partition TreewidthApprox.Pushed

private theorem three_partition {α : Type} [DecidableEq α] (s : Finset α)
    (a : α → ℕ) (q : ℕ) (hq : ∑ i ∈ s, a i ≤ q)
    (ha : ∀ i ∈ s, 2*a i ≤ q) :
    ∃ c : α → Fin 3, ∀ j : Fin 3, 2 * ∑ i ∈ s.filter (fun i => c i=j), a i ≤ q := by
  classical
  induction s using Finset.strongInductionOn generalizing a with
  | _ s ih =>
    by_cases hsmall : s.card ≤ 3
    · obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
        (show Fintype.card s ≤ Fintype.card (Fin 3) by simpa using hsmall)
      let c : α → Fin 3 := fun x => if hx : x ∈ s then e ⟨x,hx⟩ else 0
      refine ⟨c,fun j => ?_⟩
      by_cases he : (s.filter (fun x => c x=j)).Nonempty
      · obtain ⟨i,hi⟩ := he
        have his := (Finset.mem_filter.mp hi).1
        have hci := (Finset.mem_filter.mp hi).2
        have hsingle : s.filter (fun x => c x=j) = {i} := by
          apply Finset.ext
          intro x
          constructor
          · intro hx
            obtain ⟨hxs,hcx⟩ := Finset.mem_filter.mp hx
            have heq : e ⟨x,hxs⟩ = e ⟨i,his⟩ := by
              simpa only [c, dif_pos hxs, dif_pos his] using hcx.trans hci.symm
            have : x=i := congrArg Subtype.val (e.injective heq)
            simpa using this
          · intro hx
            have hxi := Finset.mem_singleton.mp hx
            subst x
            exact hi
        rw [hsingle,Finset.sum_singleton]
        exact ha i his
      · rw [Finset.not_nonempty_iff_eq_empty.mp he]
        simp
    · have hs4 : 4 ≤ s.card := by omega
      obtain ⟨i,hi,hmini⟩ := s.exists_min_image a (Finset.card_pos.mp (by omega))
      have he : (s.erase i).Nonempty := by
        apply Finset.card_pos.mp
        rw [Finset.card_erase_of_mem hi]
        omega
      obtain ⟨j,hj',hminj⟩ := (s.erase i).exists_min_image a he
      have hj := Finset.mem_of_mem_erase hj'
      have hji := (Finset.mem_erase.mp hj').1
      have hij := Ne.symm hji
      have hrest : 1 < ((s.erase i).erase j).card := by
        rw [Finset.card_erase_of_mem hj',Finset.card_erase_of_mem hi]
        omega
      obtain ⟨k,hk,l,hl,hkl⟩ := Finset.one_lt_card.mp hrest
      have hki := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
      have hkj := (Finset.mem_erase.mp hk).1
      have hli := (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1
      have hlj := (Finset.mem_erase.mp hl).1
      have hk' := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hk)
      have hl' := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hl)
      have hbnd : 2*(a i+a j) ≤ q := by
        have hs : a i+a j+a k+a l ≤ ∑ x ∈ s,a x := by
          have ht := Finset.sum_le_sum_of_subset (f:=a)
            (show ({i,j,k,l}:Finset α) ⊆ s by simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro hi (And.intro hj (And.intro hk' hl')))
          simpa [hij,Ne.symm hki,Ne.symm hli,Ne.symm hkj,Ne.symm hlj,hkl,add_assoc] using ht
        have hik := hmini k hk'
        have hjl := hminj l (Finset.mem_erase.mpr ⟨hli,hl'⟩)
        omega
      let b := Function.update a i (a i+a j)
      have hi' : i ∈ s.erase j := Finset.mem_erase.mpr ⟨hij,hi⟩
      have hsum : (∑ x ∈ s.erase j,b x) = ∑ x ∈ s,a x := by
        rw [← Finset.sum_erase_add (s.erase j) b hi', ← Finset.sum_erase_add s a hj,
          ← Finset.sum_erase_add (s.erase j) a hi']
        have heq : (∑ x ∈ (s.erase j).erase i,b x) = ∑ x ∈ (s.erase j).erase i,a x := by
          apply Finset.sum_congr rfl
          intro x hx
          exact Function.update_of_ne (Finset.mem_erase.mp hx).1 _ _
        rw [heq]
        simp [b,add_assoc]
      obtain ⟨c,hc⟩ := ih (s.erase j) (Finset.erase_ssubset hj) b
        (by rw [hsum]; exact hq) (by
          intro x hx
          by_cases hxi : x=i
          · subst x; simpa [b] using hbnd
          · simpa [b,Function.update_of_ne hxi] using ha x (Finset.mem_of_mem_erase hx))
      let c' := Function.update c j (c i)
      refine ⟨c',fun r => ?_⟩
      have heq : (∑ x ∈ s.filter (fun x => c' x=r),a x) =
          ∑ x ∈ (s.erase j).filter (fun x => c x=r),b x := by
        simp only [Finset.sum_filter]
        let f : α → ℕ := fun x => if c' x=r then a x else 0
        let g : α → ℕ := fun x => if c x=r then b x else 0
        change (∑ x ∈ s,f x) = ∑ x ∈ s.erase j,g x
        rw [← Finset.sum_erase_add s f hj, ← Finset.sum_erase_add (s.erase j) f hi',
          ← Finset.sum_erase_add (s.erase j) g hi']
        have hfg : (∑ x ∈ (s.erase j).erase i,f x) = ∑ x ∈ (s.erase j).erase i,g x := by
          apply Finset.sum_congr rfl
          intro x hx
          have hxi := (Finset.mem_erase.mp hx).1
          have hxj := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
          simp [f,g,c',b,Function.update_of_ne hxi,Function.update_of_ne hxj]
        rw [hfg]
        by_cases hcr : c i=r <;> simp [f,g,c',b,hij,hcr,add_assoc]
      rw [heq]
      exact hc r


private theorem ar_refl {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (X : Finset V) (u : V) (hu : u ∉ X) : AvoidReach G X u u := by
  exact ⟨.nil, by simpa using hu⟩

private theorem ar_symm {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (X : Finset V) {u v : V} (h : AvoidReach G X u v) : AvoidReach G X v u := by
  obtain ⟨p,hp⟩ := h
  exact ⟨p.reverse, by simpa using hp⟩

private theorem ar_trans {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (X : Finset V) {u v w : V}
    (h : AvoidReach G X u v) (h' : AvoidReach G X v w) : AvoidReach G X u w := by
  obtain ⟨p,hp⟩ := h
  obtain ⟨q,hq⟩ := h'
  refine ⟨p.append q, ?_⟩
  intro z hz
  rcases (by simpa using hz : z ∈ p.support ∨ z ∈ q.support) with h | h
  · exact hp z h
  · exact hq z h

private theorem ar_comp_eq {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (X : Finset V) {u v : V} (h : AvoidReach G X u v) :
    avoidComp G X u = avoidComp G X v := by
  classical
  ext w
  simp only [avoidComp,Finset.mem_filter,Finset.mem_univ,true_and]
  exact ⟨fun hw => ar_trans G X (ar_symm G X h) hw, ar_trans G X h⟩

private theorem comp_outside {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (X : Finset V) (u : V) : avoidComp G X u ⊆ Finset.univ \ X := by
  classical
  intro v hv
  obtain ⟨p,hp⟩ := (Finset.mem_filter.mp hv).2
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hp v p.end_mem_support⟩


theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S X : Finset V) :
    IsBalancedSSep G S X ↔
      ∃ M₁ M₂ M₃ : Finset V,
        Disjoint M₁ M₂ ∧ Disjoint M₁ M₃ ∧ Disjoint M₂ M₃ ∧
        M₁ ∪ M₂ ∪ M₃ = Finset.univ \ X ∧
        TreewidthApprox.Pushed.NoEdge G M₁ M₂ ∧ TreewidthApprox.Pushed.NoEdge G M₁ M₃ ∧ TreewidthApprox.Pushed.NoEdge G M₂ M₃ ∧
        2 * (M₁ ∩ S).card ≤ S.card ∧
        2 * (M₂ ∩ S).card ≤ S.card ∧
        2 * (M₃ ∩ S).card ≤ S.card := by
  classical
  constructor
  · intro hbal
    let Cs : Finset (Finset V) := (Finset.univ \ X).image (avoidComp G X)
    have hrepr (C : Finset V) (hC : C ∈ Cs) : ∃ u ∉ X, avoidComp G X u=C := by
      obtain ⟨u,hu,he⟩ := Finset.mem_image.mp hC
      exact ⟨u,(Finset.mem_sdiff.mp hu).2,he⟩
    have hout (C : Finset V) (hC : C ∈ Cs) : C ⊆ Finset.univ \ X := by
      obtain ⟨u,hu,rfl⟩ := hrepr C hC
      exact comp_outside G X u
    have hcomp (C : Finset V) (hC : C ∈ Cs) (v : V) (hv : v ∈ C) : avoidComp G X v=C := by
      obtain ⟨u,hu,rfl⟩ := hrepr C hC
      exact (ar_comp_eq G X (Finset.mem_filter.mp hv).2).symm
    have hdis : (Cs : Set (Finset V)).PairwiseDisjoint id := by
      intro C hC D hD hCD
      apply Finset.disjoint_left.mpr
      intro v hv hv'
      exact hCD ((hcomp C hC v hv).symm.trans (hcomp D hD v hv'))
    have hcover (v : V) (hv : v ∉ X) : ∃ C ∈ Cs,v ∈ C := by
      refine ⟨avoidComp G X v,?_,?_⟩
      · exact Finset.mem_image.mpr ⟨v,by simp [hv],rfl⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ar_refl G X v hv⟩
    have hweight : (∑ C ∈ Cs,(C ∩ S).card) ≤ S.card := by
      have hd : (Cs : Set (Finset V)).PairwiseDisjoint (fun C => C ∩ S) := by
        intro C hC D hD hCD
        exact (hdis hC hD hCD).mono (Finset.inter_subset_left) (Finset.inter_subset_left)
      rw [← Finset.card_biUnion hd]
      apply Finset.card_le_card
      intro v hv
      obtain ⟨C,hC,hv⟩ := Finset.mem_biUnion.mp hv
      exact (Finset.mem_inter.mp hv).2
    obtain ⟨c,hc⟩ := three_partition Cs (fun C => (C ∩ S).card) S.card hweight (by
      intro C hC
      obtain ⟨u,hu,rfl⟩ := hrepr C hC
      exact hbal u hu)
    let M (r : Fin 3) : Finset V := (Cs.filter (fun C => c C=r)).biUnion id
    have hmem (r : Fin 3) (v : V) : v ∈ M r ↔ ∃ C ∈ Cs, c C=r ∧ v ∈ C := by
      simp only [M,Finset.mem_biUnion,Finset.mem_filter,id_eq]
      aesop
    have hMout (r : Fin 3) : M r ⊆ Finset.univ \ X := by
      intro v hv
      obtain ⟨C,hC,hr,hv⟩ := (hmem r v).mp hv
      exact hout C hC hv
    have hMd (r t : Fin 3) (hrt : r ≠ t) : Disjoint (M r) (M t) := by
      apply Finset.disjoint_left.mpr
      intro v hv hv'
      obtain ⟨C,hC,hr,hv⟩ := (hmem r v).mp hv
      obtain ⟨D,hD,ht,hv'⟩ := (hmem t v).mp hv'
      have he : C=D := (hcomp C hC v hv).symm.trans (hcomp D hD v hv')
      exact hrt (hr.symm.trans ((congrArg c he).trans ht))
    have hMe (r t : Fin 3) (hrt : r ≠ t) : NoEdge G (M r) (M t) := by
      intro v hv w hw hvw
      have hvX := (Finset.mem_sdiff.mp (hMout r hv)).2
      have hwX := (Finset.mem_sdiff.mp (hMout t hw)).2
      obtain ⟨C,hC,hr,hv⟩ := (hmem r v).mp hv
      obtain ⟨D,hD,ht,hw⟩ := (hmem t w).mp hw
      have har : AvoidReach G X v w := ⟨.cons hvw .nil, by simpa using And.intro hvX hwX⟩
      have he : C=D := (hcomp C hC v hv).symm.trans
        ((ar_comp_eq G X har).trans (hcomp D hD w hw))
      exact hrt (hr.symm.trans ((congrArg c he).trans ht))
    have hMc (r : Fin 3) : 2*((M r) ∩ S).card ≤ S.card := by
      have hd : ((Cs.filter (fun C => c C=r)) : Set (Finset V)).PairwiseDisjoint
          (fun C => C ∩ S) := by
        intro C hC D hD hCD
        exact (hdis (Finset.mem_filter.mp hC).1 (Finset.mem_filter.mp hD).1 hCD).mono
          Finset.inter_subset_left Finset.inter_subset_left
      have he : M r ∩ S = (Cs.filter (fun C => c C=r)).biUnion (fun C => C ∩ S) :=
        Finset.biUnion_inter _ _ _
      rw [he,Finset.card_biUnion hd]
      exact hc r
    refine ⟨M 0,M 1,M 2,hMd 0 1 (by decide),hMd 0 2 (by decide),hMd 1 2 (by decide),
      ?_,hMe 0 1 (by decide),hMe 0 2 (by decide),hMe 1 2 (by decide),hMc 0,hMc 1,hMc 2⟩
    apply Finset.ext
    intro v
    constructor
    · intro hv
      rcases Finset.mem_union.mp hv with hv | hv
      · rcases Finset.mem_union.mp hv with hv | hv
        · exact hMout 0 hv
        · exact hMout 1 hv
      · exact hMout 2 hv
    · intro hv
      obtain ⟨C,hC,hvC⟩ := hcover v (Finset.mem_sdiff.mp hv).2
      have hm : v ∈ M (c C) := (hmem _ _).mpr ⟨C,hC,rfl,hvC⟩
      generalize hr : c C = r at hm
      fin_cases r <;> simp_all
  · rintro ⟨M₁,M₂,M₃,hd12,hd13,hd23,hunion,he12,he13,he23,hb1,hb2,hb3⟩
    obtain ⟨hc1,hc2,hc3⟩ := comp_subset_part G X M₁ M₂ M₃
      ⟨hd12,hd13,hd23,hunion⟩ ⟨he12,he13,he23⟩
    intro u hu
    have hmem : u ∈ M₁ ∨ u ∈ M₂ ∨ u ∈ M₃ := by
      have hh : u ∈ M₁ ∪ M₂ ∪ M₃ := by rw [hunion]; simp [hu]
      simpa [or_assoc] using hh
    have hb (M : Finset V) (hc : avoidComp G X u ⊆ M) (hM : 2*(M ∩ S).card ≤ S.card) :
        2*(avoidComp G X u ∩ S).card ≤ S.card := by
      apply le_trans (Nat.mul_le_mul_left 2 (Finset.card_le_card ?_)) hM
      intro v hv
      exact Finset.mem_inter.mpr ⟨hc (Finset.mem_inter.mp hv).1,(Finset.mem_inter.mp hv).2⟩
    rcases hmem with h | h | h
    · exact hb M₁ (hc1 u h) hb1
    · exact hb M₂ (hc2 u h) hb2
    · exact hb M₃ (hc3 u h) hb3
