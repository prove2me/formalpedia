-- Prove2me | solution 1 for TreewidthApprox.Partition.lemma_6_3
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:34:28.703593+00:00
-- url     : https://prove2.me/submissions/d8005fda-b1a3-4723-8519-1c488ce1ce28

import Mathlib



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


theorem solution (p : ℕ) (a : Fin p → ℕ) (q : ℕ)
    (hq : ∑ i, a i = q) (ha : ∀ i, 2 * a i ≤ q) :
    ∃ c : Fin p → Fin 3,
      ∀ j : Fin 3, 2 * ∑ i ∈ Finset.univ.filter (fun i => c i = j), a i ≤ q := by
  exact three_partition Finset.univ a q hq.le (fun i _ => ha i)
