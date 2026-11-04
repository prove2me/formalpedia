-- Prove2me | solution 1 for ReserveLP.ProLPR.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T09:05:18.61221+00:00
-- url     : https://prove2.me/submissions/5d00b802-5d9f-48cc-9d8a-7caa591368e9

import Mathlib
import Definitions.Def_ReserveLP_ProLPR_Model

open ReserveLP.ProLPR Finset

theorem solution {A B : Type} [Fintype A] [Fintype B] [DecidableEq B] (D : DataSet A B)
    (s : A → Profile B → ℝ) (q : B → ℝ → ℝ) (hopt : LPOptimal D s q) :
    ∀ r : B → ℝ, (∀ b, 0 ≤ r b) → rev D r ≤ LPObj D s := by
  classical
  intro r _
  have h0R : (0 : ℝ) ∈ reserves D := by simp [reserves]
  have hbidR : ∀ a b, D.bid a b ∈ reserves D := by
    intro a b; simp only [reserves, mem_insert, mem_image, mem_univ, true_and]
    exact Or.inr (Or.inr ⟨(a, b), rfl⟩)
  let up : ℝ → ℝ := fun x =>
    if h : ((reserves D).filter (fun y => x ≤ y)).Nonempty then ((reserves D).filter (fun y => x ≤ y)).min' h else 0
  have hupR : ∀ x, up x ∈ reserves D := by
    intro x; simp only [up]; split_ifs with h
    · exact (mem_filter.mp (min'_mem _ h)).1
    · exact h0R
  have hup : ∀ x a b, x ≤ D.bid a b → x ≤ up x ∧ up x ≤ D.bid a b := by
    intro x a b hx
    have hmem : D.bid a b ∈ (reserves D).filter (fun y => x ≤ y) := mem_filter.mpr ⟨hbidR a b, hx⟩
    have hne : ((reserves D).filter (fun y => x ≤ y)).Nonempty := ⟨_, hmem⟩
    simp only [up, dif_pos hne]
    exact ⟨(mem_filter.mp (min'_mem _ hne)).2, min'_le _ _ hmem⟩
  let r' : B → ℝ := fun b => if b = D.b0 ∨ b = D.b00 then 0 else up (r b)
  have hr'R : ∀ b, r' b ∈ reserves D := by
    intro b; simp only [r']; split_ifs
    · exact h0R
    · exact hupR _
  have hr'0 : r' D.b0 = 0 := by simp [r']
  have hr'00 : r' D.b00 = 0 := by simp [r']
  have hr'cl : ∀ a b, r b ≤ D.bid a b → r b ≤ r' b ∧ r' b ≤ D.bid a b := by
    intro a b hb
    simp only [r']
    split_ifs with h
    · rcases h with rfl | rfl
      · rw [D.bid_b0] at hb ⊢; exact ⟨hb, le_rfl⟩
      · rw [D.bid_b00] at hb ⊢; exact ⟨hb, le_rfl⟩
    · exact hup _ a b hb
  have hsmall : ∀ b, b = D.b0 ∨ b = D.b00 → r' b = 0 ∧ ∀ a, D.bid a b = 0 := by
    rintro b (rfl | rfl)
    · exact ⟨hr'0, D.bid_b0⟩
    · exact ⟨hr'00, D.bid_b00⟩
  -- profile per auction
  have hP : ∀ a, ∃ p ∈ validProfiles D a, (r' p.1 = p.2.2.1 ∧ r' p.2.1 = p.2.2.2) ∧
      revA D a r ≤ revProfile D a p := by
    intro a
    by_cases hne : (topBidders D a r).Nonempty
    · obtain ⟨w, hw, hweq⟩ := exists_mem_eq_sup' hne (fun w => max (r w) (otherMax D a r w))
      have hwcl : w ∈ cleared D a r := (mem_filter.mp hw).1
      have hwtop : ∀ b ∈ cleared D a r, D.bid a b ≤ D.bid a w := (mem_filter.mp hw).2
      have hwle : r w ≤ D.bid a w := (mem_filter.mp hwcl).2
      let T := ((cleared D a r).erase w) ∪ (({D.b0, D.b00} : Finset B).erase w)
      have hT : T.Nonempty := by
        by_cases h : w = D.b0
        · refine ⟨D.b00, mem_union_right _ ?_⟩
          simp [h, D.b0_ne_b00.symm]
        · exact ⟨D.b0, mem_union_right _ (by simp [Ne.symm h])⟩
      obtain ⟨b2, hb2T, hb2max⟩ := exists_max_image T (D.bid a) hT
      have hb2ne : b2 ≠ w := by
        rcases mem_union.mp hb2T with h | h
        · exact (mem_erase.mp h).1
        · exact (mem_erase.mp h).1
      have hb2prop : D.bid a b2 ≤ D.bid a w ∧ r' b2 ≤ D.bid a b2 := by
        rcases mem_union.mp hb2T with h | h
        · have hc := (mem_erase.mp h).2
          exact ⟨hwtop b2 hc, (hr'cl a b2 (mem_filter.mp hc).2).2⟩
        · have hs : b2 = D.b0 ∨ b2 = D.b00 := by
            have := (mem_erase.mp h).2; simpa using this
          obtain ⟨h1, h2⟩ := hsmall b2 hs
          rw [h1, h2 a]; exact ⟨D.bid_nonneg a w, le_rfl⟩
      refine ⟨(w, b2, r' w, r' b2), ?_, ⟨rfl, rfl⟩, ?_⟩
      · simp only [validProfiles, mem_filter, mem_product, mem_univ, true_and]
        exact ⟨⟨hr'R w, hr'R b2⟩, hb2ne.symm, hb2prop.1, (hr'cl a w hwle).2, hb2prop.2⟩
      · simp only [revA, dif_pos hne, hweq, revProfile]
        have hom : otherMax D a r w ≤ D.bid a b2 := by
          unfold otherMax
          apply max'_le
          intro y hy
          rcases mem_insert.mp hy with rfl | hy
          · exact D.bid_nonneg a b2
          · obtain ⟨b, hb, rfl⟩ := mem_image.mp hy
            exact hb2max b (mem_union_left _ hb)
        have := (hr'cl a w hwle).1
        exact max_le (le_max_of_le_right this) (le_max_of_le_left hom)
    · refine ⟨(D.b0, D.b00, 0, 0), ?_, ⟨hr'0, hr'00⟩, ?_⟩
      · simp only [validProfiles, mem_filter, mem_product, mem_univ, true_and]
        refine ⟨⟨h0R, h0R⟩, D.b0_ne_b00, ?_, ?_, ?_⟩ <;> simp [D.bid_b0, D.bid_b00]
      · simp only [revA, dif_neg hne, revProfile]
        exact le_max_of_le_left (D.bid_nonneg a _)
  choose P hPv hPc hPrev using hP
  let s1 : A → Profile B → ℝ := fun a p => if p = P a then 1 else 0
  let q1 : B → ℝ → ℝ := fun b x => if x = r' b then 1 else 0
  have hfeas : LPFeasible D s1 q1 := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro a p _; simp only [s1]; split_ifs <;> norm_num
    · intro a; simp only [s1]; rw [sum_ite_eq' _ _ (fun _ => (1:ℝ))]; split_ifs <;> norm_num
    · intro a b x _
      simp only [s1, q1]
      rw [sum_ite_eq' _ _ (fun _ => (1:ℝ))]
      split_ifs with h1 h2
      · exact le_rfl
      · exfalso; apply h2
        simp only [Qset, mem_filter] at h1
        rcases h1.2 with ⟨hb, hx⟩ | ⟨hb, hx⟩
        · rw [← hx, ← (hPc a).2, hb]
        · rw [← hx, ← (hPc a).1, hb]
      · norm_num
      · norm_num
    · intro b; simp only [q1]; rw [sum_ite_eq' _ _ (fun _ => (1:ℝ))]; simp [hr'R b]
    · intro b x _; simp only [q1]; split_ifs <;> norm_num
  have hobj : rev D r ≤ LPObj D s1 := by
    unfold rev LPObj
    apply sum_le_sum
    intro a _
    simp only [s1, ite_mul, one_mul, zero_mul]
    rw [sum_ite_eq' _ _ (fun p => revProfile D a p), if_pos (hPv a)]
    exact hPrev a
  exact hobj.trans (hopt.2 s1 q1 hfeas)
