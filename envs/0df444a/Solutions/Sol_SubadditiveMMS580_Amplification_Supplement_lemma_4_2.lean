-- Prove2me | solution 1 for SubadditiveMMS580.Amplification.Supplement.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T21:36:20.680675+00:00
-- url     : https://prove2.me/submissions/bf437e48-7793-4d7c-972f-353df3a1dc30

import Mathlib
import Definitions.Def_SubadditiveMMS580_Amplification_Supplement_Partitioning
import Definitions.Def_MultiAllocToAlloc_Subadditive_Valuation
import Definitions.Def_MultiAllocToAlloc_Subadditive_Allocation
import Definitions.Def_LittleCharity_MMS_Setting

open MultiAllocToAlloc.Subadditive
open SubadditiveMMS580.Amplification.Supplement
open Finset

theorem SMM42_core {m : ℕ} (q : ℕ) (f : Finset (Fin m) → ℝ)
    (hf : IsQPartitioning q f) (L : ℕ) (S : Finset (Fin m)) (B : Fin L → Finset (Fin m))
    (hdisj : ∀ k l : Fin L, k ≠ l → Disjoint (B k) (B l)) (hsub : ∀ l, B l ⊆ S)
    (T : Finset (Fin L)) (hT : T.card ≤ q) :
    ∑ l ∈ T, (f S - f (S \ B l)) ≤ f S := by
  classical
  obtain ⟨hf0, hmono, hpart⟩ := hf
  have hfS : 0 ≤ f S := by rw [← hf0]; exact hmono ∅ S (empty_subset _) (subset_univ _)
  rcases T.eq_empty_or_nonempty with hTe | ⟨l0, hl0⟩
  · simp [hTe, hfS]
  set R := S \ T.biUnion B with hR
  set part : Fin L → Finset (Fin m) := fun l => if l = l0 then B l ∪ R else B l with hpartdef
  have hBpart : ∀ l, B l ⊆ part l := by
    intro l; simp only [hpartdef]; split_ifs <;> simp
  have hpartS : ∀ l, part l ⊆ S := by
    intro l; simp only [hpartdef]; split_ifs
    · exact union_subset (hsub l) sdiff_subset
    · exact hsub l
  have hRdisj : ∀ l ∈ T, Disjoint R (B l) := by
    intro l hl
    rw [hR]
    exact disjoint_sdiff_self_left.mono_right (subset_biUnion_of_mem B hl)
  have hpdisj : ∀ l ∈ T, ∀ l' ∈ T, l ≠ l' → Disjoint (part l) (part l') := by
    intro l hl l' hl' hne
    simp only [hpartdef]
    split_ifs with h1 h2 h2
    · exact absurd (h1.trans h2.symm) hne
    · exact disjoint_union_left.mpr ⟨hdisj l l' hne, hRdisj l' hl'⟩
    · exact disjoint_union_right.mpr ⟨hdisj l l' hne, (hRdisj l hl).symm⟩
    · exact hdisj l l' hne
  set T' := T.filter (fun l => (part l).Nonempty) with hT'
  have ha0 : ∀ l ∈ T, l ∉ T' → f S - f (S \ B l) = 0 := by
    intro l hl hl'
    have hemp : part l = ∅ := by
      by_contra hne
      exact hl' (mem_filter.mpr ⟨hl, nonempty_iff_ne_empty.mpr hne⟩)
    have : B l = ∅ := subset_empty.mp (hemp ▸ hBpart l)
    rw [this, sdiff_empty, sub_self]
  have hsplit : ∑ l ∈ T, (f S - f (S \ B l)) = ∑ l ∈ T', (f S - f (S \ B l)) := by
    rw [hT']
    rw [sum_filter_of_ne]
    intro l hl hne
    by_contra hemp
    exact hne (ha0 l hl (by
      intro hmem; exact hemp (mem_filter.mp hmem).2))
  rw [hsplit]
  rcases T'.eq_empty_or_nonempty with hT'e | hT'ne
  · rw [hT'e, sum_empty]; exact hfS
  set t := T'.card with ht
  have ht1 : 1 ≤ t := card_pos.mpr hT'ne
  have htq : t ≤ q := (card_filter_le _ _).trans hT
  set e : Fin t ≃ T' := T'.equivFin.symm with he
  set C : Fin t → Finset (Fin m) := fun j => part (e j).1 with hC
  have heT : ∀ j, (e j).1 ∈ T := fun j => (mem_filter.mp (e j).2).1
  have hCne : ∀ j, (C j).Nonempty := fun j => (mem_filter.mp (e j).2).2
  have hCdisj : ∀ j k, j ≠ k → Disjoint (C j) (C k) := by
    intro j k hjk
    apply hpdisj _ (heT j) _ (heT k)
    intro h
    exact hjk (e.injective (Subtype.ext h))
  have hCunion : univ.biUnion C = S := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨j, -, hj⟩ := mem_biUnion.mp hx
      exact hpartS _ hj
    · intro x hxS
      have : ∃ l ∈ T, x ∈ part l := by
        by_cases hxB : x ∈ T.biUnion B
        · obtain ⟨l, hl, hxl⟩ := mem_biUnion.mp hxB
          exact ⟨l, hl, hBpart l hxl⟩
        · refine ⟨l0, hl0, ?_⟩
          simp only [hpartdef, if_true]
          exact mem_union_right _ (mem_sdiff.mpr ⟨hxS, hxB⟩)
      obtain ⟨l, hl, hxl⟩ := this
      have hlT' : l ∈ T' := mem_filter.mpr ⟨hl, ⟨x, hxl⟩⟩
      refine mem_biUnion.mpr ⟨e.symm ⟨l, hlT'⟩, mem_univ _, ?_⟩
      simp only [hC, Equiv.apply_symm_apply]
      exact hxl
  obtain ⟨w, hw0, hwsum, hwJ⟩ := hpart S (subset_univ _) t ht1 htq C hCne hCdisj hCunion
  have hbound : ∀ j, f S - f (S \ B (e j).1) ≤ w j := by
    intro j
    have h1 := hwJ (univ.erase j)
    have h2 : ∑ k ∈ univ.erase j, w k = f S - w j := by
      rw [← hwsum, ← add_sum_erase _ _ (mem_univ j)]; ring
    have h3 : (univ.erase j).biUnion C ⊆ S \ B (e j).1 := by
      intro x hx
      obtain ⟨k, hk, hxk⟩ := mem_biUnion.mp hx
      have hkj : k ≠ j := ne_of_mem_erase hk
      refine mem_sdiff.mpr ⟨hpartS _ hxk, ?_⟩
      intro hxB
      have hd := hCdisj k j hkj
      exact disjoint_left.mp hd hxk (hBpart _ hxB)
    have h4 := hmono _ _ h3 (subset_univ _)
    linarith
  calc ∑ l ∈ T', (f S - f (S \ B l))
      = ∑ x : T', (f S - f (S \ B x.1)) := (sum_coe_sort T' _).symm
    _ = ∑ j : Fin t, (f S - f (S \ B (e j).1)) := (Equiv.sum_comp e (fun x : T' => f S - f (S \ B x.1))).symm
    _ ≤ ∑ j : Fin t, w j := sum_le_sum (fun j _ => hbound j)
    _ = f S := hwsum

theorem solution {m : ℕ} (q : ℕ) (hq : 2 ≤ q) (f : Finset (Fin m) → ℝ)
    (hf : IsQPartitioning q f) (L : ℕ) (S : Finset (Fin m)) (B : Fin L → Finset (Fin m))
    (hdisj : ∀ k l : Fin L, k ≠ l → Disjoint (B k) (B l)) (hsub : ∀ l, B l ⊆ S) :
    ∑ l : Fin L, (f S - f (S \ B l)) ≤ max 1 ((L : ℝ) / q) * f S := by
  classical
  have hfS : 0 ≤ f S := by
    rw [← hf.1]; exact hf.2.1 ∅ S (empty_subset _) (subset_univ _)
  by_cases hLq : L ≤ q
  · have := SMM42_core q f hf L S B hdisj hsub univ (by simpa using hLq)
    calc ∑ l : Fin L, (f S - f (S \ B l)) ≤ f S := this
      _ = 1 * f S := (one_mul _).symm
      _ ≤ max 1 ((L : ℝ) / q) * f S := mul_le_mul_of_nonneg_right (le_max_left _ _) hfS
  · push Not at hLq
    set a : Fin L → ℝ := fun l => f S - f (S \ B l) with ha
    have hcore : ∀ T ∈ (univ : Finset (Fin L)).powersetCard q, ∑ l ∈ T, a l ≤ f S := by
      intro T hT
      exact SMM42_core q f hf L S B hdisj hsub T (mem_powersetCard.mp hT).2.le
    have hsum := sum_le_sum hcore
    rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    have hcount : ∀ l : Fin L,
        ((univ : Finset (Fin L)).powersetCard q).filter (fun T => l ∈ T) =
        ((univ : Finset (Fin L)).powersetCard q).filter (fun T => {l} ⊆ T) := by
      intro l; apply filter_congr; intro T _; exact singleton_subset_iff.symm
    have hdc : ∑ T ∈ (univ : Finset (Fin L)).powersetCard q, ∑ l ∈ T, a l
        = ((L - 1).choose (q - 1) : ℝ) * ∑ l, a l := by
      rw [mul_sum]
      rw [show (∑ T ∈ (univ : Finset (Fin L)).powersetCard q, ∑ l ∈ T, a l)
          = ∑ T ∈ (univ : Finset (Fin L)).powersetCard q, ∑ l, if l ∈ T then a l else 0 by
          apply sum_congr rfl; intro T _; rw [sum_ite_mem, univ_inter]]
      rw [sum_comm]
      apply sum_congr rfl
      intro l _
      rw [← sum_filter, sum_const, nsmul_eq_mul, hcount l,
        card_filter_powersetCard_subset {l} univ q (subset_univ _) (by simp; omega)]
      simp [card_univ, Fintype.card_fin]
    rw [hdc] at hsum
    have hid : L * (L - 1).choose (q - 1) = L.choose q * q := by
      have := Nat.add_one_mul_choose_eq (L - 1) (q - 1)
      rwa [show L - 1 + 1 = L by omega, show q - 1 + 1 = q by omega] at this
    have hidR : (L : ℝ) * ((L - 1).choose (q - 1) : ℝ) = (L.choose q : ℝ) * q := by
      exact_mod_cast hid
    have hCpos : (0 : ℝ) < ((L - 1).choose (q - 1) : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega)
    have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    have hmain : ∑ l, a l ≤ (L : ℝ) / q * f S := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hqpos]
      have h1 : ((L - 1).choose (q - 1) : ℝ) * ((∑ l, a l) * q)
          ≤ ((L - 1).choose (q - 1) : ℝ) * (L * f S) := by
        calc ((L - 1).choose (q - 1) : ℝ) * ((∑ l, a l) * q)
            = (((L - 1).choose (q - 1) : ℝ) * ∑ l, a l) * q := by ring
          _ ≤ ((L.choose q : ℝ) * f S) * q := mul_le_mul_of_nonneg_right hsum hqpos.le
          _ = ((L : ℝ) * ((L - 1).choose (q - 1) : ℝ)) * f S := by rw [hidR]; ring
          _ = ((L - 1).choose (q - 1) : ℝ) * (L * f S) := by ring
      exact le_of_mul_le_mul_left h1 hCpos
    calc ∑ l : Fin L, (f S - f (S \ B l)) = ∑ l, a l := rfl
      _ ≤ (L : ℝ) / q * f S := hmain
      _ ≤ max 1 ((L : ℝ) / q) * f S := mul_le_mul_of_nonneg_right (le_max_right _ _) hfS
