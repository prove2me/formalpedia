-- Prove2me | solution 1 for StrategicAlloc.CutChoose.theorem_4_3
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-10-15T18:03:01.932227+00:00
-- url     : https://prove2.me/submissions/c7b60087-8930-4f02-85d8-7abebd1cdd58

import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_StrategicAlloc_CutChoose_Setting
import Definitions.Def_StrategicAlloc_CutChoose_ModCutChoose

namespace StrategicAlloc.CutChoose

open StrategicAlloc.RRFair
open Finset hiding val

variable {m : ℕ}

/-- One step of the greedy cut. -/
noncomputable def step (c : Fin m → ℝ) (E : Finset (Fin m) × Finset (Fin m)) (h : Fin m) :
    Finset (Fin m) × Finset (Fin m) :=
  if ∑ g ∈ E.1, c g ≤ ∑ g ∈ E.2, c g then (insert h E.1, E.2) else (E.1, insert h E.2)

lemma cut_eq (c : Fin m → ℝ) : cut c = (rank c).foldl (step c) (∅, ∅) := rfl

lemma rank_perm (c : Fin m → ℝ) : (rank c).Perm (List.finRange m) := List.mergeSort_perm _ _

lemma rank_nodup (c : Fin m → ℝ) : (rank c).Nodup :=
  (rank_perm c).nodup_iff.2 (List.nodup_finRange m)

lemma mem_rank (c : Fin m → ℝ) (x : Fin m) : x ∈ rank c :=
  (rank_perm c).mem_iff.2 (List.mem_finRange x)

lemma rank_pairwise (c : Fin m → ℝ) : (rank c).Pairwise (fun g h => c h ≤ c g) := by
  have := List.pairwise_mergeSort (le := fun g h => decide (c h ≤ c g)) ?_ ?_ (List.finRange m)
  · unfold rank
    exact this.imp (by intro a b h; simpa using h)
  · intro a b d h1 h2
    simp only [decide_eq_true_eq] at *
    linarith
  · intro a b
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact le_total _ _

lemma fold_zero (c : Fin m → ℝ) : ∀ (l : List (Fin m)) (E : Finset (Fin m) × Finset (Fin m)),
    (∀ h ∈ l, c h = 0) → ∑ g ∈ E.1, c g ≤ ∑ g ∈ E.2, c g →
    l.foldl (step c) E = (E.1 ∪ l.toFinset, E.2)
  | [], E, _, _ => by simp
  | h :: t, E, hz, hle => by
    rw [List.foldl_cons]
    have hs : step c E h = (insert h E.1, E.2) := if_pos hle
    rw [hs]
    have hsum : ∑ g ∈ insert h E.1, c g = ∑ g ∈ E.1, c g := by
      by_cases hm : h ∈ E.1
      · rw [Finset.insert_eq_of_mem hm]
      · rw [Finset.sum_insert hm, hz h (by simp), zero_add]
    rw [fold_zero c t _ (fun x hx => hz x (by simp [hx])) (by simpa [hsum] using hle)]
    refine Prod.ext ?_ rfl
    ext x
    simp only [mem_union, mem_insert, List.mem_toFinset, List.mem_cons]
    tauto

lemma fold_zero' (c : Fin m → ℝ) : ∀ (l : List (Fin m)) (E : Finset (Fin m) × Finset (Fin m)),
    (∀ h ∈ l, c h = 0) → ∑ g ∈ E.2, c g < ∑ g ∈ E.1, c g →
    l.foldl (step c) E = (E.1, E.2 ∪ l.toFinset)
  | [], E, _, _ => by simp
  | h :: t, E, hz, hlt => by
    rw [List.foldl_cons]
    have hs : step c E h = (E.1, insert h E.2) := if_neg (not_le.2 hlt)
    rw [hs]
    have hsum : ∑ g ∈ insert h E.2, c g = ∑ g ∈ E.2, c g := by
      by_cases hm : h ∈ E.2
      · rw [Finset.insert_eq_of_mem hm]
      · rw [Finset.sum_insert hm, hz h (by simp), zero_add]
    rw [fold_zero' c t _ (fun x hx => hz x (by simp [hx])) (by simpa [hsum] using hlt)]
    refine Prod.ext rfl ?_
    ext x
    simp only [mem_union, mem_insert, List.mem_toFinset, List.mem_cons]
    tauto

lemma fold_one (c : Fin m → ℝ) (T : Finset (Fin m)) :
    ∀ (l : List (Fin m)) (E : Finset (Fin m) × Finset (Fin m)),
    l.Nodup → l.Pairwise (fun g h => c h ≤ c g) →
    (∀ h ∈ l, (h ∈ T → c h = 1) ∧ (h ∉ T → c h = 0)) →
    (∀ h ∈ l, h ∉ E.2) →
    ∑ g ∈ E.1, c g = ∑ g ∈ E.2, c g + ((l.toFinset ∩ T).card : ℝ) →
    l.foldl (step c) E = (E.1 ∪ (l.toFinset \ T), E.2 ∪ (l.toFinset ∩ T))
  | [], E, _, _, _, _, _ => by simp
  | h :: t, E, hnd, hpw, hc, hE, hsum => by
    rw [List.nodup_cons] at hnd
    rw [List.pairwise_cons] at hpw
    by_cases hT : h ∈ T
    · have hch : c h = 1 := (hc h (by simp)).1 hT
      have hcard : ((h :: t).toFinset ∩ T).card = (t.toFinset ∩ T).card + 1 := by
        rw [List.toFinset_cons, Finset.insert_inter_of_mem hT, Finset.card_insert_of_notMem]
        simp [hnd.1]
      rw [List.foldl_cons]
      have hlt : ¬ (∑ g ∈ E.1, c g ≤ ∑ g ∈ E.2, c g) := by
        rw [hsum, hcard]
        push_cast
        have : (0:ℝ) ≤ ((t.toFinset ∩ T).card : ℝ) := Nat.cast_nonneg _
        linarith
      have hs : step c E h = (E.1, insert h E.2) := if_neg hlt
      rw [hs]
      have hE2 : h ∉ E.2 := hE h (by simp)
      rw [fold_one c T t (E.1, insert h E.2) hnd.2 hpw.2 (fun x hx => hc x (by simp [hx])) ?_ ?_]
      · refine Prod.ext ?_ ?_
        · ext x
          simp only [mem_union, mem_sdiff, List.mem_toFinset, List.mem_cons]
          constructor
          · rintro (h1 | ⟨h1, h2⟩)
            · exact Or.inl h1
            · exact Or.inr ⟨Or.inr h1, h2⟩
          · rintro (h1 | ⟨h1 | h1, h2⟩)
            · exact Or.inl h1
            · exact absurd (h1 ▸ hT) h2
            · exact Or.inr ⟨h1, h2⟩
        · ext x
          simp only [mem_union, mem_insert, mem_inter, List.mem_toFinset, List.mem_cons]
          constructor
          · rintro ((h1 | h1) | ⟨h1, h2⟩)
            · exact Or.inr ⟨Or.inl h1, h1 ▸ hT⟩
            · exact Or.inl h1
            · exact Or.inr ⟨Or.inr h1, h2⟩
          · rintro (h1 | ⟨h1 | h1, h2⟩)
            · exact Or.inl (Or.inr h1)
            · exact Or.inl (Or.inl h1)
            · exact Or.inr ⟨h1, h2⟩
      · intro x hx
        simp only [mem_insert, not_or]
        exact ⟨fun e => hnd.1 (e ▸ hx), hE x (by simp [hx])⟩
      · simp only
        rw [Finset.sum_insert hE2, hch, hsum, hcard]
        push_cast
        ring
    · have hch : c h = 0 := (hc h (by simp)).2 hT
      have hall : ∀ x ∈ h :: t, c x = 0 := by
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hch
        have h1 := hpw.1 x hx
        rw [hch] at h1
        by_cases hxT : x ∈ T
        · have := (hc x (by simp [hx])).1 hxT
          linarith
        · exact (hc x (by simp [hx])).2 hxT
      have hnT : ∀ x ∈ h :: t, x ∉ T := by
        intro x hx hxT
        have h1 := (hc x hx).1 hxT
        have h2 := hall x hx
        linarith
      have hinter : (h :: t).toFinset ∩ T = ∅ := by
        ext x
        simp only [mem_inter, List.mem_toFinset, Finset.notMem_empty, iff_false, not_and]
        exact fun hx => hnT x hx
      rw [hinter] at hsum ⊢
      simp only [Finset.card_empty, Nat.cast_zero, add_zero] at hsum
      rw [fold_zero c (h :: t) E hall (le_of_eq hsum)]
      refine Prod.ext ?_ (by simp)
      ext x
      simp only [mem_union, mem_sdiff, List.mem_toFinset]
      constructor
      · rintro (h1 | h1)
        · exact Or.inl h1
        · exact Or.inr ⟨h1, hnT x h1⟩
      · rintro (h1 | ⟨h1, _⟩)
        · exact Or.inl h1
        · exact Or.inr h1

lemma fold_part (c : Fin m → ℝ) : ∀ (l : List (Fin m)) (E : Finset (Fin m) × Finset (Fin m)),
    l.Nodup → (∀ h ∈ l, h ∉ E.1 ∧ h ∉ E.2) → Disjoint E.1 E.2 →
    Disjoint (l.foldl (step c) E).1 (l.foldl (step c) E).2 ∧
      (l.foldl (step c) E).1 ∪ (l.foldl (step c) E).2 = E.1 ∪ E.2 ∪ l.toFinset
  | [], E, _, _, hd => by simp [hd]
  | h :: t, E, hnd, hE, hd => by
    rw [List.nodup_cons] at hnd
    have hh := hE h (by simp)
    have ht : ∀ x ∈ t, x ≠ h := fun x hx e => hnd.1 (e ▸ hx)
    rw [List.foldl_cons]
    by_cases hle : ∑ g ∈ E.1, c g ≤ ∑ g ∈ E.2, c g
    · rw [show step c E h = (insert h E.1, E.2) from if_pos hle]
      obtain ⟨h1, h2⟩ := fold_part c t (insert h E.1, E.2) hnd.2 (by
        intro x hx
        simp only [mem_insert, not_or]
        exact ⟨⟨ht x hx, (hE x (by simp [hx])).1⟩, (hE x (by simp [hx])).2⟩)
        (by simp only [disjoint_insert_left]; exact ⟨hh.2, hd⟩)
      refine ⟨h1, ?_⟩
      rw [h2]
      ext x
      simp only [mem_union, mem_insert, List.mem_toFinset, List.mem_cons]
      tauto
    · rw [show step c E h = (E.1, insert h E.2) from if_neg hle]
      obtain ⟨h1, h2⟩ := fold_part c t (E.1, insert h E.2) hnd.2 (by
        intro x hx
        simp only [mem_insert, not_or]
        exact ⟨(hE x (by simp [hx])).1, ⟨ht x hx, (hE x (by simp [hx])).2⟩⟩)
        (by simp only [disjoint_insert_right]; exact ⟨hh.1, hd⟩)
      refine ⟨h1, ?_⟩
      rw [h2]
      ext x
      simp only [mem_union, mem_insert, List.mem_toFinset, List.mem_cons]
      tauto

lemma cut_part (c : Fin m → ℝ) : (cut c).2 = univ \ (cut c).1 := by
  obtain ⟨h1, h2⟩ := fold_part c (rank c) (∅, ∅) (rank_nodup c) (by simp) (by simp)
  rw [cut_eq]
  ext x
  have hx : x ∈ (List.foldl (step c) (∅, ∅) (rank c)).1 ∪ (List.foldl (step c) (∅, ∅) (rank c)).2 := by
    rw [h2]; simp [mem_rank]
  rw [mem_union] at hx
  simp only [mem_sdiff, mem_univ, true_and]
  constructor
  · intro h3 h4
    exact Finset.disjoint_left.1 h1 h4 h3
  · intro h3
    tauto

lemma head_of_max (c : Fin m → ℝ) (x : Fin m) (hx : ∀ y, y ≠ x → c y < c x) :
    ∃ t, rank c = x :: t := by
  have hpw := rank_pairwise c
  have hmem := mem_rank c x
  generalize rank c = l at hpw hmem ⊢
  cases l with
  | nil => simp at hmem
  | cons a t =>
    by_cases hax : a = x
    · exact ⟨t, by rw [hax]⟩
    · have hxt : x ∈ t := by
        rcases List.mem_cons.1 hmem with h | h
        · exact absurd h.symm hax
        · exact h
      have h1 := (List.pairwise_cons.1 hpw).1 x hxt
      have h2 := hx a hax
      linarith

lemma cut_zero : cut (fun _ : Fin m => (0:ℝ)) = (univ, ∅) := by
  rw [cut_eq, fold_zero _ _ _ (fun _ _ => rfl) (by simp)]
  ext x <;> simp [mem_rank]

lemma cut_realize (P : Finset (Fin m)) : ∃ c : Fin m → ℝ, (∀ g, 0 ≤ c g) ∧
    (cut c = (P, univ \ P) ∨ cut c = (univ \ P, P)) := by
  classical
  by_cases hP : P = ∅
  · refine ⟨fun _ => 0, fun _ => le_refl _, Or.inr ?_⟩
    rw [cut_zero, hP]; simp
  obtain ⟨x1, hx1⟩ := Finset.nonempty_iff_ne_empty.2 hP
  set T := univ \ P with hTdef
  have hmemT : ∀ x, x ∈ T ↔ x ∉ P := by intro x; simp [hTdef]
  rcases Nat.lt_or_ge T.card 2 with hb | hb
  · interval_cases hcard : T.card
    · -- T empty
      refine ⟨fun _ => 0, fun _ => le_refl _, Or.inl ?_⟩
      rw [cut_zero]
      have hT : T = ∅ := Finset.card_eq_zero.1 hcard
      have hPu : P = univ := by
        ext x; simp only [mem_univ, iff_true]; by_contra hx; rw [← hmemT] at hx; simp [hT] at hx
      exact Prod.ext (by simp [hPu]) hT.symm
    · obtain ⟨t0, ht0⟩ := Finset.card_eq_one.1 hcard
      let c : Fin m → ℝ := fun g => if g = t0 then 1 else 0
      refine ⟨c, fun g => by simp only [c]; split_ifs <;> norm_num, Or.inr ?_⟩
      obtain ⟨rest, hrest⟩ := head_of_max c t0 (by intro y hy; simp [c, hy])
      have hnd := rank_nodup c
      rw [hrest, List.nodup_cons] at hnd
      have hz : ∀ h ∈ rest, c h = 0 := by
        intro h hh; simp only [c]; rw [if_neg]; rintro rfl; exact hnd.1 hh
      rw [cut_eq, hrest, List.foldl_cons]
      have hs : step c (∅, ∅) t0 = ({t0}, ∅) := by simp [step]
      rw [hs, fold_zero' c rest _ hz (by simp [c])]
      have hrestP : rest.toFinset = P := by
        ext x
        have hxr := mem_rank c x
        rw [hrest, List.mem_cons] at hxr
        rw [List.mem_toFinset]
        constructor
        · intro hx
          by_contra hxP
          have : x ∈ T := (hmemT x).2 hxP
          rw [ht0, mem_singleton] at this
          subst this; exact hnd.1 hx
        · intro hxP
          rcases hxr with rfl | h
          · have : x ∈ T := by rw [ht0]; simp
            exact absurd hxP ((hmemT x).1 this)
          · exact h
      rw [hrestP, ← ht0]
      simp
  · let b : ℝ := (T.card : ℝ)
    have hb2 : (2:ℝ) ≤ b := by simp only [b]; exact_mod_cast hb
    let c : Fin m → ℝ := fun g => if g = x1 then b else if g ∈ T then 1 else 0
    refine ⟨c, fun g => by simp only [c]; split_ifs <;> linarith, Or.inl ?_⟩
    have hx1T : x1 ∉ T := by rw [hmemT]; simpa using hx1
    obtain ⟨rest, hrest⟩ := head_of_max c x1 (by
      intro y hy; simp only [c, if_neg hy, if_pos rfl]; split_ifs <;> linarith)
    have hnd := rank_nodup c
    have hpw := rank_pairwise c
    rw [hrest, List.nodup_cons] at hnd
    rw [hrest, List.pairwise_cons] at hpw
    rw [cut_eq, hrest, List.foldl_cons]
    have hs : step c (∅, ∅) x1 = ({x1}, ∅) := by simp [step]
    have hTsub : rest.toFinset ∩ T = T := by
      ext x
      simp only [mem_inter, List.mem_toFinset, and_iff_right_iff_imp]
      intro hxT
      have hxr := mem_rank c x
      rw [hrest, List.mem_cons] at hxr
      rcases hxr with rfl | h
      · exact absurd hxT hx1T
      · exact h
    rw [hs, fold_one c T rest _ hnd.2 hpw.2 ?_ (by simp) ?_]
    · rw [hTsub]
      refine Prod.ext ?_ (by simp)
      ext x
      simp only [mem_union, mem_singleton, mem_sdiff, List.mem_toFinset]
      constructor
      · rintro (rfl | ⟨_, h2⟩)
        · exact hx1
        · by_contra hxP; exact h2 ((hmemT x).2 hxP)
      · intro hxP
        by_cases hx : x = x1
        · exact Or.inl hx
        · right
          have hxr := mem_rank c x
          rw [hrest, List.mem_cons] at hxr
          refine ⟨hxr.resolve_left hx, fun h => (hmemT x).1 h hxP⟩
    · intro h hh
      have hne : h ≠ x1 := fun e => hnd.1 (e ▸ hh)
      simp only [c, if_neg hne]
      constructor
      · intro hT; rw [if_pos hT]
      · intro hT; rw [if_neg hT]
    · rw [hTsub]; simp [c, b]

lemma mcc1 (b : Fin 2 → Fin m → ℝ) : modCutChoose b 1 =
    if ∑ g ∈ (cut (b 0)).2, b 1 g ≤ ∑ g ∈ (cut (b 0)).1, b 1 g then (cut (b 0)).1
    else (cut (b 0)).2 := by
  simp [modCutChoose]

lemma mcc0 (b : Fin 2 → Fin m → ℝ) : modCutChoose b 0 = univ \ modCutChoose b 1 := by
  simp [modCutChoose]

lemma dev0 (b : Fin 2 → Fin m → ℝ) (P : Finset (Fin m)) : ∃ c : Fin m → ℝ, (∀ g, 0 ≤ c g) ∧
    (modCutChoose (Function.update b 0 c) 0 = P ∨
      modCutChoose (Function.update b 0 c) 0 = univ \ P) := by
  obtain ⟨c, hc, hcut⟩ := cut_realize P
  refine ⟨c, hc, ?_⟩
  rw [mcc0, mcc1]
  simp only [Function.update_self, ne_eq, one_ne_zero, not_false_eq_true,
    Function.update_of_ne]
  rcases hcut with h | h <;> rw [h] <;> split_ifs <;> simp

lemma val_erase_le {n : ℕ} (v : Fin n → Fin m → ℝ) (hv : ∀ i g, 0 ≤ v i g) (i : Fin n)
    (S : Finset (Fin m)) (g : Fin m) : val v i (S.erase g) ≤ val v i S :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun x _ _ => hv i x)

theorem theorem_4_3 {m : ℕ} (v : Fin 2 → Fin m → ℝ) (hv : ∀ i g, 0 ≤ v i g) :
    (∃ b, StrategicAlloc.RRFair.IsPNE modCutChoose v b) ∧
      ∀ b, StrategicAlloc.RRFair.IsPNE modCutChoose v b →
        IsApproxMMS 1 v (modCutChoose b) ∧ IsEFX v (modCutChoose b) := by
  classical
  constructor
  · -- existence
    let out : (Fin m → ℝ) → Finset (Fin m) := fun c => modCutChoose ![c, v 1] 0
    let S : Finset (Finset (Fin m)) :=
      univ.filter (fun X => ∃ c : Fin m → ℝ, (∀ g, 0 ≤ c g) ∧ out c = X)
    have hSne : S.Nonempty := ⟨out (fun _ => 0), by
      simp only [S, mem_filter, mem_univ, true_and]; exact ⟨_, fun _ => le_refl _, rfl⟩⟩
    obtain ⟨X, hXS, hXmax⟩ := Finset.exists_max_image S (val v 0) hSne
    simp only [S, mem_filter, mem_univ, true_and] at hXS
    obtain ⟨cs, hcs, hcsX⟩ := hXS
    refine ⟨![cs, v 1], ?_, ?_⟩
    · intro i g
      fin_cases i
      · exact hcs g
      · exact hv 1 g
    · intro i
      fin_cases i
      · intro b' hb'
        have hupd : Function.update ![cs, v 1] 0 b' = ![b', v 1] := by
          funext i; fin_cases i <;> simp
        show val v 0 (modCutChoose (Function.update ![cs, v 1] 0 b') 0) ≤
          val v 0 (modCutChoose ![cs, v 1] 0)
        rw [hupd]
        have := hXmax (out b') (by
          simp only [S, mem_filter, mem_univ, true_and]; exact ⟨b', hb', rfl⟩)
        change val v 0 (out b') ≤ val v 0 (out cs)
        rw [hcsX]; exact this
      · intro b' _
        show val v 1 (modCutChoose (Function.update ![cs, v 1] 1 b') 1) ≤
          val v 1 (modCutChoose ![cs, v 1] 1)
        rw [mcc1, mcc1]
        simp only [Function.update_self, ne_eq, zero_ne_one, not_false_eq_true,
          Function.update_of_ne, Matrix.cons_val_zero, Matrix.cons_val_one]
        unfold val
        by_cases h2 : ∑ g ∈ (cut cs).2, v 1 g ≤ ∑ g ∈ (cut cs).1, v 1 g
        · simp only [h2, ↓reduceIte]
          split_ifs
          · exact le_refl _
          · exact h2
        · simp only [h2, ↓reduceIte]
          split_ifs
          · exact (not_le.1 h2).le
          · exact le_refl _
  · intro b hpne
    have hbr := hpne.2
    set E := cut (b 0) with hE
    have hpart : E.2 = univ \ E.1 := cut_part _
    -- agent 1 envy-free
    have hEF1 : val v 1 (modCutChoose b 0) ≤ val v 1 (modCutChoose b 1) := by
      have h1 := hbr 1 (fun _ => 0) (fun _ => le_refl _)
      rw [mcc1 (Function.update b 1 _)] at h1
      simp only [Function.update_self, ne_eq, zero_ne_one, not_false_eq_true,
        Function.update_of_ne, Finset.sum_const_zero, le_refl, if_true] at h1
      have h2 : E.2.Nonempty → val v 1 E.2 ≤ val v 1 (modCutChoose b 1) := by
        intro hne
        have := hbr 1 (fun g => if g ∈ E.2 then 1 else 0) (fun g => by split_ifs <;> norm_num)
        rw [mcc1 (Function.update b 1 _)] at this
        simp only [Function.update_self, ne_eq, zero_ne_one, not_false_eq_true,
          Function.update_of_ne] at this
        rw [← hE] at this
        rw [if_neg] at this
        · exact this
        · rw [Finset.sum_ite_mem, Finset.sum_ite_mem, Finset.inter_self, not_le]
          have : E.1 ∩ E.2 = ∅ := by rw [hpart]; simp
          rw [this]; simp [hne]
      rw [← hE] at h1
      rw [mcc0]
      have hmem : modCutChoose b 1 = E.1 ∨ modCutChoose b 1 = E.2 := by
        rw [mcc1, ← hE]; split_ifs <;> simp
      rcases hmem with h | h
      · rw [h, ← hpart]
        rcases E.2.eq_empty_or_nonempty with he | he
        · rw [he]; unfold val
          rw [Finset.sum_empty]
          exact Finset.sum_nonneg (fun x _ => hv 1 x)
        · have := h2 he
          rw [h] at this; exact this
      · rw [h, hpart, Finset.sdiff_sdiff_eq_self (subset_univ _)]
        rw [h, hpart] at h1
        exact h1
    -- agent 0 deviation guarantee
    have hdev : ∀ P, val v 0 P ≤ val v 0 (modCutChoose b 0) ∨
        val v 0 (univ \ P) ≤ val v 0 (modCutChoose b 0) := by
      intro P
      obtain ⟨c, hc, h⟩ := dev0 b P
      have := hbr 0 c hc
      rcases h with h | h
      · left; rw [h] at this; exact this
      · right; rw [h] at this; exact this
    have hsplit : ∀ S : Finset (Fin m), val v 1 S + val v 1 (univ \ S) = val v 1 univ := by
      intro S; unfold val; rw [add_comm]; exact Finset.sum_sdiff (subset_univ _)
    constructor
    · intro i
      rw [one_mul]
      unfold mu LittleCharity.MMS.mms
      apply ciSup_le
      intro f
      have hF : univ.filter (fun g => f g = 1) = univ \ univ.filter (fun g => f g = 0) := by
        ext g
        simp only [mem_filter, mem_univ, true_and, mem_sdiff]
        have : ∀ x : Fin 2, x = 1 ↔ ¬ x = 0 := by decide
        exact this (f g)
      have hb0 : (⨅ j : Fin 2, val v i (univ.filter (fun g => f g = j))) ≤
          val v i (univ.filter (fun g => f g = 0)) := ciInf_le (Finite.bddBelow_range _) 0
      have hb1 : (⨅ j : Fin 2, val v i (univ.filter (fun g => f g = j))) ≤
          val v i (univ \ univ.filter (fun g => f g = 0)) := by
        rw [← hF]; exact ciInf_le (Finite.bddBelow_range _) 1
      fin_cases i
      · rcases hdev (univ.filter (fun g => f g = 0)) with h | h
        · exact hb0.trans h
        · exact hb1.trans h
      · show (⨅ j : Fin 2, val v 1 (univ.filter (fun g => f g = j))) ≤ val v 1 (modCutChoose b 1)
        have h3 := hsplit (univ.filter (fun g => f g = 0))
        have h4 := hsplit (modCutChoose b 1)
        rw [← mcc0] at h4
        simp only [Fin.mk_one, Fin.isValue] at hb0 hb1
        linarith
    · intro i j _ g hg hpos
      fin_cases i <;> fin_cases j
      · exact val_erase_le v hv _ _ _
      · -- i = 0, j = 1
        simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one]
        have hg0 : g ∉ modCutChoose b 0 := by
          rw [mcc0]; simp only [mem_sdiff, not_and, not_not]; exact fun _ => hg
        rcases hdev (insert g (modCutChoose b 0)) with h | h
        · exfalso
          unfold val at h
          rw [Finset.sum_insert hg0] at h
          simp only [Fin.zero_eta, Fin.isValue] at hpos
          linarith
        · have he : univ \ insert g (modCutChoose b 0) = (modCutChoose b 1).erase g := by
            rw [mcc0]
            ext x
            simp only [mem_sdiff, mem_univ, mem_insert, true_and, not_or, not_and, not_not,
              mem_erase]
            try tauto
          rw [he] at h; exact h
      · -- i = 1, j = 0
        exact (val_erase_le v hv _ _ _).trans hEF1
      · exact val_erase_le v hv _ _ _

end StrategicAlloc.CutChoose


-- Platform entry point: restates the target verbatim.
namespace StrategicAlloc.CutChoose

/-- Theorem 4.3 (p. 18): for every two-agent instance with additive non-negative valuations,
Mod-Cut&Choose has a pure Nash equilibrium, and every pure Nash equilibrium yields an allocation
that is MMS and EFX with respect to the true valuations `v_1, v_2`. -/
theorem _root_.solution {m : ℕ} (v : Fin 2 → Fin m → ℝ) (hv : ∀ i g, 0 ≤ v i g) :
    (∃ b, StrategicAlloc.RRFair.IsPNE modCutChoose v b) ∧
      ∀ b, StrategicAlloc.RRFair.IsPNE modCutChoose v b →
        IsApproxMMS 1 v (modCutChoose b) ∧ IsEFX v (modCutChoose b) := by
  apply @StrategicAlloc.CutChoose.theorem_4_3 <;> assumption

end StrategicAlloc.CutChoose
