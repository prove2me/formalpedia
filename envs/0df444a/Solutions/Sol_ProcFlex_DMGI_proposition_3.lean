-- Prove2me | solution 1 for ProcFlex.DMGI.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T21:29:11.420293+00:00
-- url     : https://prove2.me/submissions/fe9cf68f-faae-427b-a8a6-c7b11ebfd23b

import Mathlib
import Definitions.Def_ProcFlex_DMGI_Model
import Theorems.Thm_ProcFlex_DMGI_duality_3

open Finset ProcFlex.DMGI

namespace PF3

variable {m n T : ℕ}

lemma Pbar_succ (S : System m n T) (t : Fin T) : Pbar S t.succ = S.P t := rfl
lemma Pbar_zero (S : System m n T) : Pbar S 0 = 0 := rfl

lemma Pbar_strictMono (S : System m n T) (hS : S.IsValid) : StrictMono (Pbar S) := by
  obtain ⟨_, _, _, _, hmono, hpos, _⟩ := hS
  intro a b hab
  induction a using Fin.cases with
  | zero =>
    induction b using Fin.cases with
    | zero => exact absurd hab (lt_irrefl _)
    | succ b => rw [Pbar_zero, Pbar_succ]; exact hpos b
  | succ a =>
    induction b using Fin.cases with
    | zero => exact absurd hab (by simp)
    | succ b => rw [Pbar_succ, Pbar_succ]; exact hmono (Fin.succ_lt_succ_iff.mp hab)

lemma Pbar_nonneg (S : System m n T) (hS : S.IsValid) (r : Fin (T + 1)) : 0 ≤ Pbar S r := by
  rw [← Pbar_zero S]; exact (Pbar_strictMono S hS).monotone (Fin.zero_le r)

lemma beta_nonneg (S : System m n T) (hS : S.IsValid) (t : Fin T) (r : Fin (T + 1))
    (hr : r.val ≤ t.val + 1) : 0 ≤ beta S t r := by
  unfold beta
  have : Pbar S r ≤ Pbar S t.succ :=
    (Pbar_strictMono S hS).monotone (by rw [Fin.le_iff_val_le_val]; simpa using hr)
  rw [Pbar_succ] at this; linarith

lemma beta_le (S : System m n T) (hS : S.IsValid) (t : Fin T) (r : Fin (T + 1)) :
    beta S t r ≤ S.P t := by
  unfold beta; linarith [Pbar_nonneg S hS r]

lemma weak (S : System m n T) (hS : S.IsValid) (A : Design m n) (d : Fin n → ℝ)
    (hd : ∀ i, 0 ≤ d i) (y : Fin n → ℝ) (z : Fin m → ℝ) (hy : ∀ i, 0 ≤ y i)
    (hz : ∀ j, 0 ≤ z j) (hf : ∀ a ∈ A, S.p a.2 ≤ y a.2 + z a.1) :
    g S A d ≤ ∑ i, d i * y i + ∑ j, S.C j * z j := by
  obtain ⟨_, _, _, hC, _, _, _⟩ := hS
  unfold g ProfitLPData.value
  apply csSup_le
  · refine ⟨_, ⟨0, ?_, rfl⟩⟩
    refine ⟨fun _ _ => le_refl _, fun i => ?_, fun j => ?_⟩
    · simpa using hd i
    · simp only [Pi.zero_apply, sum_const_zero]; exact hC j
  · rintro _ ⟨x, ⟨hx0, hxd, hxC⟩, rfl⟩
    unfold ProfitLPData.profit
    calc ∑ a ∈ A, S.lpData.p a.2 * x a.1 a.2
        ≤ ∑ a ∈ A, (y a.2 + z a.1) * x a.1 a.2 :=
          sum_le_sum (fun a ha => mul_le_mul_of_nonneg_right (hf a ha) (hx0 _ _))
      _ ≤ ∑ a : Fin m × Fin n, (y a.2 + z a.1) * x a.1 a.2 :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _)
            (fun a _ _ => mul_nonneg (add_nonneg (hy _) (hz _)) (hx0 _ _))
      _ = ∑ i, y i * ∑ j, x j i + ∑ j, z j * ∑ i, x j i := by
          rw [Fintype.sum_prod_type]
          simp only [add_mul, sum_add_distrib, mul_sum]
          rw [sum_comm]
      _ ≤ ∑ i, d i * y i + ∑ j, S.C j * z j := by
          apply add_le_add
          · apply sum_le_sum; intro i _
            rw [mul_comm (d i)]
            exact mul_le_mul_of_nonneg_left (hxd i) (hy i)
          · apply sum_le_sum; intro j _
            rw [mul_comm (S.C j)]
            exact mul_le_mul_of_nonneg_left (hxC j) (hz j)

lemma g_nonneg (S : System m n T) (hS : S.IsValid) (A : Design m n) (d : Fin n → ℝ) :
    0 ≤ g S A d := by
  obtain ⟨_, _, _, _, _, hpos, _⟩ := hS
  unfold g ProfitLPData.value
  apply Real.sSup_nonneg
  rintro _ ⟨x, ⟨hx0, _, _⟩, rfl⟩
  unfold ProfitLPData.profit
  exact sum_nonneg (fun a _ => mul_nonneg (le_of_lt (hpos _)) (hx0 _ _))

end PF3

namespace PF3

variable {m n T : ℕ}

/-- grid of extended margins -/
noncomputable def G (S : System m n T) : Finset ℝ := univ.image (Pbar S)

lemma p_eq (S : System m n T) (i : Fin n) : S.p i = Pbar S (S.cat i).succ := rfl

lemma p_mem_G (S : System m n T) (i : Fin n) : S.p i ∈ G S := by
  rw [p_eq]; exact mem_image_of_mem _ (mem_univ _)

lemma zero_mem_G (S : System m n T) : (0 : ℝ) ∈ G S := by
  rw [← Pbar_zero S]; exact mem_image_of_mem _ (mem_univ _)

lemma G_nonneg (S : System m n T) (hS : S.IsValid) : ∀ x ∈ G S, 0 ≤ x := by
  intro x hx; simp only [G, mem_image] at hx
  obtain ⟨r, _, rfl⟩ := hx; exact Pbar_nonneg S hS r

noncomputable def Pmax (S : System m n T) : ℝ := (G S).max' ⟨0, zero_mem_G S⟩

lemma le_Pmax (S : System m n T) {x : ℝ} (hx : x ∈ G S) : x ≤ Pmax S := le_max' _ _ hx

lemma Pmax_mem (S : System m n T) : Pmax S ∈ G S := max'_mem _ _

def Nb (A : Design m n) (i : Fin n) : Finset (Fin m × Fin n) := A.filter (fun a => a.2 = i)

noncomputable def mm (S : System m n T) (A : Design m n) (z : Fin m → ℝ) (i : Fin n) : ℝ :=
  (insert (S.p i) ((Nb A i).image (fun a => z a.1))).min' (insert_nonempty _ _)

lemma mm_le_p (S : System m n T) (A : Design m n) (z : Fin m → ℝ) (i : Fin n) :
    mm S A z i ≤ S.p i := min'_le _ _ (mem_insert_self _ _)

lemma mm_le_z (S : System m n T) (A : Design m n) (z : Fin m → ℝ) (a : Fin m × Fin n)
    (ha : a ∈ A) : mm S A z a.2 ≤ z a.1 := by
  apply min'_le
  apply mem_insert_of_mem
  exact mem_image.mpr ⟨a, by simp [Nb, ha], rfl⟩

lemma mm_mem (S : System m n T) (A : Design m n) (z : Fin m → ℝ) (i : Fin n) :
    mm S A z i = S.p i ∨ ∃ a ∈ Nb A i, mm S A z i = z a.1 := by
  have := min'_mem (insert (S.p i) ((Nb A i).image (fun a => z a.1))) (insert_nonempty _ _)
  rw [mem_insert, mem_image] at this
  rcases this with h | ⟨a, ha, h⟩
  · left; exact h
  · right; exact ⟨a, ha, h.symm⟩

lemma mm_le (S : System m n T) (A : Design m n) (z : Fin m → ℝ) (i : Fin n) (x : ℝ)
    (hx : x = S.p i ∨ ∃ a ∈ Nb A i, x = z a.1) : mm S A z i ≤ x := by
  apply min'_le
  rcases hx with rfl | ⟨a, ha, rfl⟩
  · exact mem_insert_self _ _
  · exact mem_insert_of_mem (mem_image.mpr ⟨a, ha, rfl⟩)

lemma le_mm (S : System m n T) (A : Design m n) (z : Fin m → ℝ) (i : Fin n) (b : ℝ)
    (h1 : b ≤ S.p i) (h2 : ∀ a ∈ Nb A i, b ≤ z a.1) : b ≤ mm S A z i := by
  apply le_min'
  intro x hx
  rw [mem_insert, mem_image] at hx
  rcases hx with rfl | ⟨a, ha, rfl⟩
  · exact h1
  · exact h2 a ha

noncomputable def Phi (S : System m n T) (A : Design m n) (d : Fin n → ℝ) (z : Fin m → ℝ) : ℝ :=
  ∑ i, d i * (S.p i - mm S A z i) + ∑ j, S.C j * z j

lemma R1 (S : System m n T) (A : Design m n) (d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i)
    (y : Fin n → ℝ) (z : Fin m → ℝ) (hy : ∀ i, 0 ≤ y i)
    (hf : ∀ a ∈ A, S.p a.2 ≤ y a.2 + z a.1) :
    Phi S A d z ≤ ∑ i, d i * y i + ∑ j, S.C j * z j := by
  unfold Phi
  apply add_le_add_left
  apply sum_le_sum; intro i _
  apply mul_le_mul_of_nonneg_left _ (hd i)
  rcases mm_mem S A z i with h | ⟨a, ha, h⟩
  · rw [h]; linarith [hy i]
  · rw [h]
    have ha' : a ∈ A ∧ a.2 = i := by simpa [Nb] using ha
    have := hf a ha'.1
    rw [ha'.2] at this; linarith

/-- R2: on-grid duals give structured duals -/
lemma R2 (S : System m n T) (hS : S.IsValid) (A : Design m n) (d : Fin n → ℝ)
    (z : Fin m → ℝ) (hzG : ∀ j, z j ∈ G S) :
    ∃ lv : Fin n → Fin (T + 1), (∀ i, (lv i).val ≤ (S.cat i).val + 1) ∧
      (∀ a ∈ A, Pbar S (lv a.2) ≤ z a.1) ∧
      ∑ i, d i * beta S (S.cat i) (lv i) + ∑ j, S.C j * z j = Phi S A d z := by
  have hmG : ∀ i, mm S A z i ∈ G S := by
    intro i
    rcases mm_mem S A z i with h | ⟨a, _, h⟩
    · rw [h]; exact p_mem_G S i
    · rw [h]; exact hzG _
  have hex : ∀ i, ∃ r, Pbar S r = mm S A z i := by
    intro i; have := hmG i; simp only [G, mem_image] at this
    obtain ⟨r, _, hr⟩ := this; exact ⟨r, hr⟩
  choose lv hlv using hex
  refine ⟨lv, ?_, ?_, ?_⟩
  · intro i
    have h1 : Pbar S (lv i) ≤ Pbar S (S.cat i).succ := by
      rw [hlv i, ← p_eq]; exact mm_le_p S A z i
    have := (Pbar_strictMono S hS).le_iff_le.mp h1
    rw [Fin.le_iff_val_le_val] at this; simpa using this
  · intro a ha; rw [hlv]; exact mm_le_z S A z a ha
  · unfold Phi; congr 1
    apply sum_congr rfl; intro i _
    unfold beta; rw [hlv i]; rfl

noncomputable def offc (S : System m n T) (z : Fin m → ℝ) : ℕ :=
  ((univ.image z).filter (fun x => x ∉ G S)).card

lemma R3 (S : System m n T) (hS : S.IsValid) (A : Design m n) (d : Fin n → ℝ)
    (z : Fin m → ℝ) (hz0 : ∀ j, 0 ≤ z j) (hzP : ∀ j, z j ≤ Pmax S)
    (j0 : Fin m) (hj0 : z j0 ∉ G S) :
    ∃ z' : Fin m → ℝ, (∀ j, 0 ≤ z' j) ∧ (∀ j, z' j ≤ Pmax S) ∧
      Phi S A d z' ≤ Phi S A d z ∧ offc S z' < offc S z := by
  classical
  set v := z j0 with hv
  set W := G S ∪ univ.image z with hW
  have hvpos : 0 < v := by
    rcases (hz0 j0).lt_or_eq with h | h
    · exact h
    · exfalso; apply hj0; rw [hv, ← h]; exact zero_mem_G S
  have hvP : v < Pmax S := by
    rcases (hzP j0).lt_or_eq with h | h
    · exact h
    · exfalso; apply hj0; rw [hv, h]; exact Pmax_mem S
  have hLo : (W.filter (· < v)).Nonempty := ⟨0, by simp [hW, zero_mem_G S, hvpos]⟩
  have hHi : (W.filter (v < ·)).Nonempty := ⟨Pmax S, by simp [hW, Pmax_mem S, hvP]⟩
  set lo := (W.filter (· < v)).max' hLo with hlo
  set hi := (W.filter (v < ·)).min' hHi with hhi
  have hlo_mem : lo ∈ W.filter (· < v) := max'_mem _ _
  have hhi_mem : hi ∈ W.filter (v < ·) := min'_mem _ _
  have hlov : lo < v := (mem_filter.mp hlo_mem).2
  have hvhi : v < hi := (mem_filter.mp hhi_mem).2
  have hbelow : ∀ x ∈ W, x < v → x ≤ lo := fun x hx hxv => le_max' _ _ (mem_filter.mpr ⟨hx, hxv⟩)
  have habove : ∀ x ∈ W, v < x → hi ≤ x := fun x hx hxv => min'_le _ _ (mem_filter.mpr ⟨hx, hxv⟩)
  have hzW : ∀ j, z j ∈ W := fun j => mem_union_right _ (mem_image_of_mem _ (mem_univ _))
  have hpW : ∀ i, S.p i ∈ W := fun i => mem_union_left _ (p_mem_G S i)
  have hpv : ∀ i, S.p i ≠ v := fun i h => hj0 (h ▸ p_mem_G S i)
  have hlo0 : 0 ≤ lo := le_max' _ _ (by simp [hW, zero_mem_G S, hvpos])
  have hhiP : hi ≤ Pmax S := min'_le _ _ (by simp [hW, Pmax_mem S, hvP])
  let zw : ℝ → Fin m → ℝ := fun w j => if z j = v then w else z j
  -- key: mm of zw
  have key : ∀ w, lo ≤ w → w ≤ hi → ∀ i,
      mm S A (zw w) i = if mm S A z i = v then w else mm S A z i := by
    intro w hw1 hw2 i
    have hmin_le : ∀ a ∈ Nb A i, mm S A z i ≤ z a.1 :=
      fun a ha => mm_le S A z i _ (Or.inr ⟨a, ha, rfl⟩)
    have hmp := mm_le_p S A z i
    have hmW : mm S A z i ∈ W := by
      rcases mm_mem S A z i with h | ⟨a, _, h⟩
      · rw [h]; exact hpW i
      · rw [h]; exact hzW _
    split_ifs with hcase
    · apply le_antisymm
      · rcases mm_mem S A z i with h | ⟨a, ha, h⟩
        · exact absurd (h.symm.trans hcase) (hpv i)
        · apply mm_le S A (zw w) i w (Or.inr ⟨a, ha, ?_⟩)
          simp only [zw]; rw [if_pos (h.symm.trans hcase)]
      · apply le_mm
        · have hvp : v ≤ S.p i := by rw [← hcase]; exact hmp
          have := habove _ (hpW i) (lt_of_le_of_ne hvp (hpv i).symm); linarith
        · intro a ha; simp only [zw]; split_ifs with hza
          · exact le_refl _
          · have hvz : v ≤ z a.1 := by rw [← hcase]; exact hmin_le a ha
            have := habove _ (hzW _) (lt_of_le_of_ne hvz (Ne.symm hza)); linarith
    · apply le_antisymm
      · rcases mm_mem S A z i with h | ⟨a, ha, h⟩
        · rw [h]; exact mm_le_p S A (zw w) i
        · have hza : z a.1 ≠ v := by rw [← h]; exact hcase
          rw [h]; apply mm_le S A (zw w) i _ (Or.inr ⟨a, ha, ?_⟩)
          simp only [zw]; rw [if_neg hza]
      · apply le_mm
        · exact hmp
        · intro a ha; simp only [zw]; split_ifs with hza
          · have h1 := hmin_le a ha; rw [hza] at h1
            have := hbelow _ hmW (lt_of_le_of_ne h1 hcase); linarith
          · exact hmin_le a ha
  -- Phi formula
  set S0 := ∑ j, (if z j = v then S.C j else 0) - ∑ i, (if mm S A z i = v then d i else 0)
    with hS0
  have hPhi : ∀ w, lo ≤ w → w ≤ hi → Phi S A d (zw w) = Phi S A d z + (w - v) * S0 := by
    intro w hw1 hw2
    unfold Phi
    simp only [key w hw1 hw2]
    rw [hS0, mul_sub, mul_sum, mul_sum]
    have e1 : ∑ i, d i * (S.p i - if mm S A z i = v then w else mm S A z i) =
        ∑ i, d i * (S.p i - mm S A z i) - ∑ i, (w - v) * (if mm S A z i = v then d i else 0) := by
      rw [← sum_sub_distrib]; apply sum_congr rfl; intro i _
      split_ifs with h
      · rw [h]; ring
      · ring
    have e2 : ∑ j, S.C j * zw w j = ∑ j, S.C j * z j + ∑ j, (w - v) * (if z j = v then S.C j else 0) := by
      rw [← sum_add_distrib]; apply sum_congr rfl; intro j _
      simp only [zw]
      split_ifs with h
      · rw [h]; ring
      · ring
    rw [e1, e2]; ring
  set w := if 0 ≤ S0 then lo else hi with hwdef
  have hw1 : lo ≤ w := by rw [hwdef]; split_ifs <;> linarith
  have hw2 : w ≤ hi := by rw [hwdef]; split_ifs <;> linarith
  have hwW : w ∈ W := by
    rw [hwdef]; split_ifs
    · exact (mem_filter.mp hlo_mem).1
    · exact (mem_filter.mp hhi_mem).1
  have hwv : w ≠ v := by
    rw [hwdef]; split_ifs
    · exact ne_of_lt hlov
    · exact ne_of_gt hvhi
  refine ⟨zw w, ?_, ?_, ?_, ?_⟩
  · intro j; simp only [zw]; split_ifs
    · linarith
    · exact hz0 j
  · intro j; simp only [zw]; split_ifs
    · linarith
    · exact hzP j
  · rw [hPhi w hw1 hw2]
    have : (w - v) * S0 ≤ 0 := by
      rw [hwdef]; split_ifs with h
      · exact mul_nonpos_of_nonpos_of_nonneg (by linarith) h
      · exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    linarith
  · unfold offc
    have hsub : (univ.image (zw w)).filter (fun x => x ∉ G S) ⊆
        ((univ.image z).filter (fun x => x ∉ G S)).erase v := by
      intro x hx
      rw [mem_filter, mem_image] at hx
      obtain ⟨⟨j, _, rfl⟩, hxG⟩ := hx
      rw [mem_erase, mem_filter]
      simp only [zw] at hxG ⊢
      split_ifs with hzj
      · simp only [hzj, if_true] at hxG
        refine ⟨hwv, ?_, hxG⟩
        rcases mem_union.mp hwW with h | h
        · exact absurd h hxG
        · exact h
      · simp only [hzj, if_false] at hxG
        exact ⟨hzj, mem_image_of_mem _ (mem_univ _), hxG⟩
    calc ((univ.image (zw w)).filter (fun x => x ∉ G S)).card
        ≤ (((univ.image z).filter (fun x => x ∉ G S)).erase v).card := card_le_card hsub
      _ < ((univ.image z).filter (fun x => x ∉ G S)).card := by
        apply card_erase_lt_of_mem
        exact mem_filter.mpr ⟨mem_image_of_mem _ (mem_univ _), hj0⟩

end PF3

namespace PF3

variable {m n T : ℕ}

lemma R4 (S : System m n T) (hS : S.IsValid) (A : Design m n) (d : Fin n → ℝ) :
    ∀ N, ∀ z : Fin m → ℝ, offc S z = N → (∀ j, 0 ≤ z j) → (∀ j, z j ≤ Pmax S) →
    ∃ z', (∀ j, z' j ∈ G S) ∧ (∀ j, 0 ≤ z' j) ∧ Phi S A d z' ≤ Phi S A d z := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro z hN hz0 hzP
    by_cases hall : ∀ j, z j ∈ G S
    · exact ⟨z, hall, hz0, le_refl _⟩
    · push Not at hall
      obtain ⟨j0, hj0⟩ := hall
      obtain ⟨z', h0, hP, hPhi, hoff⟩ := R3 S hS A d z hz0 hzP j0 hj0
      obtain ⟨z'', hG, h0', hPhi'⟩ := ih (offc S z') (hN ▸ hoff) z' rfl h0 hP
      exact ⟨z'', hG, h0', le_trans hPhi' hPhi⟩

lemma structured (S : System m n T) (hS : S.IsValid) (A : Design m n) (d : Fin n → ℝ)
    (hd : ∀ i, 0 ≤ d i) :
    ∃ lv : Fin n → Fin (T + 1), (∀ i, (lv i).val ≤ (S.cat i).val + 1) ∧
      ∃ z : Fin m → ℝ, (∀ j, 0 ≤ z j) ∧ (∀ a ∈ A, Pbar S (lv a.2) ≤ z a.1) ∧
      ∑ i, d i * beta S (S.cat i) (lv i) + ∑ j, S.C j * z j ≤ g S A d := by
  obtain ⟨y, z, ⟨hf, hy, hz⟩, hval⟩ := (duality_3 S hS A d hd).1
  have hC := hS.2.2.2.1
  set z1 : Fin m → ℝ := fun j => min (z j) (Pmax S) with hz1
  have hf1 : ∀ a ∈ A, S.p a.2 ≤ y a.2 + z1 a.1 := by
    intro a ha; simp only [z1]
    rcases le_total (z a.1) (Pmax S) with h | h
    · rw [min_eq_left h]; exact hf a ha
    · rw [min_eq_right h]; linarith [hy a.2, le_Pmax S (p_mem_G S a.2)]
  have h1 : Phi S A d z1 ≤ g S A d := by
    calc Phi S A d z1 ≤ ∑ i, d i * y i + ∑ j, S.C j * z1 j := R1 S A d hd y z1 hy hf1
      _ ≤ ∑ i, d i * y i + ∑ j, S.C j * z j := by
        apply add_le_add (le_refl _); apply sum_le_sum; intro j _
        exact mul_le_mul_of_nonneg_left (min_le_left _ _) (hC j)
      _ = g S A d := by rw [hval]; rfl
  obtain ⟨z2, hG, h0, hPhi⟩ := R4 S hS A d _ z1 rfl
    (fun j => le_min (hz j) (G_nonneg S hS _ (Pmax_mem S))) (fun j => min_le_right _ _)
  obtain ⟨lv, hlv, harc, heq⟩ := R2 S hS A d z2 hG
  exact ⟨lv, hlv, z2, h0, harc, by rw [heq]; linarith⟩

end PF3

namespace PF3

variable {m n T : ℕ}

def inBlock (K : Fin T → Fin (T + 1) → ℕ) (t : Fin T) (r : Fin (T + 1)) (q : ℕ) : Prop :=
  r.val ≤ t.val ∧ H K t r - K t r ≤ q ∧ q < H K t r

lemma K_le_H (K : Fin T → Fin (T + 1) → ℕ) (t : Fin T) (r : Fin (T + 1)) : K t r ≤ H K t r := by
  unfold H
  exact single_le_sum (f := fun j => K t j) (fun _ _ => Nat.zero_le _) (by simp)

lemma H_mono (K : Fin T → Fin (T + 1) → ℕ) (t : Fin T) {r r' : Fin (T + 1)} (h : r ≤ r') :
    H K t r ≤ H K t r' := by
  unfold H
  apply sum_le_sum_of_subset
  intro j hj; simp only [mem_filter, mem_univ, true_and] at hj ⊢
  rw [Fin.le_iff_val_le_val] at h; omega

lemma H_add_le (K : Fin T → Fin (T + 1) → ℕ) (t : Fin T) {r r' : Fin (T + 1)} (h : r < r') :
    H K t r + K t r' ≤ H K t r' := by
  unfold H
  have hnot : r' ∉ univ.filter (fun j : Fin (T + 1) => j.val ≤ r.val) := by
    simp only [mem_filter, mem_univ, true_and, not_le]; exact h
  have hsub : insert r' (univ.filter (fun j : Fin (T + 1) => j.val ≤ r.val)) ⊆
      univ.filter (fun j : Fin (T + 1) => j.val ≤ r'.val) := by
    intro j hj
    simp only [mem_insert, mem_filter, mem_univ, true_and] at hj ⊢
    rcases hj with rfl | hj
    · exact le_refl _
    · have : r.val < r'.val := h; omega
  calc _ = ∑ j ∈ insert r' (univ.filter (fun j : Fin (T + 1) => j.val ≤ r.val)), K t j := by
        rw [sum_insert hnot]; ring
    _ ≤ _ := sum_le_sum_of_subset hsub

lemma inBlock_unique (K : Fin T → Fin (T + 1) → ℕ) (t : Fin T) {r r' : Fin (T + 1)} {q : ℕ}
    (h1 : inBlock K t r q) (h2 : inBlock K t r' q) : r = r' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := H_add_le K t h; unfold inBlock at h1 h2; omega
  · have := H_add_le K t h; unfold inBlock at h1 h2; omega

open Classical in
noncomputable def bcq (K : Fin T → Fin (T + 1) → ℕ) (t : Fin T) (q : ℕ) : Fin (T + 1) :=
  if h : ∃ r, inBlock K t r q then h.choose else t.succ

lemma bcq_spec (K : Fin T → Fin (T + 1) → ℕ) (t : Fin T) {r : Fin (T + 1)} {q : ℕ}
    (hr : inBlock K t r q) : bcq K t q = r := by
  have hex : ∃ r, inBlock K t r q := ⟨r, hr⟩
  unfold bcq; rw [dif_pos hex]; exact inBlock_unique K t hex.choose_spec hr

lemma bcq_none (K : Fin T → Fin (T + 1) → ℕ) (t : Fin T) {q : ℕ}
    (h : ¬ ∃ r, inBlock K t r q) : bcq K t q = t.succ := by
  unfold bcq; rw [dif_neg h]

lemma bcq_le (K : Fin T → Fin (T + 1) → ℕ) (t : Fin T) (q : ℕ) :
    (bcq K t q).val ≤ t.val + 1 := by
  by_cases h : ∃ r, inBlock K t r q
  · obtain ⟨r, hr⟩ := h; rw [bcq_spec K t hr]; have := hr.1; omega
  · rw [bcq_none K t h]; simp

lemma bcq_eq_iff (K : Fin T → Fin (T + 1) → ℕ) (t : Fin T) {r : Fin (T + 1)} (q : ℕ)
    (hr : r.val ≤ t.val) : bcq K t q = r ↔ inBlock K t r q := by
  constructor
  · intro h
    by_cases hh : ∃ r, inBlock K t r q
    · obtain ⟨r', hr'⟩ := hh; rw [bcq_spec K t hr'] at h; rw [← h]; exact hr'
    · rw [bcq_none K t hh] at h; rw [← h] at hr; simp at hr
  · exact bcq_spec K t

lemma block_beta_sum (S : System m n T) (K : Fin T → Fin (T + 1) → ℕ) (t : Fin T) (q : ℕ) :
    ∑ r ∈ univ.filter (fun r : Fin (T + 1) => r.val ≤ t.val),
      beta S t r * (if H K t r - K t r ≤ q ∧ q < H K t r then (1 : ℝ) else 0) =
      beta S t (bcq K t q) := by
  by_cases h : ∃ r, inBlock K t r q
  · obtain ⟨r, hr⟩ := h
    rw [bcq_spec K t hr, sum_eq_single r]
    · rw [if_pos hr.2]; ring
    · intro b hb hbr
      have : ¬ (H K t b - K t b ≤ q ∧ q < H K t b) := fun hb' =>
        hbr (inBlock_unique K t ⟨(mem_filter.mp hb).2, hb'⟩ hr)
      rw [if_neg this]; ring
    · intro hr'
      exact absurd (by simp only [mem_filter, mem_univ, true_and]; exact hr.1) hr'
  · rw [bcq_none K t h]
    have : beta S t t.succ = 0 := by unfold beta; rw [Pbar_succ]; ring
    rw [this]; apply sum_eq_zero; intro r hr
    have : ¬ (H K t r - K t r ≤ q ∧ q < H K t r) := fun h' => h ⟨r, (mem_filter.mp hr).2, h'⟩
    rw [if_neg this]; ring

def idx (S : System m n T) (i : Fin n) : ℕ := ((S.s (S.cat i)).filter (fun j => j < i)).card

noncomputable def lvB (S : System m n T) (K : Fin T → Fin (T + 1) → ℕ) (i : Fin n) :
    Fin (T + 1) := bcq K (S.cat i) (idx S i)

abbrev em (S : System m n T) (t : Fin T) : Fin (S.s t).card ↪o Fin n :=
  (S.s t).orderEmbOfFin rfl

lemma em_mem (S : System m n T) (t : Fin T) (q : Fin (S.s t).card) : em S t q ∈ S.s t :=
  orderEmbOfFin_mem _ _ _

lemma cat_em (S : System m n T) (t : Fin T) (q : Fin (S.s t).card) : S.cat (em S t q) = t := by
  have := em_mem S t q; simpa [System.s] using this

lemma em_surj (S : System m n T) (t : Fin T) {j : Fin n} (hj : j ∈ S.s t) :
    ∃ q, em S t q = j := by
  have : j ∈ Set.range (em S t) := by rw [range_orderEmbOfFin]; exact hj
  exact this

lemma idx_em (S : System m n T) (t : Fin T) (q : Fin (S.s t).card) :
    idx S (em S t q) = q.val := by
  unfold idx; rw [cat_em]
  have : (S.s t).filter (fun j => j < em S t q) =
      (univ.filter (fun q' => q' < q)).map (em S t).toEmbedding := by
    ext j
    simp only [mem_filter, mem_map, mem_univ, true_and]
    constructor
    · rintro ⟨hj, hlt⟩
      obtain ⟨q', rfl⟩ := em_surj S t hj
      exact ⟨q', (em S t).lt_iff_lt.mp hlt, rfl⟩
    · rintro ⟨q', hq', rfl⟩
      exact ⟨em_mem S t q', (em S t).lt_iff_lt.mpr hq'⟩
  rw [this, card_map]
  have : univ.filter (fun q' : Fin (S.s t).card => q' < q) = Iio q := by ext; simp
  rw [this, Fin.card_Iio]

lemma lvB_em (S : System m n T) (K : Fin T → Fin (T + 1) → ℕ) (t : Fin T)
    (q : Fin (S.s t).card) : lvB S K (em S t q) = bcq K t q.val := by
  unfold lvB; rw [idx_em, cat_em]

lemma sum_s_eq (S : System m n T) (t : Fin T) (F : Fin n → ℝ) :
    ∑ i ∈ S.s t, F i = ∑ q : Fin (S.s t).card, F (em S t q) := by
  conv_lhs => rw [← image_orderEmbOfFin_univ (S.s t) rfl]
  rw [sum_image]
  intro a _ b _ h; exact (em S t).injective h

lemma blockSum_eq (S : System m n T) (K : Fin T → Fin (T + 1) → ℕ) (ε : Fin n → ℝ) :
    blockSum S K ε = ∑ i, ε i * beta S (S.cat i) (lvB S K i) := by
  rw [← sum_fiberwise univ S.cat (fun i => ε i * beta S (S.cat i) (lvB S K i))]
  unfold blockSum
  apply sum_congr rfl; intro t _
  have hs : univ.filter (fun i => S.cat i = t) = S.s t := rfl
  rw [hs, sum_s_eq]
  simp only [cat_em, lvB_em]
  simp only [← block_beta_sum S K t, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl; intro r _
  rw [sum_filter]
  apply sum_congr rfl; intro q _
  split_ifs <;> ring

end PF3

namespace PF3

variable {m n T : ℕ}

lemma count_em (S : System m n T) (t : Fin T) (P : Fin n → Prop) [DecidablePred P] :
    (univ.filter (fun i => S.cat i = t ∧ P i)).card =
      (univ.filter (fun q : Fin (S.s t).card => P (em S t q))).card := by
  have : univ.filter (fun i => S.cat i = t ∧ P i) =
      (univ.filter (fun q => P (em S t q))).map (em S t).toEmbedding := by
    ext i; simp only [mem_filter, mem_univ, true_and, mem_map]
    constructor
    · rintro ⟨hc, hp⟩
      have hi : i ∈ S.s t := by simp [System.s, hc]
      obtain ⟨q, hq⟩ := em_surj S t hi
      subst hq
      exact ⟨q, hp, rfl⟩
    · rintro ⟨q, hq, rfl⟩; exact ⟨cat_em S t q, hq⟩
  rw [this, card_map]

lemma lvB_level (S : System m n T) (K : Fin T → Fin (T + 1) → ℕ) (hK : InQ S K) :
    IsLevelAssignment S K (lvB S K) := by
  refine ⟨fun i => bcq_le K _ _, ?_⟩
  intro t r hrt
  rw [count_em S t (fun i => lvB S K i = r)]
  simp only [lvB_em]
  have hHc : H K t r ≤ (S.s t).card := by
    have h1 : H K t r ≤ H K t t.castSucc :=
      H_mono K t (by rw [Fin.le_iff_val_le_val]; simpa using hrt)
    have h2 : H K t t.castSucc =
        ∑ r ∈ univ.filter (fun r : Fin (T + 1) => r.val ≤ t.val), K t r := by
      simp only [H, Fin.val_castSucc]
    have := hK t
    omega
  have hKH := K_le_H K t r
  have e1 : univ.filter (fun q : Fin (S.s t).card => bcq K t q.val = r) =
      univ.filter (fun q : Fin (S.s t).card =>
        H K t r - K t r ≤ q.val ∧ q.val < H K t r) := by
    ext q; simp only [mem_filter, mem_univ, true_and]
    rw [bcq_eq_iff K t _ hrt]; unfold inBlock; simp [hrt]
  rw [e1]
  have e2 : (univ.filter (fun q : Fin (S.s t).card =>
      H K t r - K t r ≤ q.val ∧ q.val < H K t r)).map Fin.valEmbedding =
      Ico (H K t r - K t r) (H K t r) := by
    ext x; simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_Ico]
    constructor
    · rintro ⟨q, hq, rfl⟩; exact hq
    · intro hx; exact ⟨⟨x, by omega⟩, hx, rfl⟩
  rw [← card_map Fin.valEmbedding, e2, Nat.card_Ico]; omega

lemma fiber_eq (S : System m n T) (K : Fin T → Fin (T + 1) → ℕ) (f₁ f₂ : Fin n → Fin (T + 1))
    (h₁ : IsLevelAssignment S K f₁) (h₂ : IsLevelAssignment S K f₂)
    (t : Fin T) (r : Fin (T + 1)) :
    (univ.filter (fun i => S.cat i = t ∧ f₁ i = r)).card =
      (univ.filter (fun i => S.cat i = t ∧ f₂ i = r)).card := by
  by_cases hr : r.val ≤ t.val
  · rw [h₁.2 t r hr, h₂.2 t r hr]
  by_cases hr2 : r.val = t.val + 1
  · have key : ∀ f : Fin n → Fin (T + 1), IsLevelAssignment S K f →
        (univ.filter (fun i => S.cat i = t ∧ f i = r)).card +
          ∑ r' ∈ univ.filter (fun r' : Fin (T + 1) => r'.val ≤ t.val), K t r' =
          (S.s t).card := by
      intro f hf
      have e1 := card_filter_add_card_filter_not (s := S.s t) (fun i => (f i).val ≤ t.val)
      have e2 : (S.s t).filter (fun i => ¬ (f i).val ≤ t.val) =
          univ.filter (fun i => S.cat i = t ∧ f i = r) := by
        ext i; simp only [System.s, mem_filter, mem_univ, true_and]
        constructor
        · rintro ⟨hc, hn⟩
          refine ⟨hc, ?_⟩
          have := hf.1 i; rw [hc] at this
          exact Fin.ext (by omega)
        · rintro ⟨hc, rfl⟩; exact ⟨hc, by omega⟩
      have e3 : ((S.s t).filter (fun i => (f i).val ≤ t.val)).card =
          ∑ r' ∈ univ.filter (fun r' : Fin (T + 1) => r'.val ≤ t.val), K t r' := by
        rw [card_eq_sum_card_fiberwise (f := f)
          (t := univ.filter (fun r' : Fin (T + 1) => r'.val ≤ t.val))]
        · apply sum_congr rfl; intro r' hr'
          rw [← hf.2 t r' (mem_filter.mp hr').2]
          congr 1; ext i; simp only [System.s, mem_filter, mem_univ, true_and]
          constructor
          · rintro ⟨⟨hc, _⟩, he⟩; exact ⟨hc, he⟩
          · rintro ⟨hc, rfl⟩; exact ⟨⟨hc, (mem_filter.mp hr').2⟩, rfl⟩
        · intro i hi; rw [mem_coe, mem_filter] at hi
          exact mem_coe.mpr (mem_filter.mpr ⟨mem_univ _, hi.2⟩)
      rw [e2] at e1
      omega
    have k1 := key f₁ h₁; have k2 := key f₂ h₂; omega
  · have hz : ∀ f : Fin n → Fin (T + 1), IsLevelAssignment S K f →
        (univ.filter (fun i => S.cat i = t ∧ f i = r)).card = 0 := by
      intro f hf; rw [card_eq_zero, filter_eq_empty_iff]
      rintro i - ⟨hc, rfl⟩; have := hf.1 i; rw [hc] at this; omega
    rw [hz f₁ h₁, hz f₂ h₂]

lemma exists_sigma (S : System m n T) (K : Fin T → Fin (T + 1) → ℕ)
    (lv : Fin n → Fin (T + 1)) (hlv : IsLevelAssignment S K lv) (hK : InQ S K) :
    ∃ σ : Equiv.Perm (Fin n), (∀ i, S.cat (σ i) = S.cat i) ∧ ∀ i, lvB S K (σ i) = lv i := by
  have hB := lvB_level S K hK
  let F₁ : Fin n → Fin T × Fin (T + 1) := fun i => (S.cat i, lv i)
  let F₂ : Fin n → Fin T × Fin (T + 1) := fun i => (S.cat i, lvB S K i)
  have hcard : ∀ c, Fintype.card {i // F₁ i = c} = Fintype.card {i // F₂ i = c} := by
    rintro ⟨t, r⟩
    rw [Fintype.card_subtype, Fintype.card_subtype]
    simp only [F₁, F₂, Prod.mk.injEq]
    exact fiber_eq S K lv (lvB S K) hlv hB t r
  let e : ∀ c, {i // F₁ i = c} ≃ {i // F₂ i = c} := fun c => Fintype.equivOfCardEq (hcard c)
  refine ⟨Equiv.ofFiberEquiv e, ?_, ?_⟩
  · intro i; have := Equiv.ofFiberEquiv_map e i; exact congrArg Prod.fst this
  · intro i; have := Equiv.ofFiberEquiv_map e i; exact congrArg Prod.snd this

lemma arrange (S : System m n T) (K : Fin T → Fin (T + 1) → ℕ)
    (lv : Fin n → Fin (T + 1)) (hlv : IsLevelAssignment S K lv) (hK : InQ S K) :
    ∃ σ : Equiv.Perm (Fin n), (∀ i, S.cat (σ i) = S.cat i) ∧
      ∀ ε : Fin n → ℝ, ∑ i, ε (σ i) * beta S (S.cat i) (lv i) = blockSum S K ε := by
  obtain ⟨σ, hcat, hlvB⟩ := exists_sigma S K lv hlv hK
  refine ⟨σ, hcat, fun ε => ?_⟩
  rw [blockSum_eq]
  rw [← Equiv.sum_comp σ (fun j => ε j * beta S (S.cat j) (lvB S K j))]
  apply sum_congr rfl; intro i _
  rw [hcat i, hlvB i]

end PF3

open PF3 in
theorem solution {m n T : ℕ} (S : System m n T) (hS : S.IsValid)
    (A : Design m n) (U : Set (Fin n → ℝ)) (μ : Fin n → ℝ)
    (hU : IsSymmetricAround S U μ)
    (hUpos : ∀ d ∈ U, ∀ i, 0 ≤ d i)
    (hUne : U.Nonempty) (hUc : IsCompact U) :
    IsLeast {v : ℝ | ∃ (K : Fin T → Fin (T + 1) → ℕ), InQ S K ∧
      ∃ ε ∈ ((fun d => d - μ) '' U),
        v = dmgi S μ K A + blockSum S K ε}
      (Rf S (fun x _ => x) A U) := by
  have hC := hS.2.2.2.1
  have hU' : IsPartwiseIndepSymmetric S ((fun d => d - μ) '' U) := hU
  have hbddg : BddBelow (f S (fun x _ => x) A '' U) :=
    ⟨0, by rintro _ ⟨d, _, rfl⟩; exact g_nonneg S hS A d⟩
  let zs : (Fin n → Fin (T + 1)) → Fin m → ℝ := fun lv j =>
    (insert 0 ((A.filter (fun a => a.1 = j)).image (fun a => Pbar S (lv a.2)))).max'
      (insert_nonempty _ _)
  have zs_nonneg : ∀ lv j, 0 ≤ zs lv j := fun lv j => le_max' _ _ (mem_insert_self _ _)
  have zs_arc : ∀ lv, ∀ a ∈ A, Pbar S (lv a.2) ≤ zs lv a.1 := by
    intro lv a ha
    show Pbar S (lv a.2) ≤ (insert 0 ((A.filter (fun b => b.1 = a.1)).image
      (fun b => Pbar S (lv b.2)))).max' (insert_nonempty _ _)
    apply le_max'
    apply mem_insert_of_mem
    exact mem_image.mpr ⟨a, mem_filter.mpr ⟨ha, rfl⟩, rfl⟩
  have zs_min : ∀ lv (z : Fin m → ℝ), (∀ j, 0 ≤ z j) → (∀ a ∈ A, Pbar S (lv a.2) ≤ z a.1) →
      ∀ j, zs lv j ≤ z j := by
    intro lv z hz harc j
    apply max'_le; intro x hx; rw [mem_insert, mem_image] at hx
    rcases hx with rfl | ⟨a, ha, rfl⟩
    · exact hz j
    · have ha' := mem_filter.mp ha; rw [← ha'.2]; exact harc a ha'.1
  have feas_iff : ∀ (lv : Fin n → Fin (T + 1)) (z : Fin m → ℝ) (a : Fin m × Fin n),
      S.p a.2 ≤ beta S (S.cat a.2) (lv a.2) + z a.1 ↔ Pbar S (lv a.2) ≤ z a.1 := by
    intro lv z a; unfold beta System.p; constructor <;> intro h <;> linarith
  -- (a) lower bound
  have hlow : ∀ K, InQ S K → ∀ ε ∈ ((fun d => d - μ) '' U),
      Rf S (fun x _ => x) A U ≤ dmgi S μ K A + blockSum S K ε := by
    intro K hK ε hε
    obtain ⟨d0, hd0, rfl⟩ := hε
    have key : Rf S (fun x _ => x) A U - blockSum S K (d0 - μ) ≤ dmgi S μ K A := by
      unfold dmgi
      apply le_csInf
      · exact ⟨_, lvB S K, zs (lvB S K), lvB_level S K hK, zs_nonneg _,
          fun a ha => (feas_iff _ _ a).mpr (zs_arc _ a ha), rfl⟩
      rintro v ⟨lv, z, hlv, hz, harc, rfl⟩
      obtain ⟨σ, hcat, hsum⟩ := arrange S K lv hlv hK
      obtain ⟨d1, hd1, hd1eq⟩ := hU'.2 (d0 - μ) ⟨d0, hd0, rfl⟩ σ (fun i => hcat i)
      have hd1i : ∀ i, d1 i = μ i + (d0 (σ i) - μ (σ i)) := by
        intro i; have := congrFun hd1eq i; simp at this; linarith
      have hw := weak S hS A d1 (hUpos d1 hd1) (fun i => beta S (S.cat i) (lv i)) z
        (fun i => beta_nonneg S hS _ _ (hlv.1 i)) hz harc
      have hRle : Rf S (fun x _ => x) A U ≤ g S A d1 := csInf_le hbddg ⟨d1, hd1, rfl⟩
      have hs := hsum (d0 - μ)
      have hsplit : ∑ i, d1 i * beta S (S.cat i) (lv i) =
          ∑ i, μ i * beta S (S.cat i) (lv i) +
            ∑ i, (d0 - μ) (σ i) * beta S (S.cat i) (lv i) := by
        rw [← sum_add_distrib]; apply sum_congr rfl; intro i _; rw [hd1i]; simp; ring
      linarith
    linarith
  -- (b) membership
  let L : Finset (Fin n → Fin (T + 1)) :=
    univ.filter (fun lv => ∀ i, (lv i).val ≤ (S.cat i).val + 1)
  let a : (Fin n → Fin (T + 1)) → (Fin n → ℝ) → ℝ := fun lv d =>
    ∑ i, d i * beta S (S.cat i) (lv i) + ∑ j, S.C j * zs lv j
  have hacont : ∀ lv, Continuous (a lv) := by
    intro lv
    simp only [a]
    apply Continuous.add _ continuous_const
    exact continuous_finsetSum _ (fun i _ => (continuous_apply i).mul continuous_const)
  have hmin_d : ∀ lv, ∃ d ∈ U, IsMinOn (a lv) U d :=
    fun lv => hUc.exists_isMinOn hUne (hacont lv).continuousOn
  choose dmin hdminU hdmin using hmin_d
  have hLne : L.Nonempty := ⟨fun i => (S.cat i).succ, by simp [L]⟩
  obtain ⟨lv0, hlv0L, hlv0min⟩ := L.exists_min_image (fun lv => a lv (dmin lv)) hLne
  have hstar_le : a lv0 (dmin lv0) ≤ Rf S (fun x _ => x) A U := by
    apply le_csInf (hUne.image _)
    rintro _ ⟨d, hd, rfl⟩
    obtain ⟨lv, hlv, z, hz0, harc, hle⟩ := structured S hS A d (hUpos d hd)
    have hlvL : lv ∈ L := by simp [L, hlv]
    have h1 : a lv0 (dmin lv0) ≤ a lv (dmin lv) := hlv0min lv hlvL
    have h2 : a lv (dmin lv) ≤ a lv d := hdmin lv hd
    have h3 : ∑ j, S.C j * zs lv j ≤ ∑ j, S.C j * z j :=
      sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (zs_min lv z hz0 harc j) (hC j))
    show a lv0 (dmin lv0) ≤ g S A d
    simp only [a] at h1 h2 ⊢
    linarith
  have hlv0L' : ∀ i, (lv0 i).val ≤ (S.cat i).val + 1 := by simpa [L] using hlv0L
  let Ks : Fin T → Fin (T + 1) → ℕ := fun t r =>
    (univ.filter (fun i => S.cat i = t ∧ lv0 i = r)).card
  have hlvK : IsLevelAssignment S Ks lv0 := ⟨hlv0L', fun t r _ => rfl⟩
  have hKs : InQ S Ks := by
    intro t
    have e := card_eq_sum_card_fiberwise (f := lv0)
      (s := univ.filter (fun i => S.cat i = t ∧ (lv0 i).val ≤ t.val))
      (t := univ.filter (fun r : Fin (T + 1) => r.val ≤ t.val))
      (by intro i hi; rw [mem_coe, mem_filter] at hi
          exact mem_coe.mpr (mem_filter.mpr ⟨mem_univ _, hi.2.2⟩))
    have e2 : ∑ r ∈ univ.filter (fun r : Fin (T + 1) => r.val ≤ t.val), Ks t r =
        ∑ b ∈ univ.filter (fun r : Fin (T + 1) => r.val ≤ t.val),
          ((univ.filter (fun i => S.cat i = t ∧ (lv0 i).val ≤ t.val)).filter
            (fun i => lv0 i = b)).card := by
      apply sum_congr rfl; intro r hr
      simp only [Ks]; congr 1; ext i
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨hc, rfl⟩; exact ⟨⟨hc, (mem_filter.mp hr).2⟩, rfl⟩
      · rintro ⟨⟨hc, _⟩, he⟩; exact ⟨hc, he⟩
    rw [e2, ← e]
    apply card_le_card
    intro i hi; simp only [mem_filter, mem_univ, true_and] at hi
    simp [System.s, hi.1]
  obtain ⟨σ, hcat, hsum⟩ := arrange S Ks lv0 hlvK hKs
  set dstar := dmin lv0 with hdstar
  set ε'' : Fin n → ℝ := (dstar - μ) ∘ σ.symm with hε''def
  have hε'' : ε'' ∈ (fun d => d - μ) '' U :=
    hU'.2 (dstar - μ) ⟨dstar, hdminU lv0, rfl⟩ σ.symm (fun i => by
      have := hcat (σ.symm i); simp at this; exact this.symm)
  have hbs : blockSum S Ks ε'' = ∑ i, (dstar - μ) i * beta S (S.cat i) (lv0 i) := by
    rw [← hsum ε'']; apply sum_congr rfl; intro i _; simp [hε''def]
  have hbdd_dmgi : BddBelow {v | ∃ (lv : Fin n → Fin (T + 1)) (z : Fin m → ℝ),
      IsLevelAssignment S Ks lv ∧ (∀ j, 0 ≤ z j) ∧
      (∀ a ∈ A, S.p a.2 ≤ beta S (S.cat a.2) (lv a.2) + z a.1) ∧
      v = ∑ i, μ i * beta S (S.cat i) (lv i) + ∑ j, S.C j * z j} := by
    refine ⟨∑ i, (-|μ i| * S.P (S.cat i)), ?_⟩
    rintro v ⟨lv, z, hlv, hz, _, rfl⟩
    have h1 : 0 ≤ ∑ j, S.C j * z j := sum_nonneg (fun j _ => mul_nonneg (hC j) (hz j))
    have h2 : ∑ i, (-|μ i| * S.P (S.cat i)) ≤ ∑ i, μ i * beta S (S.cat i) (lv i) := by
      apply sum_le_sum; intro i _
      have b0 := beta_nonneg S hS (S.cat i) (lv i) (hlv.1 i)
      have b1 := beta_le S hS (S.cat i) (lv i)
      have m1 := neg_abs_le (μ i)
      have m2 := abs_nonneg (μ i)
      nlinarith
    linarith
  have hdm : dmgi S μ Ks A ≤ ∑ i, μ i * beta S (S.cat i) (lv0 i) + ∑ j, S.C j * zs lv0 j := by
    unfold dmgi
    exact csInf_le hbdd_dmgi ⟨lv0, zs lv0, hlvK, zs_nonneg _,
      fun a ha => (feas_iff _ _ a).mpr (zs_arc _ a ha), rfl⟩
  have hv1_le : dmgi S μ Ks A + blockSum S Ks ε'' ≤ Rf S (fun x _ => x) A U := by
    rw [hbs]
    have : a lv0 dstar = ∑ i, μ i * beta S (S.cat i) (lv0 i) + ∑ j, S.C j * zs lv0 j +
        ∑ i, (dstar - μ) i * beta S (S.cat i) (lv0 i) := by
      simp only [a]
      have : ∑ i, dstar i * beta S (S.cat i) (lv0 i) = ∑ i, μ i * beta S (S.cat i) (lv0 i) +
          ∑ i, (dstar - μ) i * beta S (S.cat i) (lv0 i) := by
        rw [← sum_add_distrib]; apply sum_congr rfl; intro i _; simp; ring
      rw [this]; ring
    linarith
  have heq := le_antisymm (hlow Ks hKs ε'' hε'') hv1_le
  refine ⟨⟨Ks, hKs, ε'', hε'', heq⟩, ?_⟩
  rintro v ⟨K, hK, ε, hε, rfl⟩
  exact hlow K hK ε hε
