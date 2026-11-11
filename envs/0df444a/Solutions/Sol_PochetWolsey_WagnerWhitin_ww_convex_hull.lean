-- Prove2me | solution 1 for PochetWolsey.WagnerWhitin.ww_convex_hull
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-11T04:43:22.010905+00:00
-- url     : https://prove2.me/submissions/43fdac57-73a1-460d-9a8c-d9c2187e33a8

import Mathlib

set_option autoImplicit false

open scoped BigOperators

namespace WWHullAux

/-- cumulative vectors with steps in `[0,1]` starting at `0` -/
def Adm (m : ℕ) (C : Fin (m + 1) → ℝ) : Prop :=
  C 0 = 0 ∧ ∀ i : Fin m, 0 ≤ C i.succ - C i.castSucc ∧ C i.succ - C i.castSucc ≤ 1

def Psi (m : ℕ) (C : Fin (m + 1) → ℝ) :
    (Fin (m + 1) → ℝ) × (Fin (m + 1) × Fin (m + 1) → ℝ) :=
  (C, fun p => max 0 (1 - (C p.2 - C p.1)))

def IntSet (m : ℕ) : Set (Fin (m + 1) → ℝ) :=
  {C | Adm m C ∧ ∀ i, ∃ z : ℤ, C i = z}

noncomputable def nfr (m : ℕ) (C : Fin (m + 1) → ℝ) : ℕ :=
  (Finset.univ.filter (fun i => Int.fract (C i) ≠ 0)).card

lemma ceil_bound (x β : ℝ) (hβ1 : β ≤ 1) (h : Int.fract x = 0 ∨ β ≤ Int.fract x) :
    (⌈x⌉ : ℝ) - (1 - β) ≤ x := by
  rcases h with h | h
  · have hx : x = (⌊x⌋ : ℝ) := by
      have := Int.floor_add_fract x
      rw [h] at this; linarith
    obtain ⟨z, rfl⟩ : ∃ z : ℤ, x = z := ⟨⌊x⌋, hx⟩
    rw [Int.ceil_intCast]; linarith
  · have h1 := Int.ceil_le_floor_add_one x
    have h2 := Int.floor_add_fract x
    have h1' : (⌈x⌉ : ℝ) ≤ ⌊x⌋ + 1 := by exact_mod_cast h1
    linarith

lemma phi_split (a b β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (A B : ℤ)
    (ha1 : (A : ℝ) - (1 - β) ≤ a) (ha2 : a ≤ A) (hb1 : (B : ℝ) - (1 - β) ≤ b) (hb2 : b ≤ B) :
    max 0 (1 - (b - a)) = β * max 0 (1 - ((B : ℝ) - A)) +
      (1 - β) * max 0 (1 - ((b - β * B) / (1 - β) - (a - β * A) / (1 - β))) := by
  have hne : (1 - β) ≠ 0 := by linarith
  have key : (1 - β) * max 0 (1 - ((b - β * B) / (1 - β) - (a - β * A) / (1 - β))) =
      max 0 ((1 - β) - (b - a) + β * ((B : ℝ) - A)) := by
    rw [mul_max_of_nonneg _ _ (by linarith)]
    congr 1
    · ring
    · field_simp; ring
  rw [key]
  rcases le_or_gt (B - A) 0 with hD | hD
  · have hDr : ((B : ℝ) - A) ≤ 0 := by
      have : (B : ℝ) ≤ A := by exact_mod_cast (by omega : B ≤ A)
      linarith
    have h1 : 0 ≤ 1 - (b - a) := by linarith
    have h2 : 0 ≤ 1 - ((B : ℝ) - A) := by linarith
    have h3 : 0 ≤ (1 - β) - (b - a) + β * ((B : ℝ) - A) := by nlinarith
    rw [max_eq_right h1, max_eq_right h2, max_eq_right h3]; ring
  · rcases (show B - A = 1 ∨ 2 ≤ B - A by omega) with hD1 | hD2
    · have hDr : ((B : ℝ) - A) = 1 := by
        have : (B : ℝ) = A + 1 := by exact_mod_cast (by omega : B = A + 1)
        linarith
      have e : (1 - β) - (b - a) + β * ((B : ℝ) - A) = 1 - (b - a) := by rw [hDr]; ring
      rw [e, hDr]; simp
    · have hDr : 2 ≤ ((B : ℝ) - A) := by
        have : (A : ℝ) + 2 ≤ B := by exact_mod_cast (by omega : A + 2 ≤ B)
        linarith
      have h1 : 1 - (b - a) ≤ 0 := by linarith
      have h2 : 1 - ((B : ℝ) - A) ≤ 0 := by linarith
      have h3 : (1 - β) - (b - a) + β * ((B : ℝ) - A) ≤ 0 := by nlinarith
      rw [max_eq_left h1, max_eq_left h2, max_eq_left h3]; ring

theorem core (m : ℕ) : ∀ N : ℕ, ∀ C : Fin (m + 1) → ℝ, Adm m C → nfr m C ≤ N →
    Psi m C ∈ convexHull ℝ (Psi m '' IntSet m) := by
  intro N
  induction N with
  | zero =>
    intro C hC hN
    apply subset_convexHull
    refine ⟨C, ⟨hC, ?_⟩, rfl⟩
    intro i
    have hfr : Int.fract (C i) = 0 := by
      by_contra hne
      have hi : i ∈ Finset.univ.filter (fun i => Int.fract (C i) ≠ 0) := by simp [hne]
      have := Finset.card_pos.2 ⟨i, hi⟩
      unfold nfr at hN; omega
    exact ⟨⌊C i⌋, by have := Int.floor_add_fract (C i); linarith⟩
  | succ N ih =>
    intro C hC hN
    by_cases h0 : nfr m C ≤ N
    · exact ih C hC h0
    set S := Finset.univ.filter (fun i => Int.fract (C i) ≠ 0) with hS
    have hnS : nfr m C = S.card := rfl
    have hcardS : S.card = N + 1 := by omega
    have hSne : S.Nonempty := by
      rw [← Finset.card_pos, hcardS]; omega
    set F := S.image (fun i => Int.fract (C i)) with hF
    have hFne : F.Nonempty := hSne.image _
    set β := F.min' hFne with hβdef
    obtain ⟨i0, hi0S, hi0⟩ : ∃ i0 ∈ S, Int.fract (C i0) = β := by
      have := F.min'_mem hFne
      rw [← hβdef, hF, Finset.mem_image] at this
      exact this
    have hi0ne : Int.fract (C i0) ≠ 0 := (Finset.mem_filter.1 hi0S).2
    have hβpos : 0 < β := by
      rw [← hi0]; exact lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm hi0ne)
    have hβlt : β < 1 := by rw [← hi0]; exact Int.fract_lt_one _
    have hne : (1 - β) ≠ 0 := by linarith
    have hmin : ∀ i, Int.fract (C i) = 0 ∨ β ≤ Int.fract (C i) := by
      intro i
      by_cases h : Int.fract (C i) = 0
      · exact Or.inl h
      · right
        apply F.min'_le
        exact Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    have hlow : ∀ i, (⌈C i⌉ : ℝ) - (1 - β) ≤ C i := fun i => ceil_bound _ _ hβlt.le (hmin i)
    have hup : ∀ i, C i ≤ ⌈C i⌉ := fun i => Int.le_ceil _
    set C1 : Fin (m + 1) → ℝ := fun i => (⌈C i⌉ : ℝ) with hC1def
    set C2 : Fin (m + 1) → ℝ := fun i => (C i - β * ⌈C i⌉) / (1 - β) with hC2def
    have hceilstep : ∀ i : Fin m, ⌈C i.succ⌉ = ⌈C i.castSucc⌉ ∨
        ⌈C i.succ⌉ = ⌈C i.castSucc⌉ + 1 := by
      intro i
      have hst := hC.2 i
      have h1 : ⌈C i.castSucc⌉ ≤ ⌈C i.succ⌉ := Int.ceil_mono (by linarith)
      have h2 : ⌈C i.succ⌉ ≤ ⌈C i.castSucc⌉ + 1 := by
        rw [← Int.ceil_add_one]; exact Int.ceil_mono (by linarith)
      omega
    have hC1 : C1 ∈ IntSet m := by
      refine ⟨⟨?_, fun i => ?_⟩, fun i => ⟨⌈C i⌉, rfl⟩⟩
      · simp [hC1def, hC.1]
      · simp only [hC1def]
        rcases hceilstep i with h | h
        · rw [h]; constructor <;> linarith
        · rw [h]; push_cast; constructor <;> linarith
    have hC2adm : Adm m C2 := by
      refine ⟨?_, fun i => ?_⟩
      · simp [hC2def, hC.1]
      · simp only [hC2def]
        rw [div_sub_div_same]
        have hst := hC.2 i
        have ha1 := hlow i.castSucc
        have hb1 := hlow i.succ
        have ha2 := hup i.castSucc
        have hb2 := hup i.succ
        have hpos : 0 < 1 - β := by linarith
        rcases hceilstep i with h | h
        · rw [h] at hb1 hb2 ⊢
          constructor
          · apply div_nonneg _ hpos.le; linarith
          · rw [div_le_one hpos]; linarith
        · rw [h] at hb1 hb2 ⊢
          push_cast at hb1 hb2 ⊢
          constructor
          · apply div_nonneg _ hpos.le; linarith
          · rw [div_le_one hpos]; linarith
    have hC2int : ∀ i, Int.fract (C i) = 0 ∨ Int.fract (C i) = β → Int.fract (C2 i) = 0 := by
      intro i hi
      rcases hi with h | h
      · have hx : C i = (⌊C i⌋ : ℝ) := by
          have := Int.floor_add_fract (C i)
          rw [h] at this; linarith
        have : C2 i = C i := by
          simp only [hC2def]
          rw [div_eq_iff hne, hx, Int.ceil_intCast]; ring
        rw [this, hx, Int.fract_intCast]
      · have hfl := Int.floor_add_fract (C i)
        have hne0 : Int.fract (C i) ≠ 0 := by rw [h]; exact hβpos.ne'
        have hce := Int.ceil_sub_self_eq hne0
        have : C2 i = (⌊C i⌋ : ℝ) := by
          simp only [hC2def]
          rw [div_eq_iff hne]
          have hc : (⌈C i⌉ : ℝ) = ⌊C i⌋ + 1 := by rw [h] at hce hfl; linarith
          rw [hc]; rw [h] at hfl; nlinarith
        rw [this, Int.fract_intCast]
    have hC2n : nfr m C2 ≤ N := by
      have hsub : (Finset.univ.filter (fun i => Int.fract (C2 i) ≠ 0)) ⊆ S.erase i0 := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        rw [Finset.mem_erase]
        refine ⟨?_, ?_⟩
        · rintro rfl; exact hi (hC2int _ (Or.inr hi0))
        · simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
          intro h; exact hi (hC2int _ (Or.inl h))
      have := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hi0S, hcardS] at this
      unfold nfr; omega
    have hdecomp : Psi m C = β • Psi m C1 + (1 - β) • Psi m C2 := by
      refine Prod.ext (funext fun i => ?_) (funext fun p => ?_)
      · simp only [Psi, Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          hC1def, hC2def]
        field_simp; ring
      · simp only [Psi, Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          hC1def, hC2def]
        exact phi_split _ _ β hβpos hβlt _ _ (hlow p.1) (hup p.1) (hlow p.2) (hup p.2)
    rw [hdecomp]
    exact convex_convexHull ℝ _ (subset_convexHull ℝ _ (Set.mem_image_of_mem (Psi m) hC1))
      (ih C2 hC2adm hC2n) hβpos.le (by linarith) (by ring)

end WWHullAux

namespace WWHullAux

variable {n : ℕ}

noncomputable def cum (y : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  fun i => ∑ u : Fin n, if u.castSucc < i then y u else 0

lemma cum_zero (y : Fin n → ℝ) : cum y 0 = 0 := by
  simp [cum]

lemma cum_step (y : Fin n → ℝ) (i : Fin n) : cum y i.succ - cum y i.castSucc = y i := by
  have h : ∀ u : Fin n, ((if u.castSucc < i.succ then y u else 0) -
      (if u.castSucc < i.castSucc then y u else 0)) = if u = i then y u else 0 := by
    intro u
    have hv : u = i ↔ u.val = i.val := Fin.ext_iff
    simp only [Fin.lt_iff_val_lt_val, Fin.coe_castSucc, Fin.val_succ, hv]
    split_ifs <;> first | ring1 | (exfalso; omega)
  simp only [cum]
  rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl (fun u _ => h u), Finset.sum_ite_eq']
  simp

lemma sum_Icc_eq (y : Fin n → ℝ) (k j : Fin n) (hkj : k ≤ j) :
    ∑ u ∈ Finset.Icc k j, y u = cum y j.succ - cum y k.castSucc := by
  have hkj' : k.val ≤ j.val := hkj
  have h : ∀ u : Fin n, ((if u.castSucc < j.succ then y u else 0) -
      (if u.castSucc < k.castSucc then y u else 0)) =
        if u ∈ Finset.Icc k j then y u else 0 := by
    intro u
    simp only [Finset.mem_Icc, Fin.le_iff_val_le_val, Fin.lt_iff_val_lt_val, Fin.coe_castSucc,
      Fin.val_succ]
    split_ifs <;> first | ring1 | (exfalso; omega)
  simp only [cum]
  rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl (fun u _ => h u), Finset.sum_ite_mem,
    Finset.univ_inter]

lemma cum_mono (y : Fin n → ℝ) (hy : ∀ u, 0 ≤ y u) {a b : Fin (n + 1)} (hab : a ≤ b) :
    cum y a ≤ cum y b := by
  apply Finset.sum_le_sum
  intro u _
  split_ifs with h1 h2 h2
  · exact le_refl _
  · exact absurd (lt_of_lt_of_le h1 hab) h2
  · exact hy u
  · exact le_refl _

lemma cum_of_adm (C : Fin (n + 1) → ℝ) (hC : Adm n C) :
    cum (fun u => C u.succ - C u.castSucc) = C := by
  funext i
  induction i using Fin.induction with
  | zero => rw [cum_zero, hC.1]
  | succ i ih =>
    have h : cum (fun u => C u.succ - C u.castSucc) i.succ -
        cum (fun u => C u.succ - C u.castSucc) i.castSucc = C i.succ - C i.castSucc :=
      cum_step _ i
    linarith

noncomputable def G (d : Fin n → ℝ) (C : Fin (n + 1) → ℝ) (t : Fin (n + 1)) : ℝ :=
  ∑ j : Fin n, if t ≤ j.castSucc then d j * max 0 (1 - (C j.succ - C t)) else 0

lemma G_nonneg (d : Fin n → ℝ) (hd : ∀ t, 0 ≤ d t) (C : Fin (n + 1) → ℝ) (t : Fin (n + 1)) :
    0 ≤ G d C t := by
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact mul_nonneg (hd j) (le_max_left _ _)
  · exact le_refl _

lemma G_ge (d : Fin n → ℝ) (hd : ∀ t, 0 ≤ d t) (C : Fin (n + 1) → ℝ) (k l : Fin n) :
    ∑ j ∈ Finset.Icc k l, d j * (1 - (C j.succ - C k.castSucc)) ≤ G d C k.castSucc := by
  calc ∑ j ∈ Finset.Icc k l, d j * (1 - (C j.succ - C k.castSucc))
      ≤ ∑ j ∈ Finset.Icc k l, (if k.castSucc ≤ j.castSucc then
          d j * max 0 (1 - (C j.succ - C k.castSucc)) else 0) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [if_pos (Fin.castSucc_le_castSucc_iff.2 (Finset.mem_Icc.1 hj).1)]
        exact mul_le_mul_of_nonneg_left (le_max_right _ _) (hd j)
    _ ≤ G d C k.castSucc := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro j _ _
        split_ifs
        · exact mul_nonneg (hd j) (le_max_left _ _)
        · exact le_refl _

lemma G_le (d : Fin n → ℝ) (s : Fin (n + 1) → ℝ) (y : Fin n → ℝ)
    (hs0 : ∀ t, 0 ≤ s t) (hy : ∀ t, 0 ≤ y t ∧ y t ≤ 1)
    (hcon : ∀ k l : Fin n, k ≤ l → s k.castSucc ≥ ∑ j ∈ Finset.Icc k l,
      d j * (1 - ∑ u ∈ Finset.Icc k j, y u))
    (t : Fin (n + 1)) : G d (cum y) t ≤ s t := by
  induction t using Fin.lastCases with
  | last =>
    have : G d (cum y) (Fin.last n) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [if_neg]
      exact not_le.2 (Fin.castSucc_lt_last j)
    rw [this]; exact hs0 _
  | cast k =>
    set C := cum y with hCdef
    set L := Finset.univ.filter (fun j : Fin n => k ≤ j ∧ C j.succ - C k.castSucc ≤ 1) with hL
    have hkL : k ∈ L := by
      simp only [hL, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨le_refl _, ?_⟩
      rw [hCdef, cum_step]; exact (hy k).2
    set l := L.max' ⟨k, hkL⟩ with hldef
    have hlL : l ∈ L := L.max'_mem _
    simp only [hL, Finset.mem_filter, Finset.mem_univ, true_and] at hlL
    have hkl : k ≤ l := hlL.1
    have hc := hcon k l hkl
    have e1 : ∑ j ∈ Finset.Icc k l, d j * (1 - ∑ u ∈ Finset.Icc k j, y u) =
        ∑ j ∈ Finset.Icc k l, d j * (1 - (C j.succ - C k.castSucc)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [sum_Icc_eq y k j (Finset.mem_Icc.1 hj).1]
    have e2 : G d C k.castSucc = ∑ j ∈ Finset.Icc k l, d j * (1 - (C j.succ - C k.castSucc)) := by
      unfold G
      rw [← Finset.sum_subset (Finset.subset_univ (Finset.Icc k l))]
      · apply Finset.sum_congr rfl
        intro j hj
        have hj' := Finset.mem_Icc.1 hj
        rw [if_pos (Fin.castSucc_le_castSucc_iff.2 hj'.1)]
        have hmono : C j.succ ≤ C l.succ :=
          cum_mono y (fun u => (hy u).1) (Fin.succ_le_succ_iff.2 hj'.2)
        rw [max_eq_right (by linarith [hlL.2])]
      · intro j _ hj
        rw [Finset.mem_Icc] at hj
        split_ifs with h
        · have hkj : k ≤ j := Fin.castSucc_le_castSucc_iff.1 h
          have hlj : ¬ j ≤ l := fun h' => hj ⟨hkj, h'⟩
          have hjL : j ∉ L := fun hj2 => hlj (L.le_max' j hj2)
          simp only [hL, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_le] at hjL
          rw [max_eq_left (by linarith [hjL hkj]), mul_zero]
        · rfl
    rw [e2, ← e1]; exact hc

def Pset (n : ℕ) (d : Fin n → ℝ) : Set ((Fin (n + 1) → ℝ) × (Fin n → ℝ)) :=
  {z | (∀ t, 0 ≤ z.1 t) ∧ (∀ t, 0 ≤ z.2 t ∧ z.2 t ≤ 1) ∧
        ∀ k l : Fin n, k ≤ l →
          z.1 k.castSucc ≥ ∑ j ∈ Finset.Icc k l,
            d j * (1 - ∑ u ∈ Finset.Icc k j, z.2 u)}

def Xset (n : ℕ) (d : Fin n → ℝ) : Set ((Fin (n + 1) → ℝ) × (Fin n → ℝ)) :=
  {z | z ∈ Pset n d ∧ ∀ t, ∃ a : ℤ, z.2 t = (a : ℝ)}

theorem Pset_convex (d : Fin n → ℝ) : Convex ℝ (Pset n d) := by
  intro z1 hz1 z2 hz2 a b ha hb hab
  simp only [Pset, Set.mem_setOf_eq] at hz1 hz2 ⊢
  obtain ⟨h1s, h1y, h1c⟩ := hz1
  obtain ⟨h2s, h2y, h2c⟩ := hz2
  refine ⟨fun t => ?_, fun t => ?_, fun k l hkl => ?_⟩
  · simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (h1s t)) (mul_nonneg hb (h2s t))
  · simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    obtain ⟨p1, q1⟩ := h1y t
    obtain ⟨p2, q2⟩ := h2y t
    constructor <;> nlinarith
  · simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    have e : ∑ j ∈ Finset.Icc k l, d j * (1 - ∑ u ∈ Finset.Icc k j, (a * z1.2 u + b * z2.2 u)) =
        a * ∑ j ∈ Finset.Icc k l, d j * (1 - ∑ u ∈ Finset.Icc k j, z1.2 u) +
        b * ∑ j ∈ Finset.Icc k l, d j * (1 - ∑ u ∈ Finset.Icc k j, z2.2 u) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      linear_combination (-(d j)) * hab
    rw [e]
    linarith [mul_le_mul_of_nonneg_left (h1c k l hkl) ha,
      mul_le_mul_of_nonneg_left (h2c k l hkl) hb]

theorem Pset_sub (d : Fin n → ℝ) (hd : ∀ t, 0 ≤ d t) :
    Pset n d ⊆ convexHull ℝ (Xset n d) := by
  rintro ⟨s, y⟩ hz
  simp only [Pset, Set.mem_setOf_eq] at hz
  obtain ⟨hs0, hy, hcon⟩ := hz
  have hCadm : Adm n (cum y) := ⟨cum_zero y, fun i => by rw [cum_step]; exact hy i⟩
  obtain ⟨ι, hι, w, p, hw0, hw1, hp, hsum⟩ :=
    mem_convexHull_iff_exists_fintype.1 (core n _ (cum y) hCadm le_rfl)
  choose C' hC' hpC' using hp
  have hp' : p = fun i => Psi n (C' i) := funext fun i => (hpC' i).symm
  subst hp'
  have hcomp1 : ∀ t, ∑ i, w i * C' i t = cum y t := by
    intro t
    have := congrArg (fun q => q.1 t) hsum
    simpa [Psi, Prod.fst_sum, Finset.sum_apply] using this
  have hcomp2 : ∀ a b : Fin (n + 1), ∑ i, w i * max 0 (1 - (C' i b - C' i a)) =
      max 0 (1 - (cum y b - cum y a)) := by
    intro a b
    have := congrArg (fun q => q.2 (a, b)) hsum
    simpa [Psi, Prod.snd_sum, Finset.sum_apply] using this
  have hGlin : ∀ t, ∑ i, w i * G d (C' i) t = G d (cum y) t := by
    intro t
    simp only [G, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs
    · rw [← hcomp2 t j.succ, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    · simp
  set yh : ι → Fin n → ℝ := fun i u => C' i u.succ - C' i u.castSucc with hyh
  have hcumC : ∀ i, cum (yh i) = C' i := fun i => cum_of_adm (C' i) (hC' i).1
  set sh : ι → Fin (n + 1) → ℝ :=
    fun i t => s t - ∑ l, w l * G d (C' l) t + G d (C' i) t with hsh
  have hslack : ∀ t, 0 ≤ s t - ∑ l, w l * G d (C' l) t := fun t => by
    rw [hGlin]; linarith [G_le d s y hs0 hy hcon t]
  apply mem_convexHull_of_exists_fintype w (fun i => (sh i, yh i)) hw0 hw1
  · intro i
    show (sh i, yh i) ∈ Xset n d
    simp only [Xset, Pset, Set.mem_setOf_eq]
    refine ⟨⟨fun t => ?_, fun t => ?_, fun k l hkl => ?_⟩, fun t => ?_⟩
    · show 0 ≤ sh i t
      simp only [hsh]; linarith [hslack t, G_nonneg d hd (C' i) t]
    · show 0 ≤ yh i t ∧ yh i t ≤ 1
      exact (hC' i).1.2 t
    · show sh i k.castSucc ≥ ∑ j ∈ Finset.Icc k l, d j * (1 - ∑ u ∈ Finset.Icc k j, yh i u)
      have e1 : ∑ j ∈ Finset.Icc k l, d j * (1 - ∑ u ∈ Finset.Icc k j, yh i u) =
          ∑ j ∈ Finset.Icc k l, d j * (1 - (C' i j.succ - C' i k.castSucc)) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [sum_Icc_eq (yh i) k j (Finset.mem_Icc.1 hj).1, hcumC i]
      rw [e1]
      simp only [hsh]
      linarith [hslack k.castSucc, G_ge d hd (C' i) k l]
    · show ∃ a : ℤ, yh i t = a
      obtain ⟨z1, hz1⟩ := (hC' i).2 t.succ
      obtain ⟨z2, hz2⟩ := (hC' i).2 t.castSucc
      exact ⟨z1 - z2, by simp only [hyh]; rw [hz1, hz2]; push_cast; ring⟩
  · refine Prod.ext (funext fun t => ?_) (funext fun u => ?_)
    · simp only [Prod.fst_sum, Finset.sum_apply, Prod.smul_mk, Pi.smul_apply, smul_eq_mul, hsh]
      simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.sum_mul, hw1]
      ring
    · simp only [Prod.snd_sum, Finset.sum_apply, Prod.smul_mk, Pi.smul_apply, smul_eq_mul, hyh]
      simp only [mul_sub, Finset.sum_sub_distrib, hcomp1]
      exact cum_step y u

theorem hull_eq (d : Fin n → ℝ) (hd : ∀ t, 0 ≤ d t) :
    Pset n d = convexHull ℝ (Xset n d) :=
  Set.Subset.antisymm (Pset_sub d hd)
    (convexHull_min (fun z (hz : z ∈ Xset n d) => by
      simp only [Xset, Set.mem_setOf_eq] at hz; exact hz.1) (Pset_convex d))

end WWHullAux

theorem solution (n : ℕ) (hn : 0 < n)
    (d : Fin n → ℝ) (hd : ∀ t, 0 ≤ d t) :
    let P : Set ((Fin (n + 1) → ℝ) × (Fin n → ℝ)) :=
      {z | (∀ t, 0 ≤ z.1 t) ∧ (∀ t, 0 ≤ z.2 t ∧ z.2 t ≤ 1) ∧
        ∀ k l : Fin n, k ≤ l →
          z.1 k.castSucc ≥ ∑ j ∈ Finset.Icc k l,
            d j * (1 - ∑ u ∈ Finset.Icc k j, z.2 u)}
    let X : Set ((Fin (n + 1) → ℝ) × (Fin n → ℝ)) :=
      {z | z ∈ P ∧ ∀ t, ∃ a : ℤ, z.2 t = (a : ℝ)}
    let cost := fun (h : Fin (n + 1) → ℝ) (q : Fin n → ℝ)
      (z : (Fin (n + 1) → ℝ) × (Fin n → ℝ)) =>
        (∑ t, h t * z.1 t) + ∑ t, q t * z.2 t
    (∀ (h : Fin (n + 1) → ℝ) (q : Fin n → ℝ), (∀ t, 0 ≤ h t) →
      ∀ z, z ∈ P.extremePoints ℝ →
        (∀ w ∈ P, cost h q z ≤ cost h q w) →
          z ∈ X ∧ ∀ w ∈ X, cost h q z ≤ cost h q w) ∧
    P = convexHull ℝ X := by
  intro P X cost
  have hE : P = convexHull ℝ X := WWHullAux.hull_eq d hd
  refine ⟨?_, hE⟩
  intro h q _ z hz hopt
  have hzX : z ∈ X := by
    rw [hE] at hz
    exact extremePoints_convexHull_subset hz
  exact ⟨hzX, fun w hw => hopt w (show w ∈ WWHullAux.Xset n d from hw).1⟩
