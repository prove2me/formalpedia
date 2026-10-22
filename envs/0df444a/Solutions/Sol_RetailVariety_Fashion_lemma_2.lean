-- Prove2me | solution 1 for RetailVariety.Fashion.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T02:41:31.929494+00:00
-- url     : https://prove2.me/submissions/0580926f-d71b-47ec-b7a4-089cbc73b450

import Mathlib
import Definitions.Def_RetailVariety_Fashion_Majorization



namespace RetailVariety.Fashion

noncomputable def chord (g : ℝ → ℝ) (a b : ℝ) : ℝ := (g b - g a) / (b - a)

lemma chord_symm (g : ℝ → ℝ) (a b : ℝ) : chord g a b = chord g b a := by
  unfold chord
  by_cases h : b = a
  · subst h; simp
  · rw [← neg_sub (g b) (g a), ← neg_sub b a, neg_div_neg_eq]

lemma chord_mono {s : Set ℝ} {g : ℝ → ℝ} (hg : ConvexOn ℝ s g) {a a' b b' : ℝ}
    (ha : a ∈ s) (ha' : a' ∈ s) (hb : b ∈ s) (hb' : b' ∈ s)
    (haa : a' ≤ a) (hbb : b' ≤ b) (hab : a ≠ b) (hab' : a' ≠ b') :
    chord g a' b' ≤ chord g a b := by
  by_cases h1 : a = b'
  · by_cases h2 : b = a'
    · exfalso; apply hab; linarith
    · -- path 2
      calc chord g a' b' ≤ chord g a' b := hg.secant_mono ha' hb' hb (Ne.symm hab') h2 hbb
        _ = chord g b a' := chord_symm g _ _
        _ ≤ chord g b a := hg.secant_mono hb ha' ha (Ne.symm h2) hab haa
        _ = chord g a b := chord_symm g _ _
  · calc chord g a' b' = chord g b' a' := chord_symm g _ _
      _ ≤ chord g b' a := hg.secant_mono hb' ha' ha hab' h1 haa
      _ = chord g a b' := chord_symm g _ _
      _ ≤ chord g a b := hg.secant_mono ha hb' hb (Ne.symm h1) (Ne.symm hab) hbb

lemma abel_nonneg (c d : ℕ → ℝ) (hc : ∀ i j, i ≤ j → c j ≤ c i) (N : ℕ)
    (hD : ∀ k ≤ N, 0 ≤ ∑ i ∈ Finset.range k, d i) :
    ∀ n ≤ N, c n * ∑ i ∈ Finset.range n, d i ≤ ∑ i ∈ Finset.range n, c i * d i := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have h1 := ih (by omega)
    have h2 := hD (n + 1) hn
    rw [Finset.sum_range_succ] at h2 ⊢
    rw [Finset.sum_range_succ]
    have h3 : c (n + 1) ≤ c n := hc n (n + 1) (by omega)
    nlinarith

lemma karamata_nat {s : Set ℝ} {g : ℝ → ℝ} (hg : ConvexOn ℝ s g) (N : ℕ) (x y : ℕ → ℝ)
    (hxs : ∀ i < N, x i ∈ s) (hys : ∀ i < N, y i ∈ s)
    (hxa : ∀ i j, i ≤ j → j < N → x j ≤ x i) (hya : ∀ i j, i ≤ j → j < N → y j ≤ y i)
    (hpart : ∀ k ≤ N, ∑ i ∈ Finset.range k, x i ≤ ∑ i ∈ Finset.range k, y i)
    (htot : ∑ i ∈ Finset.range N, x i = ∑ i ∈ Finset.range N, y i) :
    ∑ i ∈ Finset.range N, g (x i) ≤ ∑ i ∈ Finset.range N, g (y i) := by
  set σ : ℕ → ℝ := fun j => chord g (x j) (y j) with hσ
  set B : ℝ := ∑ j ∈ Finset.range N, |σ j| with hB
  set T : ℕ → Finset ℕ := fun i => (Finset.range N).filter (fun j => i ≤ j ∧ x j ≠ y j) with hT
  set c : ℕ → ℝ := fun i => sSup (insert (-B) (σ '' (T i : Set ℕ))) with hc
  have hbdd : ∀ i, BddAbove (insert (-B) (σ '' (T i : Set ℕ))) := fun i =>
    (Set.Finite.insert _ ((T i).finite_toSet.image _)).bddAbove
  have hc_anti : ∀ i j, i ≤ j → c j ≤ c i := by
    intro i j hij
    apply csSup_le_csSup (hbdd i) (Set.insert_nonempty _ _)
    apply Set.insert_subset_insert
    apply Set.image_mono
    intro m hm
    simp only [hT, Finset.coe_filter, Set.mem_setOf_eq] at hm ⊢
    exact ⟨hm.1, le_trans hij hm.2.1, hm.2.2⟩
  have hc_eq : ∀ j < N, x j ≠ y j → c j = σ j := by
    intro j hj hne
    have hjT : j ∈ T j := by simp [hT, hj, hne]
    apply le_antisymm
    · apply csSup_le (Set.insert_nonempty _ _)
      intro z hz
      rcases hz with rfl | ⟨m, hm, rfl⟩
      · have h1 : |σ j| ≤ B := by
          rw [hB]
          exact Finset.single_le_sum (f := fun j => |σ j|) (fun _ _ => abs_nonneg _) (Finset.mem_range.2 hj)
        have := neg_abs_le (σ j)
        linarith
      · simp only [hT, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hm
        obtain ⟨hmN, hjm, hmne⟩ := hm
        exact chord_mono hg (hxs j hj) (hxs m hmN) (hys j hj) (hys m hmN)
          (hxa j m hjm hmN) (hya j m hjm hmN) hne hmne
    · exact le_csSup (hbdd j) (Set.mem_insert_of_mem _ ⟨j, by exact_mod_cast hjT, rfl⟩)
  have hterm : ∀ i < N, c i * (y i - x i) = g (y i) - g (x i) := by
    intro i hi
    by_cases hne : x i = y i
    · rw [hne]; simp
    · rw [hc_eq i hi hne]
      simp only [hσ, chord]
      have : y i - x i ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
      field_simp
  have hD : ∀ k ≤ N, 0 ≤ ∑ i ∈ Finset.range k, (y i - x i) := by
    intro k hk
    rw [Finset.sum_sub_distrib]
    linarith [hpart k hk]
  have habel := abel_nonneg c (fun i => y i - x i) hc_anti N hD N le_rfl
  have hDN : ∑ i ∈ Finset.range N, (y i - x i) = 0 := by
    rw [Finset.sum_sub_distrib]; linarith
  rw [hDN, mul_zero] at habel
  have : ∑ i ∈ Finset.range N, c i * (y i - x i) = ∑ i ∈ Finset.range N, (g (y i) - g (x i)) :=
    Finset.sum_congr rfl (fun i hi => hterm i (Finset.mem_range.1 hi))
  rw [this, Finset.sum_sub_distrib] at habel
  linarith


/-- extension of a `Fin n` vector to `ℕ` -/
noncomputable def fe {n : ℕ} (f : Fin n → ℝ) (m : ℕ) : ℝ := if h : m < n then f ⟨m, h⟩ else 0

lemma fe_val {n : ℕ} (f : Fin n → ℝ) (i : Fin n) : fe f i.val = f i := by
  simp [fe, i.isLt]

lemma sum_fin_prefix {n : ℕ} (f : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), f i = ∑ m ∈ Finset.range k, fe f m := by
  rw [Finset.sum_filter]
  have h1 : ∀ i : Fin n, (if i.val < k then f i else 0) = (fun m => if m < k then fe f m else 0) i.val := by
    intro i; simp [fe_val]
  rw [Finset.sum_congr rfl (fun i _ => h1 i)]
  rw [Fin.sum_univ_eq_sum_range (fun m => if m < k then fe f m else 0) n, ← Finset.sum_filter]
  congr 1
  ext m; simp; omega

lemma sum_fin_total {n : ℕ} (f : Fin n → ℝ) : ∑ i, f i = ∑ m ∈ Finset.range n, fe f m := by
  have := sum_fin_prefix f n le_rfl
  simpa using this

lemma karamata_fin {n : ℕ} {s : Set ℝ} {g : ℝ → ℝ} (hg : ConvexOn ℝ s g) (x y : Fin n → ℝ)
    (hxs : ∀ i, x i ∈ s) (hys : ∀ i, y i ∈ s) (hxa : Antitone x) (hya : Antitone y)
    (hpart : ∀ k ≤ n, ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), x i ≤
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), y i)
    (htot : ∑ i, x i = ∑ i, y i) :
    ∑ i, g (x i) ≤ ∑ i, g (y i) := by
  have hg1 : ∀ (f : Fin n → ℝ), ∑ i, g (f i) = ∑ m ∈ Finset.range n, g (fe f m) := by
    intro f
    rw [← Fin.sum_univ_eq_sum_range (fun m => g (fe f m)) n]
    simp [fe_val]
  rw [hg1 x, hg1 y]
  apply karamata_nat hg n (fe x) (fe y)
  · intro i hi; have := fe_val x ⟨i, hi⟩; simp only at this; rw [this]; exact hxs _
  · intro i hi; have := fe_val y ⟨i, hi⟩; simp only at this; rw [this]; exact hys _
  · intro i j hij hj
    have h1 := fe_val x ⟨i, by omega⟩
    have h2 := fe_val x ⟨j, hj⟩
    simp only at h1 h2
    rw [h1, h2]; exact hxa (Fin.mk_le_mk.2 hij)
  · intro i j hij hj
    have h1 := fe_val y ⟨i, by omega⟩
    have h2 := fe_val y ⟨j, hj⟩
    simp only at h1 h2
    rw [h1, h2]; exact hya (Fin.mk_le_mk.2 hij)
  · intro k hk
    rw [← sum_fin_prefix x k hk, ← sum_fin_prefix y k hk]; exact hpart k hk
  · rw [← sum_fin_total x, ← sum_fin_total y]; exact htot

lemma maj_sorted {n : ℕ} {v w : Fin n → ℝ} (hva : Antitone v) (hwa : Antitone w)
    (h : Majorized v w) :
    (∀ k ≤ n, ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), v i ≤
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), w i) ∧ ∑ i, v i = ∑ i, w i := by
  obtain ⟨σx, σy, hx, hy, htot, hpart⟩ := h
  have key : ∀ (u : Fin n → ℝ) (σ : Equiv.Perm (Fin n)), Antitone u → Antitone (u ∘ σ) →
      ∀ i, u (σ i) = u i := by
    intro u σ hu hσ i
    have := Tuple.unique_monotone (f := fun i => -u i) (σ := σ) (τ := 1)
      (fun a b hab => by simpa using hσ hab) (fun a b hab => by simpa using hu hab)
    have h2 := congrFun this i
    simpa using h2
  have e1 := key v σx hva hx
  have e2 := key w σy hwa hy
  simp only [e1, e2] at htot hpart
  refine ⟨?_, htot⟩
  intro k hk
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp
  rcases lt_or_eq_of_le hk with hlt | heq
  · exact hpart k hk0 hlt
  · have : Finset.univ.filter (fun i : Fin n => i.val < k) = Finset.univ := by
      ext i; simp; have := i.isLt; omega
    rw [this]; exact htot.le

theorem karamata_core {n : ℕ} {s : Set ℝ} {g : ℝ → ℝ} (hg : ConvexOn ℝ s g)
    (x y : Fin n → ℝ) (hxs : ∀ i, x i ∈ s) (hys : ∀ i, y i ∈ s) (hxy : Majorized x y) :
    ∑ i, g (x i) ≤ ∑ i, g (y i) := by
  obtain ⟨σx, σy, hx, hy, htot, hpart⟩ := hxy
  have h1 : ∑ i, g (x i) = ∑ i, g (x (σx i)) := (Equiv.sum_comp σx (fun i => g (x i))).symm
  have h2 : ∑ i, g (y i) = ∑ i, g (y (σy i)) := (Equiv.sum_comp σy (fun i => g (y i))).symm
  rw [h1, h2]
  apply karamata_fin hg (fun i => x (σx i)) (fun i => y (σy i)) (fun i => hxs _) (fun i => hys _) hx hy
  · intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp
    rcases lt_or_eq_of_le hk with hlt | heq
    · exact hpart k hk0 hlt
    · have : Finset.univ.filter (fun i : Fin n => i.val < k) = Finset.univ := by
        ext i; simp; have := i.isLt; omega
      rw [this]; exact htot.le
  · exact htot

end RetailVariety.Fashion

open RetailVariety.Fashion


theorem solution {n : ℕ} {s : Set ℝ} {g : ℝ → ℝ} (hg : ConvexOn ℝ s g)
    (x y : Fin n → ℝ) (hxs : ∀ i, x i ∈ s) (hys : ∀ i, y i ∈ s) (hxy : Majorized x y) :
    ∑ i, g (x i) ≤ ∑ i, g (y i) := by
  exact karamata_core hg x y hxs hys hxy
