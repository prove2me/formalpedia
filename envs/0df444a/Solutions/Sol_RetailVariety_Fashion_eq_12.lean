-- Prove2me | solution 1 for RetailVariety.Fashion.eq_12
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T03:47:36.595214+00:00
-- url     : https://prove2.me/submissions/30a24140-6bc7-4bd6-a013-80182e762f45

import Mathlib
import Definitions.Def_RetailVariety_Fashion_Model
import Definitions.Def_RetailVariety_Fashion_Majorization
import Definitions.Def_RetailVariety_Fashion_ProofObjects



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



lemma sum_A_eq_range {n k : ℕ} (hk : k ≤ n) (f : Fin n → ℝ) :
    ∑ j ∈ RetailVariety.Statics.A n k, f j = ∑ i ∈ Finset.range k, fe f i := by
  have h1 : ∑ j ∈ RetailVariety.Statics.A n k, f j
      = ∑ j : Fin n, if j.val < k then fe f j.val else 0 := by
    unfold RetailVariety.Statics.A RetailVariety.Structure.popularSet
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [fe_val]
  rw [h1, Fin.sum_univ_eq_sum_range (fun i => if i < k then fe f i else 0) n,
    ← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

lemma sum_fin_eq_range {r : ℕ} (f : Fin r → ℝ) :
    ∑ j : Fin r, f j = ∑ i ∈ Finset.range r, fe f i := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => fe f i) r]
  exact Finset.sum_congr rfl (fun j _ => (fe_val f j).symm)

lemma fe_castLE {n r : ℕ} (hr : r ≤ n) (v : Fin n → ℝ) {i : ℕ} (hi : i < r) :
    fe (fun j : Fin r => v (Fin.castLE hr j)) i = fe v i := by
  simp [fe, hi, lt_of_lt_of_le hi hr]

lemma fe_nonneg {n : ℕ} {f : Fin n → ℝ} (hf : ∀ j, 0 ≤ f j) (i : ℕ) : 0 ≤ fe f i := by
  unfold fe; split_ifs
  · exact hf _
  · exact le_rfl

lemma fe_wPrime {n : ℕ} (w : Fin n → ℝ) (r t : ℕ) (θ : ℝ) (hr : r ≤ n) {i : ℕ} (hi : i < r) :
    fe (wPrime w r t θ hr) i =
      if i < t then fe w i else if i = t then θ * fe w i else 0 := by
  have hin : i < n := lt_of_lt_of_le hi hr
  simp only [fe, wPrime, dif_pos hi, dif_pos hin, Fin.castLE]

lemma maj_prefix {n : ℕ} {v w : Fin n → ℝ} (hva : Antitone v) (hwa : Antitone w)
    (h : Majorized v w) {k : ℕ} (hk : k < n) :
    ∑ j ∈ RetailVariety.Statics.A n k, v j ≤ ∑ j ∈ RetailVariety.Statics.A n k, w j := by
  obtain ⟨σx, σy, hx, hy, _, hp⟩ := h
  have e1' : ∀ i, v (σx i) = v i := by
    have := Tuple.unique_monotone (f := fun i => OrderDual.toDual (v i)) (σ := σx) (τ := Equiv.refl _)
      (fun a b hab => hx hab) (fun a b hab => hva hab)
    intro i; simpa using congrFun this i
  have e2' : ∀ i, w (σy i) = w i := by
    have := Tuple.unique_monotone (f := fun i => OrderDual.toDual (w i)) (σ := σy) (τ := Equiv.refl _)
      (fun a b hab => hy hab) (fun a b hab => hwa hab)
    intro i; simpa using congrFun this i
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp [RetailVariety.Statics.A, RetailVariety.Structure.popularSet]
  have := hp k hk0 hk
  simp only [e1', e2'] at this
  exact this


lemma sum_wp_range {n : ℕ} (w : Fin n → ℝ) (r t : ℕ) (θ : ℝ) (hr : r ≤ n) (ht : t < r)
    {k : ℕ} (hkr : k ≤ r) :
    ∑ i ∈ Finset.range k, fe (wPrime w r t θ hr) i =
      if k ≤ t then ∑ i ∈ Finset.range k, fe w i
      else ∑ i ∈ Finset.range t, fe w i + θ * fe w t := by
  split_ifs with hkt
  · refine Finset.sum_congr rfl (fun i hi => ?_)
    have hi' : i < k := Finset.mem_range.mp hi
    rw [fe_wPrime w r t θ hr (by omega), if_pos (by omega)]
  · have h1 : t + 1 ≤ k := by omega
    rw [← Finset.sum_range_add_sum_Ico _ h1]
    have h2 : ∑ i ∈ Finset.Ico (t + 1) k, fe (wPrime w r t θ hr) i = 0 := by
      refine Finset.sum_eq_zero (fun i hi => ?_)
      have hi' := Finset.mem_Ico.mp hi
      rw [fe_wPrime w r t θ hr (by omega), if_neg (by omega), if_neg (by omega)]
    rw [h2, add_zero, Finset.sum_range_succ]
    congr 1
    · refine Finset.sum_congr rfl (fun i hi => ?_)
      have hi' : i < t := Finset.mem_range.mp hi
      rw [fe_wPrime w r t θ hr (by omega), if_pos hi']
    · rw [fe_wPrime w r t θ hr ht, if_neg (lt_irrefl _), if_pos rfl]



lemma sum_fe_castLE {n r : ℕ} (hr : r ≤ n) (v : Fin n → ℝ) {k : ℕ} (hk : k ≤ r) :
    ∑ m ∈ Finset.range k, fe (fun j : Fin r => v (Fin.castLE hr j)) m = ∑ m ∈ Finset.range k, fe v m :=
  Finset.sum_congr rfl (fun m hm => fe_castLE hr v (by have := Finset.mem_range.1 hm; omega))

lemma wp_total {n : ℕ} (v w : Fin n → ℝ) (r : ℕ) (hr : r ≤ n)
    (t : ℕ) (ht : t < r) (θ : ℝ)
    (heq : ∑ j ∈ RetailVariety.Statics.A n t, w j + θ * w ⟨t, by omega⟩
        = ∑ j ∈ RetailVariety.Statics.A n r, v j) :
    ∑ j : Fin r, wPrime w r t θ hr j = ∑ j : Fin r, v (Fin.castLE hr j) := by
  have hw_t : fe w t = w ⟨t, by omega⟩ := by
    simp [fe, show t < n by omega]
  rw [sum_fin_eq_range, sum_wp_range w r t θ hr ht le_rfl, if_neg (by omega),
    sum_fin_eq_range (fun j : Fin r => v (Fin.castLE hr j)), sum_fe_castLE hr v le_rfl,
    ← sum_A_eq_range hr v, ← heq, sum_A_eq_range (by omega : t ≤ n), hw_t]

lemma wPrime_antitone {n : ℕ} (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j) (hwa : Antitone w)
    (r t : ℕ) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hr : r ≤ n) :
    Antitone (wPrime w r t θ hr) := by
  have hcle : ∀ a b : Fin r, a ≤ b → Fin.castLE hr a ≤ Fin.castLE hr b := fun a b hab => hab
  intro a b hab
  have hab' : a.val ≤ b.val := hab
  unfold wPrime
  by_cases hb1 : b.val < t
  · have ha1 : a.val < t := by omega
    rw [if_pos hb1, if_pos ha1]
    exact hwa (hcle a b hab)
  · by_cases hb2 : b.val = t
    · by_cases ha1 : a.val < t
      · rw [if_neg hb1, if_pos hb2, if_pos ha1]
        have h1 : w (Fin.castLE hr b) ≤ w (Fin.castLE hr a) := hwa (hcle a b hab)
        have h2 : 0 ≤ w (Fin.castLE hr b) := hw _
        nlinarith
      · have ha2 : a.val = t := by omega
        have : a = b := Fin.ext (by omega)
        subst this
        exact le_rfl
    · by_cases ha1 : a.val < t
      · rw [if_neg hb1, if_neg hb2, if_pos ha1]; exact hw _
      · by_cases ha2 : a.val = t
        · rw [if_neg hb1, if_neg hb2, if_neg ha1, if_pos ha2]
          exact mul_nonneg hθ0.le (hw _)
        · rw [if_neg hb1, if_neg hb2, if_neg ha1, if_neg ha2]

lemma maj_vr_wp {n : ℕ} (v w : Fin n → ℝ) (hv : ∀ j, 0 ≤ v j) (hw : ∀ j, 0 ≤ w j)
    (hva : Antitone v) (hwa : Antitone w) (hvw : Majorized v w) (r : ℕ) (hr : r ≤ n)
    (t : ℕ) (ht : t < r) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (heq : ∑ j ∈ RetailVariety.Statics.A n t, w j + θ * w ⟨t, by omega⟩
        = ∑ j ∈ RetailVariety.Statics.A n r, v j) :
    Majorized (fun j : Fin r => v (Fin.castLE hr j)) (wPrime w r t θ hr) := by
  have hcle : ∀ a b : Fin r, a ≤ b → Fin.castLE hr a ≤ Fin.castLE hr b := fun a b hab => hab
  have hw_t : fe w t = w ⟨t, by omega⟩ := by
    simp [fe, show t < n by omega]
  have hAv : ∑ j ∈ RetailVariety.Statics.A n r, v j = ∑ i ∈ Finset.range r, fe v i :=
    sum_A_eq_range hr v
  have htot := wp_total v w r hr t ht θ heq
  refine ⟨Equiv.refl _, Equiv.refl _, ?_, wPrime_antitone w hw hwa r t θ hθ0 hθ1 hr, ?_, ?_⟩
  · intro a b hab
    simp only [Equiv.coe_refl, Function.comp_id]
    exact hva (hcle a b hab)
  · simp only [Equiv.coe_refl, Equiv.refl_apply, Function.comp_id]
    exact htot.symm
  · intro k hk1 hkr
    simp only [Equiv.coe_refl, Equiv.refl_apply, Function.comp_id]
    rw [sum_fin_prefix _ k hkr.le, sum_fin_prefix _ k hkr.le, sum_fe_castLE hr v hkr.le,
      sum_wp_range w r t θ hr ht hkr.le]
    split_ifs with hkt
    · rw [← sum_A_eq_range (by omega : k ≤ n) v, ← sum_A_eq_range (by omega : k ≤ n) w]
      exact maj_prefix hva hwa hvw (by omega)
    · have h1 : ∑ i ∈ Finset.range k, fe v i ≤ ∑ i ∈ Finset.range r, fe v i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hkr.le)
          (fun i _ _ => fe_nonneg hv i)
      rw [← hAv, ← heq, sum_A_eq_range (by omega : t ≤ n)] at h1
      rw [hw_t]
      exact h1


lemma safetyCoeff_nonneg (p c lam σ β : ℝ) (hc : 0 < c) (hcp : c < p) (hlam : 0 < lam)
    (hσ : 0 < σ) : 0 ≤ safetyCoeff p c lam σ β := by
  have hp : 0 < p := by linarith
  unfold safetyCoeff
  positivity

lemma wPrime_nonneg {n : ℕ} (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j) (r t : ℕ) (θ : ℝ)
    (hθ0 : 0 < θ) (hr : r ≤ n) (j : Fin r) : 0 ≤ wPrime w r t θ hr j := by
  unfold wPrime
  split_ifs
  · exact hw _
  · exact mul_nonneg hθ0.le (hw _)
  · exact le_rfl

lemma gFun_convex' (p c lam σ β L : ℝ) (hc : 0 < c) (hcp : c < p) (hlam : 0 < lam)
    (hσ : 0 < σ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hL : 0 < L) :
    ConvexOn ℝ (Set.Ici 0) (gFun p c lam σ β L) := by
  have hK : 0 ≤ safetyCoeff p c lam σ β / L ^ β :=
    div_nonneg (safetyCoeff_nonneg p c lam σ β hc hcp hlam hσ) (Real.rpow_nonneg hL.le _)
  have ha : 0 ≤ (p - c) * lam / L := by
    have : 0 < p - c := by linarith
    positivity
  have h1 := (convexOn_id (convex_Ici (0:ℝ))).smul ha
  have h2 := ((Real.concaveOn_rpow hβ0 hβ1.le).neg).smul hK
  refine (h1.add h2).congr ?_
  intro x _
  simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, id, gFun]
  ring

lemma convex_max_affine (a b : ℝ) : ConvexOn ℝ Set.univ (fun x : ℝ => max (a * x + b) 0) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ s t hs ht hst
  simp only [smul_eq_mul]
  have e : a * (s * x + t * y) + b = s * (a * x + b) + t * (a * y + b) := by
    have : b = (s + t) * b := by rw [hst]; ring
    nlinarith [this]
  rw [e]
  refine max_le ?_ ?_
  · nlinarith [le_max_left (a * x + b) 0, le_max_left (a * y + b) 0]
  · have := le_max_right (a * x + b) 0
    have := le_max_right (a * y + b) 0
    nlinarith [mul_nonneg hs (le_max_right (a * x + b) 0), mul_nonneg ht (le_max_right (a * y + b) 0)]

lemma gFunT_convex' (p c lam L : ℝ) (hlam : 0 < lam) (hL : 0 < L) :
    ConvexOn ℝ (Set.Ici 0) (gFunT p c lam L) := by
  have h := (convex_max_affine p (-(c * L))).smul (le_of_lt (div_pos hlam hL))
  refine (h.subset (Set.subset_univ _) (convex_Ici 0)).congr ?_
  intro x _
  simp only [Pi.smul_apply, smul_eq_mul, gFunT]
  congr 2

lemma profitI_eq {n : ℕ} (p c lam σ β v0 : ℝ) (v : Fin n → ℝ) (hv : ∀ j, 0 ≤ v j)
    (S : Finset (Fin n)) (hL : 0 < ∑ j ∈ S, v j + v0) :
    profitI p c lam σ β v v0 S = ∑ j ∈ S, gFun p c lam σ β (∑ j ∈ S, v j + v0) (v j) := by
  unfold profitI gFun RetailVariety.Structure.share
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Real.div_rpow (hv j) hL.le]
  ring

lemma profitT_eq {n : ℕ} (p c lam v0 : ℝ) (v : Fin n → ℝ)
    (S : Finset (Fin n)) (hL : 0 < ∑ j ∈ S, v j + v0) :
    profitT p c lam v v0 S = ∑ j ∈ S, gFunT p c lam (∑ j ∈ S, v j + v0) (v j) := by
  unfold profitT gFunT RetailVariety.Structure.share
  refine Finset.sum_congr rfl (fun j _ => ?_)
  set L := ∑ j ∈ S, v j + v0
  have h1 : p * (v j / L) - c = (p * v j - c * L) / L := by field_simp
  have h2 := max_div_div_right (a := p * v j - c * L) (b := 0) hL.le
  rw [zero_div] at h2
  rw [h1, h2]
  field_simp

lemma sumFin_eq_sumA {n r : ℕ} (hr : r ≤ n) (F : Fin n → ℝ) :
    ∑ j : Fin r, F (Fin.castLE hr j) = ∑ j ∈ RetailVariety.Statics.A n r, F j := by
  rw [sum_fin_eq_range (fun j : Fin r => F (Fin.castLE hr j)), sum_fe_castLE hr F le_rfl,
    sum_A_eq_range hr F]

theorem eq12_core {n : ℕ} (p c lam σ β v0 : ℝ) (hc : 0 < c) (hcp : c < p) (hlam : 0 < lam)
    (hσ : 0 < σ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hv0 : 0 < v0)
    (v w : Fin n → ℝ) (hv : ∀ j, 0 ≤ v j) (hw : ∀ j, 0 ≤ w j)
    (hva : Antitone v) (hwa : Antitone w) (hvw : Majorized v w) (r : ℕ) (hr : r ≤ n)
    (t : ℕ) (ht : t < r) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (heq : ∑ j ∈ RetailVariety.Statics.A n t, w j + θ * w ⟨t, by omega⟩ = ∑ j ∈ RetailVariety.Statics.A n r, v j)
    (L : ℝ) (hL : L = ∑ j ∈ RetailVariety.Statics.A n r, v j + v0) :
    ∑ j : Fin r, gFun p c lam σ β L (v (Fin.castLE hr j)) ≤
        ∑ j : Fin r, gFun p c lam σ β L (wPrime w r t θ hr j) ∧
      ∑ j : Fin r, gFunT p c lam L (v (Fin.castLE hr j)) ≤
        ∑ j : Fin r, gFunT p c lam L (wPrime w r t θ hr j) := by
  have hLpos : 0 < L := by
    rw [hL]
    have : 0 ≤ ∑ j ∈ RetailVariety.Statics.A n r, v j := Finset.sum_nonneg (fun j _ => hv j)
    linarith
  have hmaj := maj_vr_wp v w hv hw hva hwa hvw r hr t ht θ hθ0 hθ1 heq
  have hxs : ∀ j : Fin r, v (Fin.castLE hr j) ∈ Set.Ici (0:ℝ) := fun j => hv _
  have hys : ∀ j : Fin r, wPrime w r t θ hr j ∈ Set.Ici (0:ℝ) :=
    fun j => wPrime_nonneg w hw r t θ hθ0 hr j
  exact ⟨karamata_core (gFun_convex' p c lam σ β L hc hcp hlam hσ hβ0 hβ1 hLpos) _ _ hxs hys hmaj,
    karamata_core (gFunT_convex' p c lam L hlam hLpos) _ _ hxs hys hmaj⟩

end RetailVariety.Fashion

open RetailVariety.Fashion


theorem solution {n : ℕ} (p c lam σ β v0 : ℝ) (hc : 0 < c) (hcp : c < p) (hlam : 0 < lam)
    (hσ : 0 < σ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hv0 : 0 < v0)
    (v w : Fin n → ℝ) (hv : ∀ j, 0 ≤ v j) (hw : ∀ j, 0 ≤ w j)
    (hva : Antitone v) (hwa : Antitone w) (hvw : Majorized v w) (r : ℕ) (hr : r ≤ n)
    (t : ℕ) (ht : t < r) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (heq : ∑ j ∈ RetailVariety.Statics.A n t, w j + θ * w ⟨t, by omega⟩ = ∑ j ∈ RetailVariety.Statics.A n r, v j)
    (L : ℝ) (hL : L = ∑ j ∈ RetailVariety.Statics.A n r, v j + v0) :
    ∑ j : Fin r, gFun p c lam σ β L (v (Fin.castLE hr j)) ≤
        ∑ j : Fin r, gFun p c lam σ β L (wPrime w r t θ hr j) ∧
      ∑ j : Fin r, gFunT p c lam L (v (Fin.castLE hr j)) ≤
        ∑ j : Fin r, gFunT p c lam L (wPrime w r t θ hr j) := by
  exact eq12_core p c lam σ β v0 hc hcp hlam hσ hβ0 hβ1 hv0 v w hv hw hva hwa hvw r hr t ht θ hθ0 hθ1 heq L hL
