-- Prove2me | solution 1 for RetailVariety.Fashion.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T03:53:08.793173+00:00
-- url     : https://prove2.me/submissions/0a397713-1f11-41fc-b274-9e3ae461f3cf

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



lemma key_ineq {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {x u A B : ℝ} (hx : 0 ≤ x) (hu : 0 ≤ u)
    (hA : 0 < A) (hB : 0 < B) :
    x ^ β * u ^ (1 - β) ≤ A ^ β * B ^ (1 - β) * (β * (x / A) + (1 - β) * (u / B)) := by
  have h := Real.geom_mean_le_arith_mean2_weighted (w₁ := β) (w₂ := 1 - β) hβ0.le
    (by linarith) (div_nonneg hx hA.le) (div_nonneg hu hB.le) (by ring)
  rw [Real.div_rpow hx hA.le, Real.div_rpow hu hB.le] at h
  have hA' : 0 < A ^ β := Real.rpow_pos_of_pos hA _
  have hB' : 0 < B ^ (1 - β) := Real.rpow_pos_of_pos hB _
  calc x ^ β * u ^ (1 - β)
      = A ^ β * B ^ (1 - β) * (x ^ β / A ^ β * (u ^ (1 - β) / B ^ (1 - β))) := by
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)

lemma geo_comb {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {a b px py qx qy : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) (hpx : 0 ≤ px) (hpy : 0 ≤ py) (hqx : 0 ≤ qx) (hqy : 0 ≤ qy) :
    a * (px ^ β * qx ^ (1 - β)) + b * (py ^ β * qy ^ (1 - β))
      ≤ (a * px + b * py) ^ β * (a * qx + b * qy) ^ (1 - β) := by
  set A := a * px + b * py with hAdef
  set B := a * qx + b * qy with hBdef
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  have hRHS : 0 ≤ A ^ β * B ^ (1 - β) :=
    mul_nonneg (Real.rpow_nonneg hA0 _) (Real.rpow_nonneg hB0 _)
  rcases hA0.eq_or_lt with hA | hA
  · -- A = 0
    have h1 : a * px = 0 := by
      have : 0 ≤ a * px := mul_nonneg ha hpx
      have : 0 ≤ b * py := mul_nonneg hb hpy
      linarith
    have h2 : b * py = 0 := by
      have : 0 ≤ a * px := mul_nonneg ha hpx
      have : 0 ≤ b * py := mul_nonneg hb hpy
      linarith
    have e1 : a * (px ^ β * qx ^ (1 - β)) = 0 := by
      rcases mul_eq_zero.1 h1 with h | h
      · rw [h]; ring
      · rw [h, Real.zero_rpow hβ0.ne']; ring
    have e2 : b * (py ^ β * qy ^ (1 - β)) = 0 := by
      rcases mul_eq_zero.1 h2 with h | h
      · rw [h]; ring
      · rw [h, Real.zero_rpow hβ0.ne']; ring
    rw [e1, e2]; simpa using hRHS
  rcases hB0.eq_or_lt with hB | hB
  · have h1 : a * qx = 0 := by
      have : 0 ≤ a * qx := mul_nonneg ha hqx
      have : 0 ≤ b * qy := mul_nonneg hb hqy
      linarith
    have h2 : b * qy = 0 := by
      have : 0 ≤ a * qx := mul_nonneg ha hqx
      have : 0 ≤ b * qy := mul_nonneg hb hqy
      linarith
    have hne : (1 - β) ≠ 0 := by linarith
    have e1 : a * (px ^ β * qx ^ (1 - β)) = 0 := by
      rcases mul_eq_zero.1 h1 with h | h
      · rw [h]; ring
      · rw [h, Real.zero_rpow hne]; ring
    have e2 : b * (py ^ β * qy ^ (1 - β)) = 0 := by
      rcases mul_eq_zero.1 h2 with h | h
      · rw [h]; ring
      · rw [h, Real.zero_rpow hne]; ring
    rw [e1, e2]; simpa using hRHS
  have k1 := key_ineq hβ0 hβ1 hpx hqx hA hB
  have k2 := key_ineq hβ0 hβ1 hpy hqy hA hB
  have hAB : 0 ≤ A ^ β * B ^ (1 - β) := hRHS
  have hsum : a * (β * (px / A) + (1 - β) * (qx / B)) + b * (β * (py / A) + (1 - β) * (qy / B)) = 1 := by
    have e : a * (β * (px / A) + (1 - β) * (qx / B)) + b * (β * (py / A) + (1 - β) * (qy / B))
        = β * ((a * px + b * py) / A) + (1 - β) * ((a * qx + b * qy) / B) := by ring
    rw [e, ← hAdef, ← hBdef, div_self hA.ne', div_self hB.ne']; ring
  calc a * (px ^ β * qx ^ (1 - β)) + b * (py ^ β * qy ^ (1 - β))
      ≤ a * (A ^ β * B ^ (1 - β) * (β * (px / A) + (1 - β) * (qx / B)))
        + b * (A ^ β * B ^ (1 - β) * (β * (py / A) + (1 - β) * (qy / B))) := by
        gcongr
    _ = A ^ β * B ^ (1 - β) * (a * (β * (px / A) + (1 - β) * (qx / B))
          + b * (β * (py / A) + (1 - β) * (qy / B))) := by ring
    _ = A ^ β * B ^ (1 - β) := by rw [hsum]; ring

lemma R_concave {β U M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hU : 0 ≤ U) (hM : 0 ≤ M) :
    ConcaveOn ℝ (Set.Ici 0) (fun δ : ℝ => (U + δ ^ β) * (M + δ) ^ (1 - β)) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy a b ha hb hab
  have hx' : (0:ℝ) ≤ x := hx
  have hy' : (0:ℝ) ≤ y := hy
  simp only [smul_eq_mul]
  rcases hβ0.eq_or_lt with h0 | hpos
  · subst h0
    simp only [Real.rpow_zero, sub_zero, Real.rpow_one]
    have : b = 1 - a := by linarith
    subst this
    apply le_of_eq
    ring
  · have h1 := geo_comb hpos hβ1 ha hb hab hx' hy' (by linarith : 0 ≤ M + x) (by linarith : 0 ≤ M + y)
    have h2 := geo_comb hpos hβ1 ha hb hab (zero_le_one : (0:ℝ) ≤ 1) (zero_le_one : (0:ℝ) ≤ 1)
      (by linarith : 0 ≤ M + x) (by linarith : 0 ≤ M + y)
    have e : a * (M + x) + b * (M + y) = M + (a * x + b * y) := by
      have : b = 1 - a := by linarith
      subst this; ring
    have e2 : a * 1 + b * 1 = 1 := by linarith
    rw [e] at h1 h2
    rw [e2, Real.one_rpow] at h2
    have h3 := mul_le_mul_of_nonneg_left h2 hU
    nlinarith [h1, h3]

lemma NI_convex {β U M T K a : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hU : 0 ≤ U) (hM : 0 ≤ M)
    (hK : 0 ≤ K) :
    ConvexOn ℝ (Set.Ici 0)
      (fun δ : ℝ => a * (T + δ) - K * ((U + δ ^ β) * (M + δ) ^ (1 - β))) := by
  have hR := R_concave (β := β) hβ0 hβ1 hU hM
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy s t hs ht hst
  have := hR.2 hx hy hs ht hst
  simp only [smul_eq_mul] at this ⊢
  have e : a * (T + (s * x + t * y)) = s * (a * (T + x)) + t * (a * (T + y)) := by
    have : t = 1 - s := by linarith
    subst this; ring
  have h3 := mul_le_mul_of_nonneg_left this hK
  nlinarith [h3, e]

lemma quasi_ratio {N : ℝ → ℝ} (hN : ConvexOn ℝ (Set.Ici 0) N) {M : ℝ} (hM : 0 < M) {x : ℝ}
    (hx : 0 ≤ x) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδx : δ ≤ x) :
    N δ / (M + δ) ≤ max (N 0 / (M + 0)) (N x / (M + x)) := by
  set α := max (N 0 / (M + 0)) (N x / (M + x)) with hα
  have h0 : N 0 ≤ α * (M + 0) := by
    have : N 0 / (M + 0) ≤ α := le_max_left _ _
    rwa [div_le_iff₀ (by linarith)] at this
  have h1 : N x ≤ α * (M + x) := by
    have : N x / (M + x) ≤ α := le_max_right _ _
    rwa [div_le_iff₀ (by linarith)] at this
  rw [div_le_iff₀ (by linarith)]
  rcases hx.eq_or_lt with hx0 | hxpos
  · have : δ = 0 := by linarith
    subst this; subst hx0
    simpa using h0
  · set t := δ / x with ht
    have ht0 : 0 ≤ t := div_nonneg hδ0 hx
    have ht1 : t ≤ 1 := by rw [ht, div_le_one hxpos]; exact hδx
    have hs : 0 ≤ 1 - t := by linarith
    have hδ : δ = (1 - t) * 0 + t * x := by rw [ht]; field_simp; ring
    have hc := hN.2 (Set.mem_Ici.2 (le_refl (0:ℝ))) (Set.mem_Ici.2 hx) hs ht0 (by ring)
    simp only [smul_eq_mul] at hc
    rw [← hδ] at hc
    have hM' : α * (M + δ) = (1 - t) * (α * (M + 0)) + t * (α * (M + x)) := by
      rw [hδ]; ring
    rw [hM']
    nlinarith [mul_le_mul_of_nonneg_left h0 hs, mul_le_mul_of_nonneg_left h1 ht0]


lemma gFun_zero_nonpos (p c lam σ β L : ℝ) (hc : 0 < c) (hcp : c < p) (hlam : 0 < lam)
    (hσ : 0 < σ) (hL : 0 < L) : gFun p c lam σ β L 0 ≤ 0 := by
  unfold gFun
  have hK : 0 ≤ safetyCoeff p c lam σ β / L ^ β :=
    div_nonneg (safetyCoeff_nonneg p c lam σ β hc hcp hlam hσ) (Real.rpow_nonneg hL.le _)
  have h0 : 0 ≤ (0:ℝ) ^ β := Real.rpow_nonneg le_rfl _
  have := mul_nonneg hK h0
  nlinarith

lemma gFunT_zero (p c lam L : ℝ) (hc : 0 < c) (hL : 0 < L) : gFunT p c lam L 0 = 0 := by
  unfold gFunT
  have : max (p * 0 - c * L) 0 = 0 := max_eq_right (by nlinarith)
  rw [this]; ring

lemma sum_A_succ {n t : ℕ} (ht : t < n) (F : Fin n → ℝ) :
    ∑ j ∈ RetailVariety.Statics.A n (t + 1), F j =
      ∑ j ∈ RetailVariety.Statics.A n t, F j + F ⟨t, ht⟩ := by
  rw [sum_A_eq_range (by omega : t + 1 ≤ n), sum_A_eq_range (by omega : t ≤ n),
    Finset.sum_range_succ]
  congr 1
  simp [fe, ht]

lemma sum_A_comp {n t : ℕ} (ht : t ≤ n) (G : ℝ → ℝ) (w : Fin n → ℝ) :
    ∑ j ∈ RetailVariety.Statics.A n t, G (w j) = ∑ i ∈ Finset.range t, G (fe w i) := by
  rw [sum_A_eq_range ht (fun j => G (w j))]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have : i < n := by have := Finset.mem_range.1 hi; omega
  simp [fe, this]

lemma sum_gwp_le (G : ℝ → ℝ) (hG0 : G 0 ≤ 0) {n : ℕ} (w : Fin n → ℝ) (r t : ℕ) (θ : ℝ)
    (hr : r ≤ n) (ht : t < r) :
    ∑ j : Fin r, G (wPrime w r t θ hr j) ≤
      ∑ j ∈ RetailVariety.Statics.A n t, G (w j) + G (θ * w ⟨t, by omega⟩) := by
  have hw_t : fe w t = w ⟨t, by omega⟩ := by simp [fe, show t < n by omega]
  rw [sum_fin_eq_range (fun j : Fin r => G (wPrime w r t θ hr j)),
    sum_A_comp (by omega : t ≤ n)]
  have hterm : ∀ i ∈ Finset.range r, fe (fun j : Fin r => G (wPrime w r t θ hr j)) i =
      (if i < t then G (fe w i) else if i = t then G (θ * fe w i) else G 0) := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    have h1 : fe (fun j : Fin r => G (wPrime w r t θ hr j)) i = G (fe (wPrime w r t θ hr) i) := by
      simp [fe, hi']
    rw [h1, fe_wPrime w r t θ hr hi']
    split_ifs <;> rfl
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_range_add_sum_Ico _ (by omega : t + 1 ≤ r),
    Finset.sum_range_succ]
  have e1 : ∑ i ∈ Finset.range t, (if i < t then G (fe w i) else if i = t then G (θ * fe w i) else G 0)
      = ∑ i ∈ Finset.range t, G (fe w i) := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [if_pos (Finset.mem_range.1 hi)]
  have e2 : (if t < t then G (fe w t) else if t = t then G (θ * fe w t) else G 0) = G (θ * fe w t) := by
    simp
  have e3 : ∑ i ∈ Finset.Ico (t + 1) r, (if i < t then G (fe w i) else if i = t then G (θ * fe w i) else G 0) ≤ 0 := by
    refine Finset.sum_nonpos (fun i hi => ?_)
    have := Finset.mem_Ico.1 hi
    rw [if_neg (by omega), if_neg (by omega)]
    exact hG0
  rw [e1, e2, hw_t] at *
  linarith

/-- the `Φ_I` function -/
noncomputable def PhiI (p c lam σ β : ℝ) {n : ℕ} (w : Fin n → ℝ) (S : Finset (Fin n)) (M δ : ℝ) : ℝ :=
  ∑ j ∈ S, gFun p c lam σ β (M + δ) (w j) + gFun p c lam σ β (M + δ) δ

noncomputable def PhiT (p c lam : ℝ) {n : ℕ} (w : Fin n → ℝ) (S : Finset (Fin n)) (M δ : ℝ) : ℝ :=
  ∑ j ∈ S, gFunT p c lam (M + δ) (w j) + gFunT p c lam (M + δ) δ

lemma PhiI_eq (p c lam σ β : ℝ) {n : ℕ} (w : Fin n → ℝ) (S : Finset (Fin n)) (M δ : ℝ)
    (hL : 0 < M + δ) :
    PhiI p c lam σ β w S M δ =
      ((p - c) * lam * ((∑ j ∈ S, w j) + δ) - safetyCoeff p c lam σ β *
        (((∑ j ∈ S, w j ^ β) + δ ^ β) * (M + δ) ^ (1 - β))) / (M + δ) := by
  unfold PhiI gFun
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h : (M + δ) ^ (1 - β) = (M + δ) / (M + δ) ^ β := by
    rw [Real.rpow_sub hL, Real.rpow_one]
  have hp : 0 < (M + δ) ^ β := Real.rpow_pos_of_pos hL _
  rw [h]
  field_simp
  ring

lemma PhiT_eq (p c lam : ℝ) {n : ℕ} (w : Fin n → ℝ) (S : Finset (Fin n)) (M δ : ℝ)
    (hL : 0 < M + δ) :
    PhiT p c lam w S M δ =
      (lam * (∑ j ∈ S, max (p * w j - c * (M + δ)) 0 + max (p * δ - c * (M + δ)) 0)) / (M + δ) := by
  unfold PhiT gFunT
  rw [← Finset.mul_sum]
  field_simp

lemma max_aff_ineq (A B x y s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) :
    max (A * (s * x + t * y) + B) 0 ≤ s * max (A * x + B) 0 + t * max (A * y + B) 0 := by
  have := (convex_max_affine A B).2 (Set.mem_univ x) (Set.mem_univ y) hs ht hst
  simpa [smul_eq_mul] using this

lemma NT_convex (p c lam M : ℝ) {n : ℕ} (w : Fin n → ℝ) (S : Finset (Fin n)) (hlam : 0 ≤ lam) :
    ConvexOn ℝ (Set.Ici 0)
      (fun δ : ℝ => lam * (∑ j ∈ S, max (p * w j - c * (M + δ)) 0 + max (p * δ - c * (M + δ)) 0)) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x _ y _ s t hs ht hst
  simp only [smul_eq_mul]
  have hj : ∀ j ∈ S, max (p * w j - c * (M + (s * x + t * y))) 0 ≤
      s * max (p * w j - c * (M + x)) 0 + t * max (p * w j - c * (M + y)) 0 := by
    intro j _
    have := max_aff_ineq (-c) (p * w j - c * M) x y s t hs ht hst
    have e0 : p * w j - c * (M + (s * x + t * y)) = -c * (s * x + t * y) + (p * w j - c * M) := by ring
    have ex : p * w j - c * (M + x) = -c * x + (p * w j - c * M) := by ring
    have ey : p * w j - c * (M + y) = -c * y + (p * w j - c * M) := by ring
    rw [e0, ex, ey]; exact this
  have hsum := Finset.sum_le_sum hj
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hlast := max_aff_ineq (p - c) (-(c * M)) x y s t hs ht hst
  have e0 : p * (s * x + t * y) - c * (M + (s * x + t * y)) = (p - c) * (s * x + t * y) + -(c * M) := by ring
  have ex : p * x - c * (M + x) = (p - c) * x + -(c * M) := by ring
  have ey : p * y - c * (M + y) = (p - c) * y + -(c * M) := by ring
  rw [e0, ex, ey]
  have := mul_le_mul_of_nonneg_left (add_le_add hsum hlast) hlam
  nlinarith [this]

lemma phiI_bound (p c lam σ β : ℝ) (hc : 0 < c) (hcp : c < p) (hlam : 0 < lam)
    (hσ : 0 < σ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) {n : ℕ} (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j)
    (S : Finset (Fin n)) (v0 : ℝ) (hv0 : 0 < v0) {x : ℝ} (hx : 0 ≤ x) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδx : δ ≤ x) :
    PhiI p c lam σ β w S (∑ j ∈ S, w j + v0) δ ≤
      max (PhiI p c lam σ β w S (∑ j ∈ S, w j + v0) 0) (PhiI p c lam σ β w S (∑ j ∈ S, w j + v0) x) := by
  have hT : 0 ≤ ∑ j ∈ S, w j := Finset.sum_nonneg (fun j _ => hw j)
  set M := ∑ j ∈ S, w j + v0 with hM
  have hMpos : 0 < M := by linarith
  have hU : 0 ≤ ∑ j ∈ S, w j ^ β := Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (hw j) _)
  have hK := safetyCoeff_nonneg p c lam σ β hc hcp hlam hσ
  have hN := NI_convex (β := β) (U := ∑ j ∈ S, w j ^ β) (M := M) (T := ∑ j ∈ S, w j)
    (K := safetyCoeff p c lam σ β) (a := (p - c) * lam) hβ0 hβ1 hU hMpos.le hK
  have := quasi_ratio hN hMpos hx hδ0 hδx
  rw [PhiI_eq p c lam σ β w S M δ (by linarith), PhiI_eq p c lam σ β w S M 0 (by linarith),
    PhiI_eq p c lam σ β w S M x (by linarith)]
  exact this

lemma phiT_bound (p c lam : ℝ) (hlam : 0 < lam) {n : ℕ} (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j)
    (S : Finset (Fin n)) (v0 : ℝ) (hv0 : 0 < v0) {x : ℝ} (hx : 0 ≤ x) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδx : δ ≤ x) :
    PhiT p c lam w S (∑ j ∈ S, w j + v0) δ ≤
      max (PhiT p c lam w S (∑ j ∈ S, w j + v0) 0) (PhiT p c lam w S (∑ j ∈ S, w j + v0) x) := by
  have hT : 0 ≤ ∑ j ∈ S, w j := Finset.sum_nonneg (fun j _ => hw j)
  set M := ∑ j ∈ S, w j + v0 with hM
  have hMpos : 0 < M := by linarith
  have hN := NT_convex p c lam M w S hlam.le
  have := quasi_ratio hN hMpos hx hδ0 hδx
  rw [PhiT_eq p c lam w S M δ (by linarith), PhiT_eq p c lam w S M 0 (by linarith),
    PhiT_eq p c lam w S M x (by linarith)]
  exact this


lemma choice_t {n : ℕ} (v w : Fin n → ℝ) (hv : ∀ j, 0 ≤ v j) (hw : ∀ j, 0 ≤ w j)
    (hva : Antitone v) (hwa : Antitone w) (hvw : Majorized v w) (r : ℕ) (hr : r ≤ n)
    (hpos : 0 < ∑ j ∈ RetailVariety.Statics.A n r, v j) :
    ∃ t : ℕ, ∃ ht : t < r, ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧
      ∑ j ∈ RetailVariety.Statics.A n t, w j + θ * w ⟨t, by omega⟩ =
        ∑ j ∈ RetailVariety.Statics.A n r, v j := by
  obtain ⟨hpart, _⟩ := maj_sorted hva hwa hvw
  set V := ∑ j ∈ RetailVariety.Statics.A n r, v j with hV
  have hVr : V = ∑ i ∈ Finset.range r, fe v i := sum_A_eq_range hr v
  have hWr : V ≤ ∑ i ∈ Finset.range r, fe w i := by
    have := hpart r hr
    rw [sum_fin_prefix v r hr, sum_fin_prefix w r hr] at this
    rw [hVr]; exact this
  have hex : ∃ m, V ≤ ∑ i ∈ Finset.range m, fe w i := ⟨r, hWr⟩
  classical
  set m0 := Nat.find hex with hm0
  have hm0spec : V ≤ ∑ i ∈ Finset.range m0, fe w i := Nat.find_spec hex
  have hm0pos : m0 ≠ 0 := by
    intro h
    rw [h] at hm0spec
    simp at hm0spec
    linarith
  have hm0le : m0 ≤ r := Nat.find_min' hex hWr
  obtain ⟨t, ht⟩ : ∃ t, m0 = t + 1 := ⟨m0 - 1, by omega⟩
  have htr : t < r := by omega
  have hlt : ¬ V ≤ ∑ i ∈ Finset.range t, fe w i := Nat.find_min hex (by omega)
  push_neg at hlt
  rw [ht, Finset.sum_range_succ] at hm0spec
  have hwt_pos : 0 < fe w t := by linarith
  have hw_t : fe w t = w ⟨t, by omega⟩ := by simp [fe, show t < n by omega]
  refine ⟨t, htr, (V - ∑ i ∈ Finset.range t, fe w i) / fe w t, ?_, ?_, ?_⟩
  · exact div_pos (by linarith) hwt_pos
  · rw [div_le_one hwt_pos]; linarith
  · rw [← hw_t, sum_A_eq_range (by omega : t ≤ n)]
    field_simp
    ring

theorem theorem3_core {n : ℕ} (p c lam σ β v0 : ℝ) (hc : 0 < c) (hcp : c < p) (hlam : 0 < lam)
    (hσ : 0 < σ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hv0 : 0 < v0)
    (v w : Fin n → ℝ) (hv : ∀ j, 0 ≤ v j) (hw : ∀ j, 0 ≤ w j)
    (hva : Antitone v) (hwa : Antitone w) (r l : ℕ) (hr : r ≤ n) (hl : l ≤ n)
    (hvw : Majorized v w) :
    ((∀ S : Finset (Fin n), profitI p c lam σ β v v0 S ≤ profitI p c lam σ β v v0 (RetailVariety.Statics.A n r)) →
      (∀ S : Finset (Fin n), profitI p c lam σ β w v0 S ≤ profitI p c lam σ β w v0 (RetailVariety.Statics.A n l)) →
      profitI p c lam σ β v v0 (RetailVariety.Statics.A n r) ≤ profitI p c lam σ β w v0 (RetailVariety.Statics.A n l)) ∧
    ((∀ S : Finset (Fin n), profitT p c lam v v0 S ≤ profitT p c lam v v0 (RetailVariety.Statics.A n r)) →
      (∀ S : Finset (Fin n), profitT p c lam w v0 S ≤ profitT p c lam w v0 (RetailVariety.Statics.A n l)) →
      profitT p c lam v v0 (RetailVariety.Statics.A n r) ≤ profitT p c lam w v0 (RetailVariety.Statics.A n l)) := by
  have hVnn : 0 ≤ ∑ j ∈ RetailVariety.Statics.A n r, v j := Finset.sum_nonneg (fun j _ => hv j)
  have hLpos : 0 < ∑ j ∈ RetailVariety.Statics.A n r, v j + v0 := by linarith
  have hprofI_empty : profitI p c lam σ β w v0 ∅ = 0 := by simp [profitI]
  have hprofT_empty : profitT p c lam w v0 ∅ = 0 := by simp [profitT]
  by_cases hpos : 0 < ∑ j ∈ RetailVariety.Statics.A n r, v j
  · obtain ⟨t, ht, θ, hθ0, hθ1, heq⟩ := choice_t v w hv hw hva hwa hvw r hr hpos
    set L := ∑ j ∈ RetailVariety.Statics.A n r, v j + v0 with hL
    have hq := eq12_core p c lam σ β v0 hc hcp hlam hσ hβ0 hβ1 hv0 v w hv hw hva hwa hvw r hr t ht θ
      hθ0 hθ1 heq L hL
    have hwt : 0 ≤ w ⟨t, by omega⟩ := hw _
    have hT : 0 ≤ ∑ j ∈ RetailVariety.Statics.A n t, w j := Finset.sum_nonneg (fun j _ => hw j)
    have hLM : L = (∑ j ∈ RetailVariety.Statics.A n t, w j + v0) + θ * w ⟨t, by omega⟩ := by
      rw [hL, ← heq]; ring
    have hδ0 : 0 ≤ θ * w ⟨t, by omega⟩ := mul_nonneg hθ0.le hwt
    have hδx : θ * w ⟨t, by omega⟩ ≤ w ⟨t, by omega⟩ := by nlinarith
    have hMpos : 0 < ∑ j ∈ RetailVariety.Statics.A n t, w j + v0 := by linarith
    have hAt1 : 0 < ∑ j ∈ RetailVariety.Statics.A n (t + 1), w j + v0 := by
      have : 0 ≤ ∑ j ∈ RetailVariety.Statics.A n (t + 1), w j := Finset.sum_nonneg (fun j _ => hw j)
      linarith
    have hsucc : ∑ j ∈ RetailVariety.Statics.A n (t + 1), w j + v0 =
        (∑ j ∈ RetailVariety.Statics.A n t, w j + v0) + w ⟨t, by omega⟩ := by
      rw [sum_A_succ (by omega : t < n) w]; ring
    constructor
    · intro hoptv hoptw
      -- left: profit of A_r for v
      have h1 : profitI p c lam σ β v v0 (RetailVariety.Statics.A n r) =
          ∑ j : Fin r, gFun p c lam σ β L (v (Fin.castLE hr j)) := by
        rw [profitI_eq p c lam σ β v0 v hv _ hLpos]
        exact (sumFin_eq_sumA hr (fun j => gFun p c lam σ β L (v j))).symm
      have h2 := sum_gwp_le (gFun p c lam σ β L) (gFun_zero_nonpos p c lam σ β L hc hcp hlam hσ
        (by rw [hL]; exact hLpos)) w r t θ hr ht
      have h3 : ∑ j ∈ RetailVariety.Statics.A n t, gFun p c lam σ β L (w j) +
          gFun p c lam σ β L (θ * w ⟨t, by omega⟩) =
          PhiI p c lam σ β w (RetailVariety.Statics.A n t)
            (∑ j ∈ RetailVariety.Statics.A n t, w j + v0) (θ * w ⟨t, by omega⟩) := by
        unfold PhiI; rw [hLM]
      have h4 := phiI_bound p c lam σ β hc hcp hlam hσ hβ0 hβ1 w hw (RetailVariety.Statics.A n t) v0
        hv0 hwt hδ0 hδx
      have hP0 : PhiI p c lam σ β w (RetailVariety.Statics.A n t)
          (∑ j ∈ RetailVariety.Statics.A n t, w j + v0) 0 ≤
          profitI p c lam σ β w v0 (RetailVariety.Statics.A n l) := by
        calc _ ≤ profitI p c lam σ β w v0 (RetailVariety.Statics.A n t) := by
              rw [profitI_eq p c lam σ β v0 w hw _ hMpos]
              unfold PhiI
              have := gFun_zero_nonpos p c lam σ β (∑ j ∈ RetailVariety.Statics.A n t, w j + v0 + 0)
                hc hcp hlam hσ (by linarith)
              simp only [add_zero] at this ⊢
              linarith
          _ ≤ _ := hoptw _
      have hP1 : PhiI p c lam σ β w (RetailVariety.Statics.A n t)
          (∑ j ∈ RetailVariety.Statics.A n t, w j + v0) (w ⟨t, by omega⟩) ≤
          profitI p c lam σ β w v0 (RetailVariety.Statics.A n l) := by
        calc _ = profitI p c lam σ β w v0 (RetailVariety.Statics.A n (t + 1)) := by
              rw [profitI_eq p c lam σ β v0 w hw _ hAt1, sum_A_succ (by omega : t < n),
                hsucc]
              unfold PhiI
              rfl
          _ ≤ _ := hoptw _
      calc profitI p c lam σ β v v0 (RetailVariety.Statics.A n r)
          = ∑ j : Fin r, gFun p c lam σ β L (v (Fin.castLE hr j)) := h1
        _ ≤ ∑ j : Fin r, gFun p c lam σ β L (wPrime w r t θ hr j) := hq.1
        _ ≤ _ := h2
        _ = _ := h3
        _ ≤ _ := h4
        _ ≤ _ := max_le hP0 hP1
    · intro hoptv hoptw
      have h1 : profitT p c lam v v0 (RetailVariety.Statics.A n r) =
          ∑ j : Fin r, gFunT p c lam L (v (Fin.castLE hr j)) := by
        rw [profitT_eq p c lam v0 v _ hLpos]
        exact (sumFin_eq_sumA hr (fun j => gFunT p c lam L (v j))).symm
      have h2 := sum_gwp_le (gFunT p c lam L) (le_of_eq (gFunT_zero p c lam L hc
        (by rw [hL]; exact hLpos))) w r t θ hr ht
      have h3 : ∑ j ∈ RetailVariety.Statics.A n t, gFunT p c lam L (w j) +
          gFunT p c lam L (θ * w ⟨t, by omega⟩) =
          PhiT p c lam w (RetailVariety.Statics.A n t)
            (∑ j ∈ RetailVariety.Statics.A n t, w j + v0) (θ * w ⟨t, by omega⟩) := by
        unfold PhiT; rw [hLM]
      have h4 := phiT_bound p c lam hlam w hw (RetailVariety.Statics.A n t) v0
        hv0 hwt hδ0 hδx
      have hP0 : PhiT p c lam w (RetailVariety.Statics.A n t)
          (∑ j ∈ RetailVariety.Statics.A n t, w j + v0) 0 ≤
          profitT p c lam w v0 (RetailVariety.Statics.A n l) := by
        calc _ ≤ profitT p c lam w v0 (RetailVariety.Statics.A n t) := by
              rw [profitT_eq p c lam v0 w _ hMpos]
              unfold PhiT
              have := gFunT_zero p c lam (∑ j ∈ RetailVariety.Statics.A n t, w j + v0 + 0)
                hc (by linarith)
              simp only [add_zero] at this ⊢
              linarith
          _ ≤ _ := hoptw _
      have hP1 : PhiT p c lam w (RetailVariety.Statics.A n t)
          (∑ j ∈ RetailVariety.Statics.A n t, w j + v0) (w ⟨t, by omega⟩) ≤
          profitT p c lam w v0 (RetailVariety.Statics.A n l) := by
        calc _ = profitT p c lam w v0 (RetailVariety.Statics.A n (t + 1)) := by
              rw [profitT_eq p c lam v0 w _ hAt1, sum_A_succ (by omega : t < n),
                hsucc]
              unfold PhiT
              rfl
          _ ≤ _ := hoptw _
      calc profitT p c lam v v0 (RetailVariety.Statics.A n r)
          = ∑ j : Fin r, gFunT p c lam L (v (Fin.castLE hr j)) := h1
        _ ≤ ∑ j : Fin r, gFunT p c lam L (wPrime w r t θ hr j) := hq.2
        _ ≤ _ := h2
        _ = _ := h3
        _ ≤ _ := h4
        _ ≤ _ := max_le hP0 hP1
  · -- all v j = 0 on A_r
    have hz : ∑ j ∈ RetailVariety.Statics.A n r, v j = 0 := le_antisymm (not_lt.1 hpos) hVnn
    have hvz : ∀ j ∈ RetailVariety.Statics.A n r, v j = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hv j)).1 hz
    constructor
    · intro hoptv hoptw
      have : profitI p c lam σ β v v0 (RetailVariety.Statics.A n r) ≤ 0 := by
        rw [profitI_eq p c lam σ β v0 v hv _ hLpos]
        refine Finset.sum_nonpos (fun j hj => ?_)
        rw [hvz j hj]
        exact gFun_zero_nonpos p c lam σ β _ hc hcp hlam hσ hLpos
      have h2 := hoptw ∅
      rw [hprofI_empty] at h2
      linarith
    · intro hoptv hoptw
      have : profitT p c lam v v0 (RetailVariety.Statics.A n r) ≤ 0 := by
        rw [profitT_eq p c lam v0 v _ hLpos]
        refine Finset.sum_nonpos (fun j hj => ?_)
        rw [hvz j hj, gFunT_zero p c lam _ hc hLpos]
      have h2 := hoptw ∅
      rw [hprofT_empty] at h2
      linarith

end RetailVariety.Fashion

open RetailVariety.Fashion


theorem solution {n : ℕ} (p c lam σ β v0 : ℝ) (hc : 0 < c) (hcp : c < p) (hlam : 0 < lam)
    (hσ : 0 < σ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hv0 : 0 < v0)
    (v w : Fin n → ℝ) (hv : ∀ j, 0 ≤ v j) (hw : ∀ j, 0 ≤ w j)
    (hva : Antitone v) (hwa : Antitone w) (r l : ℕ) (hr : r ≤ n) (hl : l ≤ n)
    (hvw : Majorized v w) :
    ((∀ S : Finset (Fin n), profitI p c lam σ β v v0 S ≤ profitI p c lam σ β v v0 (RetailVariety.Statics.A n r)) →
      (∀ S : Finset (Fin n), profitI p c lam σ β w v0 S ≤ profitI p c lam σ β w v0 (RetailVariety.Statics.A n l)) →
      profitI p c lam σ β v v0 (RetailVariety.Statics.A n r) ≤ profitI p c lam σ β w v0 (RetailVariety.Statics.A n l)) ∧
    ((∀ S : Finset (Fin n), profitT p c lam v v0 S ≤ profitT p c lam v v0 (RetailVariety.Statics.A n r)) →
      (∀ S : Finset (Fin n), profitT p c lam w v0 S ≤ profitT p c lam w v0 (RetailVariety.Statics.A n l)) →
      profitT p c lam v v0 (RetailVariety.Statics.A n r) ≤ profitT p c lam w v0 (RetailVariety.Statics.A n l)) := by
  exact theorem3_core p c lam σ β v0 hc hcp hlam hσ hβ0 hβ1 hv0 v w hv hw hva hwa r l hr hl hvw
