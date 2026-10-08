-- Prove2me | solution 1 for SecretaryWD.Graphic.graphic_matroid_secretary_competitive
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T08:09:11.872098+00:00
-- url     : https://prove2.me/submissions/4efdbcc0-ad5c-49fa-a540-6914192c23fa

import Mathlib
import Definitions.Def_SecretaryWD_Graphic_RandomPartition
import Definitions.Def_SecretaryWD_Graphic_PartitionSecretary



namespace SecretaryWD.Graphic

section PPpart


open Classical

lemma cs_find_iff {m : ℕ} (p : Fin m → Bool) (t : Fin m) :
    (List.finRange m).find? p = some t ↔ p t = true ∧ ∀ s : Fin m, s < t → p s = false := by
  rw [List.find?_eq_some_iff_getElem]
  constructor
  · rintro ⟨hp, i, hi, hit, hj⟩
    refine ⟨hp, fun s hs => ?_⟩
    simp only [List.getElem_finRange] at hit
    subst hit
    have := hj s.val (by simpa [Fin.lt_def] using hs)
    simpa using this
  · rintro ⟨hp, hs⟩
    refine ⟨hp, t.val, by simp, by simp, fun j hj => ?_⟩
    have := hs ⟨j, by omega⟩ (by simp [Fin.lt_def]; omega)
    simp [this]

variable {L : Type*} [LinearOrder L]

/-- `a` is the position of the maximum among the first `t` arrivals. -/
def IsPA {m : ℕ} (k : Fin m → L) (σ : Equiv.Perm (Fin m)) (t a : Fin m) : Prop :=
  a < t ∧ ∀ u : Fin m, u < t → u ≠ a → k (σ u) < k (σ a)

noncomputable def NN {m : ℕ} (k : Fin m → L) (e₀ : Fin m) (t a : Fin m) : ℕ :=
  (Finset.univ.filter fun σ : Equiv.Perm (Fin m) => σ t = e₀ ∧ IsPA k σ t a).card

noncomputable def AA {m : ℕ} (e₀ : Fin m) (t : Fin m) : ℕ :=
  (Finset.univ.filter fun σ : Equiv.Perm (Fin m) => σ t = e₀).card

lemma NN_le {m : ℕ} (k : Fin m → L) (e₀ t a a' : Fin m) (ha : a < t) (ha' : a' < t) :
    NN k e₀ t a ≤ NN k e₀ t a' := by
  unfold NN
  apply Finset.card_le_card_of_injOn (fun σ => σ * Equiv.swap a a')
  · intro σ hσ
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hσ ⊢
    obtain ⟨h1, h2, h3⟩ := hσ
    have hta : t ≠ a := ne_of_gt ha
    have hta' : t ≠ a' := ne_of_gt ha'
    refine ⟨?_, ha', ?_⟩
    · simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hta hta', h1]
    · intro u hu hua'
      simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_right]
      apply h3
      · rcases eq_or_ne u a with rfl | hua
        · rw [Equiv.swap_apply_left]; exact ha'
        · rw [Equiv.swap_apply_of_ne_of_ne hua hua']; exact hu
      · intro h
        apply hua'
        have := congrArg (Equiv.swap a a') h
        simpa using this
  · intro σ _ τ _ h
    simpa using h

lemma NN_eq {m : ℕ} (k : Fin m → L) (e₀ t a a' : Fin m) (ha : a < t) (ha' : a' < t) :
    NN k e₀ t a = NN k e₀ t a' :=
  le_antisymm (NN_le k e₀ t a a' ha ha') (NN_le k e₀ t a' a ha' ha)

lemma AA_le {m : ℕ} (e₀ t t' : Fin m) : AA e₀ t ≤ AA e₀ t' := by
  unfold AA
  apply Finset.card_le_card_of_injOn (fun σ => σ * Equiv.swap t t')
  · intro σ hσ
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hσ ⊢
    simp [Equiv.Perm.mul_apply, hσ]
  · intro σ _ τ _ h
    simpa using h

lemma AA_eq {m : ℕ} (e₀ t t' : Fin m) : AA e₀ t = AA e₀ t' :=
  le_antisymm (AA_le e₀ t t') (AA_le e₀ t' t)

lemma AA_sum {m : ℕ} (e₀ : Fin m) : ∑ t, AA e₀ t = m.factorial := by
  unfold AA
  rw [show m.factorial = (Finset.univ : Finset (Equiv.Perm (Fin m))).card by
    simp [Fintype.card_perm]]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun σ : Equiv.Perm (Fin m) => σ.symm e₀)
    (t := Finset.univ) (by simp)]
  apply Finset.sum_congr rfl
  intro t _
  congr 1
  ext σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h; rw [← h]; simp
  · intro h; rw [← h]; simp

lemma AA_val {m : ℕ} (e₀ t : Fin m) : (m : ℝ) * AA e₀ t = m.factorial := by
  have h := AA_sum e₀
  rw [Finset.sum_congr rfl (fun t' _ => AA_eq e₀ t' t)] at h
  simp at h
  exact_mod_cast h

lemma NN_sum {m : ℕ} (k : Fin m → L) (hk : Function.Injective k) (e₀ t : Fin m) (ht : 0 < t.val) :
    ∑ a ∈ Finset.univ.filter (· < t), NN k e₀ t a = AA e₀ t := by
  unfold NN AA
  rw [← Finset.card_biUnion]
  · congr 1
    ext σ
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, _, h, _⟩; exact h
    · intro h
      obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image (Finset.univ.filter (· < t))
        (fun u => k (σ u)) ⟨⟨0, by omega⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]; exact ht⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hmax
      refine ⟨a, ha, h, ha, fun u hu hua => lt_of_le_of_ne (hmax u hu) ?_⟩
      intro heq
      exact hua (σ.injective (hk heq))
  · intro a _ a' _ haa'
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro σ h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    have := h1.2.2 a' h2.2.1 (Ne.symm haa')
    have := h2.2.2 a h1.2.1 haa'
    exact absurd (lt_trans ‹k (σ a') < k (σ a)› this) (lt_irrefl _)

lemma NN_val {m : ℕ} (k : Fin m → L) (hk : Function.Injective k) (e₀ t a : Fin m) (ha : a < t) :
    (m : ℝ) * t.val * NN k e₀ t a = m.factorial := by
  have ht : 0 < t.val := lt_of_le_of_lt (Nat.zero_le _) ha
  have h := NN_sum k hk e₀ t ht
  rw [Finset.sum_congr rfl (fun a' ha' => NN_eq k e₀ t a' a (by simpa using ha') ha)] at h
  rw [Finset.sum_const, smul_eq_mul] at h
  have hc : (Finset.univ.filter (· < t)).card = t.val := by
    rw [show Finset.univ.filter (· < t) = Finset.Iio t by ext; simp]
    simp
  rw [hc] at h
  rw [← AA_val e₀ t, ← h]; push_cast; ring


def SuccP {m : ℕ} (k : Fin m → L) (r : ℕ) (σ : Equiv.Perm (Fin m)) : Prop :=
  ∃ t : Fin m, (List.finRange m).find? (fun t => decide (r ≤ t.val ∧
      ∀ s : Fin m, s < t → k (σ s) < k (σ t))) = some t ∧ ∀ e : Fin m, k e ≤ k (σ t)

lemma max_iff {m : ℕ} (k : Fin m → L) (hk : Function.Injective k) (e₀ : Fin m)
    (he₀ : ∀ e, k e ≤ k e₀) (y : Fin m) : (∀ e, k e ≤ k y) ↔ y = e₀ := by
  constructor
  · intro h; exact hk (le_antisymm (he₀ y) (h e₀))
  · rintro rfl; exact he₀

lemma SuccP_iff {m : ℕ} (k : Fin m → L) (hk : Function.Injective k) (e₀ : Fin m)
    (he₀ : ∀ e, k e ≤ k e₀) (r : ℕ) (hr : 1 ≤ r) (σ : Equiv.Perm (Fin m)) :
    SuccP k r σ ↔ ∃ t a : Fin m, r ≤ t.val ∧ a.val < r ∧ σ t = e₀ ∧ IsPA k σ t a := by
  unfold SuccP
  simp only [cs_find_iff, decide_eq_true_eq, decide_eq_false_iff_not, max_iff k hk e₀ he₀]
  constructor
  · rintro ⟨t, ⟨⟨hrt, _⟩, hs⟩, hte⟩
    have ht : 0 < t.val := by omega
    obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image (Finset.univ.filter (· < t))
      (fun u => k (σ u)) ⟨⟨0, by omega⟩, by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]; exact ht⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hmax
    have hPA : IsPA k σ t a := ⟨ha, fun u hu hua => lt_of_le_of_ne (hmax u hu)
      (fun heq => hua (σ.injective (hk heq)))⟩
    refine ⟨t, a, hrt, ?_, hte, hPA⟩
    by_contra hra
    push_neg at hra
    apply hs a ha
    refine ⟨hra, fun u hu => hPA.2 u (lt_trans hu ha) (ne_of_lt hu)⟩
  · rintro ⟨t, a, hrt, har, hte, hPA⟩
    refine ⟨t, ⟨⟨hrt, fun s hs => ?_⟩, fun s hs ⟨hrs, hrec⟩ => ?_⟩, hte⟩
    · rw [hte]
      refine lt_of_le_of_ne (he₀ _) (fun heq => ?_)
      have := σ.injective ((hk heq).trans hte.symm)
      exact absurd this (ne_of_lt hs)
    · have has : a < s := by rw [Fin.lt_def]; omega
      have h1 := hrec a has
      have h2 := hPA.2 s hs (ne_of_gt has)
      exact absurd (lt_trans h1 h2) (lt_irrefl _)

lemma SuccP_count {m : ℕ} (k : Fin m → L) (hk : Function.Injective k) (e₀ : Fin m)
    (he₀ : ∀ e, k e ≤ k e₀) (r : ℕ) (hr : 1 ≤ r) (hrm : r ≤ m) :
    ((Finset.univ.filter (SuccP k r)).card : ℝ) =
      ∑ i ∈ Finset.Ico r m, (r : ℝ) * (m.factorial : ℝ) / ((m : ℝ) * i) := by
  have hset : Finset.univ.filter (SuccP k r) =
      (Finset.univ.filter fun p : Fin m × Fin m => r ≤ p.1.val ∧ p.2.val < r).biUnion
        (fun p => Finset.univ.filter fun σ : Equiv.Perm (Fin m) => σ p.1 = e₀ ∧ IsPA k σ p.1 p.2) := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      SuccP_iff k hk e₀ he₀ r hr, Prod.exists]
    constructor
    · rintro ⟨t, a, h1, h2, h3, h4⟩; exact ⟨t, a, ⟨h1, h2⟩, h3, h4⟩
    · rintro ⟨t, a, ⟨h1, h2⟩, h3, h4⟩; exact ⟨t, a, h1, h2, h3, h4⟩
  rw [hset, Finset.card_biUnion]
  · push_cast
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    have hinner : ∀ t : Fin m, (∑ a : Fin m, if r ≤ t.val ∧ a.val < r then
        ((NN k e₀ t a : ℕ) : ℝ) else 0) =
        if r ≤ t.val then (r : ℝ) * m.factorial / (m * t.val) else 0 := by
      intro t
      split_ifs with hrt
      · have hm : (0 : ℝ) < m := by
          have := t.isLt; exact_mod_cast (show 0 < m by omega)
        have ht : (0 : ℝ) < t.val := by exact_mod_cast (show 0 < t.val by omega)
        have : ∀ a : Fin m, (if r ≤ t.val ∧ a.val < r then ((NN k e₀ t a : ℕ) : ℝ) else 0) =
            if a.val < r then (m.factorial : ℝ) / (m * t.val) else 0 := by
          intro a
          by_cases har : a.val < r
          · rw [if_pos ⟨hrt, har⟩, if_pos har]
            have := NN_val k hk e₀ t a (by rw [Fin.lt_def]; omega)
            field_simp
            linarith
          · rw [if_neg (fun h => har h.2), if_neg har]
        rw [Finset.sum_congr rfl (fun a _ => this a), ← Finset.sum_filter, Finset.sum_const,
          nsmul_eq_mul]
        have hc : (Finset.univ.filter fun a : Fin m => a.val < r).card = r := by
          rw [Fin.card_filter_val_lt]
          omega
        rw [hc]; ring
      · exact Finset.sum_eq_zero (fun a _ => if_neg (fun h => hrt h.1))
    refine (Finset.sum_congr rfl (fun t _ => hinner t)).trans ?_
    rw [Fin.sum_univ_eq_sum_range (fun i => if r ≤ i then (r : ℝ) * m.factorial / (m * i) else 0),
      ← Finset.sum_filter]
    apply Finset.sum_congr
    · ext i; simp [Finset.mem_Ico]; omega
    · intro i _; rfl
  · intro p hp q hq hpq
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro σ h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    apply hpq
    have ht : p.1 = q.1 := σ.injective (h1.1.trans h2.1.symm)
    have ha : p.2 = q.2 := by
      by_contra hne
      have := h1.2.2 q.2 (ht ▸ h2.2.1) (Ne.symm hne)
      have := h2.2.2 p.2 (ht ▸ h1.2.1) hne
      exact absurd (lt_trans ‹k (σ q.2) < k (σ p.2)› this) (lt_irrefl _)
    exact Prod.ext ht ha

lemma an_log_le (x : ℝ) (hx : 1 ≤ x) : Real.log x ≤ (x - x⁻¹) / 2 := by
  let h : ℝ → ℝ := fun y => (y - y⁻¹) / 2 - Real.log y
  have hd : ∀ y : ℝ, 0 < y → HasDerivAt h ((1 + (y ^ 2)⁻¹) / 2 - y⁻¹) y := by
    intro y hy
    have h1 := (hasDerivAt_id y).sub (hasDerivAt_inv hy.ne')
    have h2 := (h1.div_const 2).sub (Real.hasDerivAt_log hy.ne')
    refine h2.congr_deriv ?_
    ring
  have hmono : MonotoneOn h (Set.Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
    · intro y hy
      exact (hd y (lt_of_lt_of_le one_pos hy)).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      exact (hd y (lt_trans one_pos hy)).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      have hy0 : 0 < y := lt_trans one_pos hy
      rw [(hd y hy0).deriv]
      have : (1 + (y ^ 2)⁻¹) / 2 - y⁻¹ = (1 - y⁻¹) ^ 2 / 2 := by
        field_simp; ring
      rw [this]; positivity
  have := hmono (Set.mem_Ici.2 (le_refl (1:ℝ))) hx hx
  simp only [h, inv_one, sub_self, zero_div, Real.log_one] at this
  linarith

lemma an_step (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n + 1) - Real.log n ≤ (1 / n + 1 / (n + 1)) / 2 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < n := by linarith
  rw [← Real.log_div (by positivity) hpos.ne']
  refine (an_log_le _ (by rw [le_div_iff₀ hpos]; linarith)).trans (le_of_eq ?_)
  field_simp
  ring

lemma an_sum (r : ℕ) (hr : 1 ≤ r) (n : ℕ) (hn : r ≤ n) :
    Real.log n - Real.log r + (1 / r - 1 / n) / 2 ≤ ∑ i ∈ Finset.Ico r n, (1 : ℝ) / i := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hrn ih =>
    rw [Finset.sum_Ico_succ_top hrn]
    have := an_step n (le_trans hr hrn)
    push_cast
    linarith

lemma an_main (m : ℕ) (hm : 1 ≤ m) (r : ℕ) (hr : r = Nat.floor ((m : ℝ) / Real.exp 1)) :
    1 / Real.exp 1 ≤ (if r = 0 then (1 : ℝ) / m else
      (r : ℝ) / m * ∑ i ∈ Finset.Ico r m, (1 : ℝ) / i) := by
  have hE1 := Real.exp_one_gt_d9
  have hE2 := Real.exp_one_lt_d9
  set E := Real.exp 1 with hEdef
  have hEpos : 0 < E := by linarith
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hfl := Nat.floor_le (show 0 ≤ (m : ℝ) / E by positivity)
  have hlt := Nat.lt_floor_add_one ((m : ℝ) / E)
  rw [← hr] at hfl hlt
  rw [le_div_iff₀ hEpos] at hfl
  rw [div_lt_iff₀ hEpos] at hlt
  have h1n : 2718281 * r < 1000000 * m := by
    have : (2718281:ℝ) * r < 1000000 * m := by nlinarith
    exact_mod_cast this
  have h2n : 1000000 * m < 2718282 * (r + 1) := by
    have : (1000000:ℝ) * m < 2718282 * (r + 1) := by nlinarith
    exact_mod_cast this
  by_cases hr0 : r = 0
  · rw [if_pos hr0]
    subst hr0
    have hm2 : m ≤ 2 := by omega
    have : (m : ℝ) ≤ E := by
      have : (m : ℝ) ≤ 2 := by exact_mod_cast hm2
      linarith
    exact one_div_le_one_div_of_le hm0 this
  rw [if_neg hr0]
  have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.2 hr0
  by_cases hm8 : m ≤ 8
  · have hr3 : r ≤ 3 := by omega
    interval_cases m <;> interval_cases r <;> first
      | omega
      | (norm_num [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ]
         rw [inv_eq_one_div, div_le_iff₀ hEpos]; linarith)
  push_neg at hm8
  have hm9 : (9 : ℝ) ≤ m := by exact_mod_cast hm8
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hrm : r ≤ m := by omega
  have hS := an_sum r hr1 m hrm
  have hlog : 2 - E * r / m ≤ Real.log m - Real.log r := by
    have hx : 0 < (m : ℝ) / (E * r) := by positivity
    have := Real.one_sub_inv_le_log_of_pos hx
    rw [Real.log_div hm0.ne' (by positivity), Real.log_mul hEpos.ne' (by positivity),
      hEdef, Real.log_exp, ← hEdef, inv_div] at this
    linarith
  have hkey : (m - E * r) ^ 2 ≤ E * (m - r) / 2 := by
    have hd0 : 0 ≤ m - E * r := by linarith
    have hdE : m - E * r < E := by linarith
    have hmr : 2 * E ≤ m - r := by nlinarith
    nlinarith
  have hL : 1 / E ≤ r / m * ((2 - E * r / m) + (1 / r - 1 / m) / 2) := by
    rw [div_le_iff₀ hEpos]
    have : r / m * ((2 - E * r / m) + (1 / r - 1 / m) / 2) * E =
        1 + (E * (m - r) / 2 - (m - E * r) ^ 2) / m ^ 2 := by
      field_simp; ring
    rw [this]
    have : 0 ≤ (E * (m - r) / 2 - (m - E * r) ^ 2) / m ^ 2 := by
      apply div_nonneg <;> nlinarith
    linarith
  refine hL.trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  linarith

lemma SuccP_zero {m : ℕ} (hm : 1 ≤ m) (k : Fin m → L) (hk : Function.Injective k) (e₀ : Fin m)
    (he₀ : ∀ e, k e ≤ k e₀) (σ : Equiv.Perm (Fin m)) :
    SuccP k 0 σ ↔ σ ⟨0, hm⟩ = e₀ := by
  unfold SuccP
  simp only [cs_find_iff, decide_eq_true_eq, decide_eq_false_iff_not, max_iff k hk e₀ he₀,
    Nat.zero_le, true_and]
  constructor
  · rintro ⟨t, ⟨_, hs⟩, hte⟩
    have : t = ⟨0, hm⟩ := by
      by_contra hne
      have hlt : (⟨0, hm⟩ : Fin m) < t := by
        rw [Fin.lt_def]; have : t.val ≠ 0 := fun h => hne (Fin.ext h); simp; omega
      exact hs _ hlt (fun u hu => absurd hu (by simp [Fin.lt_def]))
    rw [← this]; exact hte
  · intro h
    refine ⟨⟨0, hm⟩, ⟨fun s hs => absurd hs (by simp [Fin.lt_def]), fun s hs => absurd hs
      (by simp [Fin.lt_def])⟩, h⟩

theorem classical_secretary_guarantee_core (m : ℕ) (hm : 1 ≤ m) (v : Fin m → ℝ) :
    1 / Real.exp 1 ≤
      (1 / (m.factorial : ℝ)) *
        ((Finset.univ.filter fun σ : Equiv.Perm (Fin m) =>
            ∃ t : Fin m, SecretaryWD.DiscUpper.classicalSecretary m (fun s => SecretaryWD.DiscUpper.tieKey v (σ s)) = some t ∧
              ∀ e : Fin m, SecretaryWD.DiscUpper.tieKey v e ≤ SecretaryWD.DiscUpper.tieKey v (σ t)).card : ℝ) := by
  set k := SecretaryWD.DiscUpper.tieKey v with hkdef
  have hk : Function.Injective k := by
    intro a b h
    have := congrArg (fun p => OrderDual.ofDual (ofLex p).2) h
    simpa [hkdef, SecretaryWD.DiscUpper.tieKey] using this
  obtain ⟨e₀, _, he₀⟩ := Finset.exists_max_image Finset.univ k ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  replace he₀ : ∀ e, k e ≤ k e₀ := fun e => he₀ e (Finset.mem_univ _)
  set r := Nat.floor ((m : ℝ) / Real.exp 1) with hr
  have hfilt : (Finset.univ.filter fun σ : Equiv.Perm (Fin m) =>
            ∃ t : Fin m, SecretaryWD.DiscUpper.classicalSecretary m (fun s => k (σ s)) = some t ∧
              ∀ e : Fin m, k e ≤ k (σ t)) = Finset.univ.filter (SuccP k r) := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  rw [hfilt]
  have hmain := an_main m hm r hr
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hf0 : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  by_cases hr0 : r = 0
  · rw [if_pos hr0] at hmain
    have : Finset.univ.filter (SuccP k r) =
        Finset.univ.filter fun σ : Equiv.Perm (Fin m) => σ ⟨0, hm⟩ = e₀ := by
      ext σ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hr0]; exact SuccP_zero hm k hk e₀ he₀ σ
    rw [this]
    have h := AA_val e₀ ⟨0, hm⟩
    unfold AA at h
    refine hmain.trans (le_of_eq ?_)
    field_simp
    linarith
  · rw [if_neg hr0] at hmain
    have hrm : r ≤ m := by
      have : (r : ℝ) ≤ m := by
        have h1 := Nat.floor_le (show 0 ≤ (m : ℝ) / Real.exp 1 by positivity)
        rw [← hr] at h1
        have : (m : ℝ) / Real.exp 1 ≤ m := div_le_self hm0.le (by
          have := Real.add_one_le_exp (1 : ℝ); linarith)
        linarith
      exact_mod_cast this
    rw [SuccP_count k hk e₀ he₀ r (Nat.one_le_iff_ne_zero.2 hr0) hrm]
    refine hmain.trans (le_of_eq ?_)
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hi0 : (0 : ℝ) < i := by
      have := (Finset.mem_Ico.1 hi).1
      exact_mod_cast (show 0 < i by omega)
    field_simp

lemma SuccP_bound {m : ℕ} (hm : 1 ≤ m) (k : Fin m → L) (hk : Function.Injective k) :
    1 / Real.exp 1 ≤ (1 / (m.factorial : ℝ)) *
      ((Finset.univ.filter (SuccP k (Nat.floor ((m : ℝ) / Real.exp 1)))).card : ℝ) := by
  obtain ⟨e₀, _, he₀⟩ := Finset.exists_max_image Finset.univ k ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  replace he₀ : ∀ e, k e ≤ k e₀ := fun e => he₀ e (Finset.mem_univ _)
  set r := Nat.floor ((m : ℝ) / Real.exp 1) with hr
  have hmain := an_main m hm r hr
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hf0 : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  by_cases hr0 : r = 0
  · rw [if_pos hr0] at hmain
    have : Finset.univ.filter (SuccP k r) =
        Finset.univ.filter fun σ : Equiv.Perm (Fin m) => σ ⟨0, hm⟩ = e₀ := by
      ext σ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hr0]; exact SuccP_zero hm k hk e₀ he₀ σ
    rw [this]
    have h := AA_val e₀ ⟨0, hm⟩
    unfold AA at h
    refine hmain.trans (le_of_eq ?_)
    field_simp
    linarith
  · rw [if_neg hr0] at hmain
    have hrm : r ≤ m := by
      have : (r : ℝ) ≤ m := by
        have h1 := Nat.floor_le (show 0 ≤ (m : ℝ) / Real.exp 1 by positivity)
        rw [← hr] at h1
        have : (m : ℝ) / Real.exp 1 ≤ m := div_le_self hm0.le (by
          have := Real.add_one_le_exp (1 : ℝ); linarith)
        linarith
      exact_mod_cast this
    rw [SuccP_count k hk e₀ he₀ r (Nat.one_le_iff_ne_zero.2 hr0) hrm]
    refine hmain.trans (le_of_eq ?_)
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hi0 : (0 : ℝ) < i := by
      have := (Finset.mem_Ico.1 hi).1
      exact_mod_cast (show 0 < i by omega)
    field_simp

/-- Fiber uniformity. -/
lemma fiber_count {n k : ℕ} (Φ : Equiv.Perm (Fin n) → Equiv.Perm (Fin k))
    (R : Equiv.Perm (Fin k) → Equiv.Perm (Fin n))
    (hR : ∀ τ π, Φ (R τ * π) = τ * Φ π) (Q : Equiv.Perm (Fin k) → Prop) :
    (1 / (n.factorial : ℝ)) * ((Finset.univ.filter fun π => Q (Φ π)).card : ℝ) =
      (1 / (k.factorial : ℝ)) * ((Finset.univ.filter Q).card : ℝ) := by
  set F : Equiv.Perm (Fin k) → ℕ := fun σ => (Finset.univ.filter fun π => Φ π = σ).card
  have hle : ∀ σ σ', F σ ≤ F σ' := by
    intro σ σ'
    apply Finset.card_le_card_of_injOn (fun π => R (σ' * σ⁻¹) * π)
    · intro π hπ
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hπ ⊢
      rw [hR, hπ]; group
    · intro a _ b _ h
      simpa using h
  have hF : ∀ σ, F σ = F 1 := fun σ => le_antisymm (hle σ 1) (hle 1 σ)
  have htot : ∀ S : Finset (Equiv.Perm (Fin k)),
      (Finset.univ.filter fun π => Φ π ∈ S).card = S.card * F 1 := by
    intro S
    rw [Finset.card_eq_sum_card_fiberwise (f := Φ) (t := S) (by intro π hπ; simpa using hπ)]
    rw [Finset.sum_congr rfl (g := fun _ => F 1)]
    · simp
    · intro σ hσ
      rw [← hF σ]
      congr 1; ext π
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨_, h⟩; exact h
      · intro h; exact ⟨h ▸ hσ, h⟩
  have h1 := htot Finset.univ
  have h2 := htot (Finset.univ.filter Q)
  simp only [Finset.mem_univ, Finset.filter_true, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, Finset.mem_filter, true_and] at h1 h2
  rw [h2]
  have hk0 : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hn0 : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have h1' : (n.factorial : ℝ) = k.factorial * F 1 := by exact_mod_cast h1
  rw [h1']
  push_cast
  have hF0 : (0 : ℝ) < F 1 := by
    have : (0:ℝ) < k.factorial * F 1 := h1' ▸ hn0
    exact pos_of_mul_pos_right this hk0.le
  field_simp

lemma cs_cast {α : Type*} [LinearOrder α] {c c' : ℕ} (h : c = c') (x : Fin c → α) :
    SecretaryWD.DiscUpper.classicalSecretary c x =
      (SecretaryWD.DiscUpper.classicalSecretary c' (fun i => x (Fin.cast h.symm i))).map
        (Fin.cast h.symm) := by
  subst h; simp

lemma oemb_congr {n : ℕ} {s s' : Finset (Fin n)} (hs : s = s') {c c' : ℕ} (h : s.card = c)
    (h' : s'.card = c') (i : Fin c) (i' : Fin c') (hi : i.val = i'.val) :
    (s.orderEmbOfFin h i : Fin n) = s'.orderEmbOfFin h' i' := by
  subst hs
  have : c = c' := h.symm.trans h'
  subst this
  have : i = i' := Fin.ext hi
  subst this; rfl

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def Np (E : Finset (Sym2 V)) (p : Finset (Sym2 V)) : Finset (Fin E.card) :=
  Finset.univ.filter fun j => edgeAt E j ∈ p

lemma mem_partTimes' (E : Finset (Sym2 V)) (π : Equiv.Perm (Fin E.card)) (p : Finset (Sym2 V))
    (t : Fin E.card) : t ∈ partTimes E π p ↔ π t ∈ Np E p := by
  simp [partTimes, Np]

lemma card_partTimes' (E : Finset (Sym2 V)) (π : Equiv.Perm (Fin E.card)) (p : Finset (Sym2 V)) :
    (partTimes E π p).card = (Np E p).card := by
  apply Finset.card_nbij' π π.symm
  · intro t ht; simpa [mem_partTimes'] using ht
  · intro y hy; simp only [Finset.mem_coe] at hy ⊢; rw [mem_partTimes']; simpa using hy
  · intro t _; simp
  · intro y _; simp

noncomputable def npE (E : Finset (Sym2 V)) (p : Finset (Sym2 V)) :
    Fin (Np E p).card ≃o {x // x ∈ Np E p} := (Np E p).orderIsoOfFin rfl

noncomputable def Phi (E : Finset (Sym2 V)) (p : Finset (Sym2 V)) (π : Equiv.Perm (Fin E.card)) :
    Equiv.Perm (Fin (Np E p).card) :=
  (finCongr (card_partTimes' E π p).symm).trans
    (((partTimes E π p).orderIsoOfFin rfl).toEquiv.trans
      ((π.subtypeEquiv (fun t => mem_partTimes' E π p t)).trans (npE E p).symm.toEquiv))

lemma Phi_apply (E : Finset (Sym2 V)) (p : Finset (Sym2 V)) (π : Equiv.Perm (Fin E.card))
    (i : Fin (Np E p).card) :
    ((npE E p (Phi E p π i)) : Fin E.card) =
      π (partArrivalTime E π p (Fin.cast (card_partTimes' E π p).symm i)) := by
  simp [Phi, partArrivalTime, Finset.coe_orderIsoOfFin_apply]

noncomputable def Rt (E : Finset (Sym2 V)) (p : Finset (Sym2 V))
    (τ : Equiv.Perm (Fin (Np E p).card)) : Equiv.Perm (Fin E.card) :=
  Equiv.Perm.ofSubtype ((npE E p).symm.toEquiv.trans (τ.trans (npE E p).toEquiv))

lemma Rt_mem (E : Finset (Sym2 V)) (p : Finset (Sym2 V)) (τ : Equiv.Perm (Fin (Np E p).card))
    (y : Fin E.card) : Rt E p τ y ∈ Np E p ↔ y ∈ Np E p := by
  by_cases hy : y ∈ Np E p
  · simp only [hy, iff_true]
    rw [Rt, Equiv.Perm.ofSubtype_apply_of_mem _ hy]
    exact Subtype.property _
  · rw [Rt, Equiv.Perm.ofSubtype_apply_of_not_mem _ hy]

lemma Phi_Rt (E : Finset (Sym2 V)) (p : Finset (Sym2 V)) (τ : Equiv.Perm (Fin (Np E p).card))
    (π : Equiv.Perm (Fin E.card)) : Phi E p (Rt E p τ * π) = τ * Phi E p π := by
  ext i
  have hinj : Function.Injective (fun j : Fin (Np E p).card => ((npE E p j) : Fin E.card)) :=
    fun a b h => (npE E p).injective (Subtype.ext h)
  apply congrArg Fin.val
  apply hinj
  simp only
  rw [Phi_apply]
  have hs : partTimes E (Rt E p τ * π) p = partTimes E π p := by
    ext t; rw [mem_partTimes', mem_partTimes', Equiv.Perm.mul_apply, Rt_mem]
  have ha : partArrivalTime E (Rt E p τ * π) p (Fin.cast (card_partTimes' E _ p).symm i) =
      partArrivalTime E π p (Fin.cast (card_partTimes' E π p).symm i) := by
    unfold partArrivalTime
    exact oemb_congr hs _ _ _ _ (by simp)
  rw [ha, Equiv.Perm.mul_apply]
  set a := partArrivalTime E π p (Fin.cast (card_partTimes' E π p).symm i)
  have hmem : π a ∈ Np E p := by
    rw [← mem_partTimes']; exact Finset.orderEmbOfFin_mem _ _ _
  rw [Rt, Equiv.Perm.ofSubtype_apply_of_mem _ hmem]
  have : (npE E p).symm ⟨π a, hmem⟩ = Phi E p π i := by
    apply (npE E p).injective
    apply Subtype.ext
    simp only [OrderIso.apply_symm_apply]
    rw [Phi_apply]
  show ((npE E p (τ ((npE E p).symm ⟨π a, hmem⟩))) : Fin E.card) = _
  rw [this]; rfl

noncomputable def kp (E : Finset (Sym2 V)) (v : Sym2 V → ℝ) (p : Finset (Sym2 V))
    (i : Fin (Np E p).card) : Lex (ℝ × (Fin E.card)ᵒᵈ) :=
  SecretaryWD.DiscUpper.tieKey (fun j => v (edgeAt E j)) (npE E p i : Fin E.card)

lemma kp_inj (E : Finset (Sym2 V)) (v : Sym2 V → ℝ) (p : Finset (Sym2 V)) :
    Function.Injective (kp E v p) := by
  intro a b h
  have := congrArg (fun q => OrderDual.ofDual (ofLex q).2) h
  simp only [kp, SecretaryWD.DiscUpper.tieKey] at this
  exact (npE E p).injective (Subtype.ext (by simpa using this))

lemma sel_eq (E : Finset (Sym2 V)) (v : Sym2 V → ℝ) (p : Finset (Sym2 V))
    (π : Equiv.Perm (Fin E.card)) :
    partSelection E v π p =
      (SecretaryWD.DiscUpper.classicalSecretary (Np E p).card
        (fun i => kp E v p (Phi E p π i))).map (fun i => edgeAt E (npE E p (Phi E p π i))) := by
  unfold partSelection
  rw [cs_cast (card_partTimes' E π p), Option.map_map]
  congr 1
  · funext i
    simp only [Function.comp_apply, Phi_apply]
  · congr 1
    funext i
    simp only [kp, Phi_apply]

lemma edgeAt_equivFin (E : Finset (Sym2 V)) (e : Sym2 V) (he : e ∈ E) :
    edgeAt E (E.equivFin ⟨e, he⟩) = e := by
  simp [edgeAt]

lemma part_bound (E : Finset (Sym2 V)) (v : Sym2 V → ℝ) (hv : ∀ e, 0 ≤ v e)
    (p : Finset (Sym2 V)) (hp : p.Nonempty) (hpE : p ⊆ E) :
    partMax p v ≤ Real.exp 1 * SecretaryWD.DiscUpper.uniformAvg
      (fun π => ∑ e ∈ (partSelection E v π p).toFinset, v e) := by
  obtain ⟨e1, he1⟩ := hp
  have hj1 : E.equivFin ⟨e1, hpE he1⟩ ∈ Np E p := by
    simp [Np, edgeAt_equivFin E e1 (hpE he1), he1]
  have hkN : 1 ≤ (Np E p).card := Finset.card_pos.2 ⟨_, hj1⟩
  obtain ⟨istar, _, hstar⟩ := Finset.exists_max_image Finset.univ (kp E v p)
    ⟨⟨0, hkN⟩, Finset.mem_univ _⟩
  replace hstar : ∀ i, kp E v p i ≤ kp E v p istar := fun i => hstar i (Finset.mem_univ _)
  set vs := v (edgeAt E (npE E p istar)) with hvs
  have hvs0 : 0 ≤ vs := hv _
  have hmax : partMax p v ≤ vs := by
    unfold partMax
    rw [dif_pos ⟨e1, he1⟩]
    apply Finset.sup'_le
    intro e he
    have hj : E.equivFin ⟨e, hpE he⟩ ∈ Np E p := by
      simp [Np, edgeAt_equivFin E e (hpE he), he]
    set i := (npE E p).symm ⟨_, hj⟩
    have hi : (npE E p i : Fin E.card) = E.equivFin ⟨e, hpE he⟩ := by simp [i]
    have := hstar i
    simp only [kp, SecretaryWD.DiscUpper.tieKey, Prod.Lex.toLex_le_toLex'] at this
    rw [hi, edgeAt_equivFin] at this
    exact this.1
  set r := Nat.floor (((Np E p).card : ℝ) / Real.exp 1)
  have hpt : ∀ π : Equiv.Perm (Fin E.card),
      vs * (if SuccP (kp E v p) r (Phi E p π) then 1 else 0) ≤
        ∑ e ∈ (partSelection E v π p).toFinset, v e := by
    intro π
    split_ifs with hS
    · obtain ⟨t, ht, htmax⟩ := hS
      have htt : Phi E p π t = istar :=
        kp_inj E v p (le_antisymm (hstar _) (htmax istar))
      have : partSelection E v π p = some (edgeAt E (npE E p istar)) := by
        rw [sel_eq]
        have ht' : SecretaryWD.DiscUpper.classicalSecretary (Np E p).card
            (fun i => kp E v p (Phi E p π i)) = some t := ht
        rw [ht', Option.map_some, htt]
      rw [this]; simp [hvs]
    · rw [mul_zero]
      exact Finset.sum_nonneg (fun e _ => hv e)
  have hfc := fiber_count (Phi E p) (Rt E p) (Phi_Rt E p) (SuccP (kp E v p) r)
  have hb := SuccP_bound hkN (kp E v p) (kp_inj E v p)
  rw [← hfc] at hb
  have havg : vs * (1 / Real.exp 1) ≤ SecretaryWD.DiscUpper.uniformAvg
      (fun π => ∑ e ∈ (partSelection E v π p).toFinset, v e) := by
    unfold SecretaryWD.DiscUpper.uniformAvg
    calc vs * (1 / Real.exp 1)
        ≤ vs * ((1 / ((E.card).factorial : ℝ)) *
          ((Finset.univ.filter fun π => SuccP (kp E v p) r (Phi E p π)).card : ℝ)) :=
          mul_le_mul_of_nonneg_left hb hvs0
      _ = (1 / ((E.card).factorial : ℝ)) * ∑ π : Equiv.Perm (Fin E.card),
          vs * (if SuccP (kp E v p) r (Phi E p π) then 1 else 0) := by
          rw [← Finset.mul_sum, Finset.sum_boole]; ring
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Finset.sum_le_sum (fun π _ => hpt π)
  have hE : 0 < Real.exp 1 := Real.exp_pos 1
  calc partMax p v ≤ vs := hmax
    _ = Real.exp 1 * (vs * (1 / Real.exp 1)) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left havg hE.le

lemma sel_mem (E : Finset (Sym2 V)) (v : Sym2 V → ℝ) (p : Finset (Sym2 V))
    (π : Equiv.Perm (Fin E.card)) (e : Sym2 V) (he : e ∈ (partSelection E v π p).toFinset) :
    e ∈ p := by
  rw [Option.mem_toFinset] at he
  unfold partSelection at he
  obtain ⟨i, _, rfl⟩ := Option.map_eq_some_iff.1 he
  have := Finset.orderEmbOfFin_mem (partTimes E π p) rfl i
  simp only [partTimes, Finset.mem_filter, Finset.mem_univ, true_and] at this
  exact this

lemma uniformAvg_sum {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Equiv.Perm (Fin n) → ℝ) :
    SecretaryWD.DiscUpper.uniformAvg (fun π => ∑ i ∈ s, f i π) =
      ∑ i ∈ s, SecretaryWD.DiscUpper.uniformAvg (f i) := by
  unfold SecretaryWD.DiscUpper.uniformAvg
  rw [Finset.sum_comm, Finset.mul_sum]

theorem partition_secretary_competitive_core {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (P : Finset (Finset (Sym2 V))) (hP : IsPartitionOf E P)
    (v : Sym2 V → ℝ) (hv : ∀ e, 0 ≤ v e) :
    (∀ π : Equiv.Perm (Fin E.card), IsPartIndep P (partitionSecretaryOutput E v P π)) ∧
      partitionValue P v ≤
        Real.exp 1 * SecretaryWD.DiscUpper.uniformAvg fun π => partitionSecretaryValue E v P π := by
  obtain ⟨hPa, hPb⟩ := hP
  have hdisj : ∀ π : Equiv.Perm (Fin E.card),
      (P : Set (Finset (Sym2 V))).PairwiseDisjoint (fun p => (partSelection E v π p).toFinset) := by
    intro π p hp p' hp' hpp'
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro e h1 h2
    have := hPb hp hp' hpp'
    exact Finset.disjoint_left.1 this (sel_mem E v p π e h1) (sel_mem E v p' π e h2)
  refine ⟨fun π => ⟨?_, ?_⟩, ?_⟩
  · intro e he
    obtain ⟨p, hp, he⟩ := Finset.mem_biUnion.1 he
    exact ⟨p, hp, sel_mem E v p π e he⟩
  · intro p hp
    apply Finset.card_le_one.2
    have key : ∀ a ∈ partitionSecretaryOutput E v P π ∩ p, a ∈ (partSelection E v π p).toFinset := by
      intro a ha
      obtain ⟨ha1, ha2⟩ := Finset.mem_inter.1 ha
      obtain ⟨p', hp', ha'⟩ := Finset.mem_biUnion.1 ha1
      by_cases hpp : p' = p
      · subst hpp; exact ha'
      · exact absurd ha2 (Finset.disjoint_left.1 (hPb hp' hp hpp) (sel_mem E v p' π a ha'))
    intro a ha b hb
    have h1 := Option.mem_toFinset.1 (key a ha)
    have h2 := Option.mem_toFinset.1 (key b hb)
    rw [Option.mem_def] at h1 h2
    rw [h1] at h2
    exact Option.some_injective _ h2
  · have hval : ∀ π, partitionSecretaryValue E v P π =
        ∑ p ∈ P, ∑ e ∈ (partSelection E v π p).toFinset, v e := by
      intro π
      unfold partitionSecretaryValue partitionSecretaryOutput
      rw [Finset.sum_biUnion (hdisj π)]
    simp only [hval]
    rw [uniformAvg_sum, Finset.mul_sum]
    unfold partitionValue
    apply Finset.sum_le_sum
    intro p hp
    exact part_bound E v hv p (hPa p hp).1 (hPa p hp).2

lemma pmfExp_mono {α : Type*} [Fintype α] (μ : PMF α) (f g : α → ℝ)
    (h : ∀ a ∈ μ.support, f a ≤ g a) : pmfExp μ f ≤ pmfExp μ g := by
  unfold pmfExp
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : a ∈ μ.support
  · exact mul_le_mul_of_nonneg_left (h a ha) ENNReal.toReal_nonneg
  · rw [PMF.mem_support_iff, not_not] at ha
    simp [ha]

lemma pmfExp_nonneg {α : Type*} [Fintype α] (μ : PMF α) (f : α → ℝ)
    (h : ∀ a ∈ μ.support, 0 ≤ f a) : 0 ≤ pmfExp μ f := by
  have := pmfExp_mono μ (fun _ => 0) f h
  simpa [pmfExp] using this

lemma pmfExp_mul {α : Type*} [Fintype α] (μ : PMF α) (f : α → ℝ) (c : ℝ) :
    pmfExp μ (fun a => c * f a) = c * pmfExp μ f := by
  unfold pmfExp; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; ring

lemma partMax_nonneg (p : Finset (Sym2 V)) (v : Sym2 V → ℝ) (hv : ∀ e, 0 ≤ v e) :
    0 ≤ partMax p v := by
  unfold partMax
  split_ifs with h
  · obtain ⟨e, he⟩ := h
    exact (hv e).trans (Finset.le_sup' v he)
  · exact le_refl _

lemma algval_le (E : Finset (Sym2 V)) (v : Sym2 V → ℝ) (hv : ∀ e, 0 ≤ v e)
    (P : Finset (Finset (Sym2 V))) (hP : IsPartitionOf E P) :
    0 ≤ SecretaryWD.DiscUpper.uniformAvg (fun π => partitionSecretaryValue E v P π) ∧
    SecretaryWD.DiscUpper.uniformAvg (fun π => partitionSecretaryValue E v P π) ≤
      partitionValue P v := by
  obtain ⟨hPa, hPb⟩ := hP
  have hpt : ∀ π : Equiv.Perm (Fin E.card), 0 ≤ partitionSecretaryValue E v P π ∧
      partitionSecretaryValue E v P π ≤ partitionValue P v := by
    intro π
    have hdisj : (P : Set (Finset (Sym2 V))).PairwiseDisjoint
        (fun p => (partSelection E v π p).toFinset) := by
      intro p hp p' hp' hpp'
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro e h1 h2
      exact Finset.disjoint_left.1 (hPb hp hp' hpp') (sel_mem E v p π e h1) (sel_mem E v p' π e h2)
    unfold partitionSecretaryValue partitionSecretaryOutput partitionValue
    rw [Finset.sum_biUnion hdisj]
    refine ⟨Finset.sum_nonneg (fun p _ => Finset.sum_nonneg (fun e _ => hv e)),
      Finset.sum_le_sum (fun p hp => ?_)⟩
    cases hs : partSelection E v π p with
    | none => simpa using partMax_nonneg p v hv
    | some e =>
      have he : e ∈ p := sel_mem E v p π e (by simp [hs])
      simp only [Option.toFinset_some, Finset.sum_singleton]
      unfold partMax
      rw [dif_pos ⟨e, he⟩]
      exact Finset.le_sup' v he
  have hf : (0 : ℝ) < ((E.card).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  unfold SecretaryWD.DiscUpper.uniformAvg
  constructor
  · exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun π _ => (hpt π).1))
  · calc (1 / ((E.card).factorial : ℝ)) * ∑ π, partitionSecretaryValue E v P π
        ≤ (1 / ((E.card).factorial : ℝ)) * ∑ _π : Equiv.Perm (Fin E.card), partitionValue P v :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun π _ => (hpt π).2)) (by positivity)
      _ = partitionValue P v := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
            nsmul_eq_mul]
          field_simp

theorem partition_property_competitive_core {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (μ : PMF (Finset (Finset (Sym2 V)))) (α : ℝ)
    (hμ : IsPartitionScheme G.edgeFinset μ α) (v : Sym2 V → ℝ) (hv : ∀ e, 0 ≤ v e) :
    (∀ P ∈ μ.support, ∀ π : Equiv.Perm (Fin G.edgeFinset.card),
        partitionSecretaryOutput G.edgeFinset v P π ⊆ G.edgeFinset ∧
          IsAcyclicSet (partitionSecretaryOutput G.edgeFinset v P π)) ∧
      OPT G.edgeFinset v ≤ Real.exp 1 * α * expectedAlgValue G.edgeFinset v μ := by
  obtain ⟨h1, h2⟩ := hμ
  refine ⟨fun P hP π => ?_, ?_⟩
  · obtain ⟨hpart, hac⟩ := h1 P hP
    have hind := (partition_secretary_competitive_core G.edgeFinset P hpart v hv).1 π
    refine ⟨fun e he => ?_, hac _ hind⟩
    obtain ⟨p, hp, hep⟩ := hind.1 e he
    exact (hpart.1 p hp).2 hep
  · have hopt := h2 v hv
    have hOPT0 : 0 ≤ OPT G.edgeFinset v := by
      unfold OPT
      refine le_trans (le_of_eq ?_) (Finset.le_sup' (fun S => ∑ e ∈ S, v e)
        (empty_mem_acyclicSubsets G.edgeFinset))
      simp
    set X := pmfExp μ fun P => partitionValue P v
    set Y := expectedAlgValue G.edgeFinset v μ
    have hXY : X ≤ Real.exp 1 * Y := by
      unfold Y expectedAlgValue
      rw [← pmfExp_mul]
      apply pmfExp_mono
      intro P hP
      exact (partition_secretary_competitive_core G.edgeFinset P (h1 P hP).1 v hv).2
    have hY0 : 0 ≤ Y := pmfExp_nonneg _ _ (fun P hP => (algval_le _ v hv P (h1 P hP).1).1)
    have hYX : Y ≤ X := pmfExp_mono _ _ _ (fun P hP => (algval_le _ v hv P (h1 P hP).1).2)
    rcases le_or_gt 0 α with hα | hα
    · calc OPT G.edgeFinset v ≤ α * X := hopt
        _ ≤ α * (Real.exp 1 * Y) := mul_le_mul_of_nonneg_left hXY hα
        _ = Real.exp 1 * α * Y := by ring
    · have hX0 : X ≤ 0 := by
        by_contra hX; push_neg at hX
        have : α * X < 0 := mul_neg_of_neg_of_pos hα hX
        linarith
      have hY : Y = 0 := le_antisymm (hYX.trans hX0) hY0
      rw [hY, mul_zero]
      have : α * X ≤ 0 := by nlinarith
      linarith


end PPpart

section TPpart


section RP


open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

def RPInv (E : Finset (Sym2 V)) (P : Finset (Finset (Sym2 V))) : Prop :=
  IsPartitionOf E P ∧ ∀ S : Finset (Sym2 V), IsPartIndep P S → IsAcyclicSet S

lemma rp_edge_eq {e : Sym2 V} {x x' : V} (hx : x ∈ e) (hx' : x' ∈ e) (hne : x ≠ x') :
    e = s(x, x') := by
  exact (Sym2.mem_and_mem_iff hne).1 ⟨hx, hx'⟩

lemma rp_mem_redPart {E : Finset (Sym2 V)} {col : V → Bool} {x : V} {f : Sym2 V} :
    f ∈ redPart E col x ↔ f ∈ E ∧ x ∈ f ∧ ∃ y ∈ f, col y = false := by
  unfold redPart; simp [Finset.mem_filter]

lemma rp_mem_roundParts {E : Finset (Sym2 V)} {col : V → Bool} {p : Finset (Sym2 V)} :
    p ∈ roundParts E col ↔ (∃ x, col x = true ∧ redPart E col x = p) ∧ p.Nonempty := by
  unfold roundParts; simp [Finset.mem_filter, Finset.mem_image]

lemma rp_mem_blue {E : Finset (Sym2 V)} {col : V → Bool} {f : Sym2 V} :
    f ∈ blueEdges E col ↔ f ∈ E ∧ ∀ y ∈ f, col y = false := by
  unfold blueEdges; simp [Finset.mem_filter]

/-- An edge in some round part, containing a red node `x`, lies in `redPart x`. -/
lemma rp_in_redPart_of {E : Finset (Sym2 V)} {col : V → Bool} {x x' : V} {f : Sym2 V}
    (hx : col x = true) (hxf : x ∈ f) (hf : f ∈ redPart E col x') (hx' : col x' = true) :
    f ∈ redPart E col x := by
  rw [rp_mem_redPart] at hf ⊢
  obtain ⟨hfE, hx'f, y, hy, hcy⟩ := hf
  refine ⟨hfE, hxf, y, hy, hcy⟩

lemma rp_red_eq {E : Finset (Sym2 V)} {col : V → Bool} {x x' : V} {f : Sym2 V}
    (hx : col x = true) (hxf : x ∈ f) (hf : f ∈ redPart E col x') (hx' : col x' = true) :
    x = x' := by
  by_contra hne
  rw [rp_mem_redPart] at hf
  obtain ⟨_, hx'f, y, hy, hcy⟩ := hf
  have := rp_edge_eq hxf hx'f hne
  subst this
  rcases Sym2.mem_iff.1 hy with rfl | rfl <;> simp_all

lemma rp_step (E : Finset (Sym2 V)) (col : V → Bool) (Q : Finset (Finset (Sym2 V)))
    (hQ : RPInv (blueEdges E col) Q) : RPInv E (roundParts E col ∪ Q) := by
  obtain ⟨⟨hQa, hQb⟩, hQc⟩ := hQ
  have hblueE : blueEdges E col ⊆ E := fun f hf => (rp_mem_blue.1 hf).1
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro p hp
    rcases Finset.mem_union.1 hp with hp | hp
    · obtain ⟨⟨x, hx, rfl⟩, hne⟩ := rp_mem_roundParts.1 hp
      exact ⟨hne, fun f hf => (rp_mem_redPart.1 hf).1⟩
    · exact ⟨(hQa p hp).1, (hQa p hp).2.trans hblueE⟩
  · intro p hp p' hp' hpp'
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hp hp'
    -- generic disjointness via elements
    have key : ∀ p ∈ roundParts E col, ∀ p' ∈ roundParts E col ∪ Q, p ≠ p' →
        Disjoint p p' := by
      intro p hp p' hp' hpp'
      obtain ⟨⟨x, hx, rfl⟩, _⟩ := rp_mem_roundParts.1 hp
      rw [Finset.disjoint_left]
      intro f hf hf'
      have hxf := (rp_mem_redPart.1 hf).2.1
      rcases Finset.mem_union.1 hp' with hp' | hp'
      · obtain ⟨⟨x', hx', rfl⟩, _⟩ := rp_mem_roundParts.1 hp'
        exact hpp' (by rw [rp_red_eq hx hxf hf' hx'])
      · have := (rp_mem_blue.1 ((hQa p' hp').2 hf')).2 x hxf
        simp_all
    rcases hp with hp | hp
    · exact key p hp p' (by simp_all) hpp'
    rcases hp' with hp' | hp'
    · exact (key p' hp' p (by simp_all) (Ne.symm hpp')).symm
    · exact hQb hp hp' hpp'
  · intro S ⟨hS1, hS2⟩
    set S2 := S.filter (fun e => ∃ q ∈ Q, e ∈ q) with hS2def
    have hS2ind : IsPartIndep Q S2 := by
      refine ⟨fun e he => (Finset.mem_filter.1 he).2, fun q hq => ?_⟩
      refine le_trans (Finset.card_le_card ?_) (hS2 q (Finset.mem_union_right _ hq))
      exact Finset.inter_subset_inter_right (Finset.filter_subset _ _)
    have hS2ac := hQc S2 hS2ind
    intro u c hc
    by_cases hall : ∀ e ∈ c.edges, e ∈ (SimpleGraph.fromEdgeSet (S2 : Set (Sym2 V))).edgeSet
    · exact hS2ac _ (hc.transfer hall)
    push_neg at hall
    obtain ⟨e, hec, heS2⟩ := hall
    have heS : e ∈ (SimpleGraph.fromEdgeSet (S : Set (Sym2 V))).edgeSet := c.edges_subset_edgeSet hec
    rw [SimpleGraph.edgeSet_fromEdgeSet] at heS
    have heS' : e ∈ S := heS.1
    have heS2' : e ∉ S2 := by
      intro h; apply heS2; rw [SimpleGraph.edgeSet_fromEdgeSet]; exact ⟨h, heS.2⟩
    obtain ⟨p, hp, hep⟩ := hS1 e heS'
    have hpR : p ∈ roundParts E col := by
      rcases Finset.mem_union.1 hp with hp | hp
      · exact hp
      · exact absurd (Finset.mem_filter.2 ⟨heS', p, hp, hep⟩) heS2'
    obtain ⟨⟨x, hx, rfl⟩, hpne⟩ := rp_mem_roundParts.1 hpR
    have hxe : x ∈ e := (rp_mem_redPart.1 hep).2.1
    -- every S-edge containing x lies in redPart x
    have hinc : ∀ f ∈ S, x ∈ f → f ∈ redPart E col x := by
      intro f hfS hxf
      obtain ⟨p', hp', hfp'⟩ := hS1 f hfS
      rcases Finset.mem_union.1 hp' with hp' | hp'
      · obtain ⟨⟨x', hx', rfl⟩, _⟩ := rp_mem_roundParts.1 hp'
        exact rp_in_redPart_of hx hxf hfp' hx'
      · have := (rp_mem_blue.1 ((hQa p' hp').2 hfp')).2 x hxf
        simp_all
    have hcard := hS2 _ hp
    -- rotate cycle to start at x
    have hxs : x ∈ c.support := by
      induction e using Sym2.ind with
      | h a b =>
        rcases Sym2.mem_iff.1 hxe with rfl | rfl
        · exact c.fst_mem_support_of_mem_edges hec
        · exact c.snd_mem_support_of_mem_edges hec
    have hc' := hc.rotate hxs
    generalize c.rotate x hxs = d at hc'
    cases d with
    | nil => exact hc'.not_of_nil
    | cons h p =>
      rename_i y
      rw [SimpleGraph.Walk.cons_isCycle_iff] at hc'
      obtain ⟨hpath, hnot⟩ := hc'
      -- last edge of p contains x
      have hyx : y ≠ x := (h.ne).symm
      obtain ⟨f, hfp, hxf⟩ : ∃ f ∈ p.edges, x ∈ f := by
        cases hr : p.reverse with
        | nil => exact absurd rfl hyx
        | cons h' q =>
          rename_i z
          refine ⟨s(x, z), ?_, Sym2.mem_mk_left _ _⟩
          have : s(x, z) ∈ p.reverse.edges := by rw [hr]; simp
          simpa using this
      have hfS : f ∈ S := by
        have := p.edges_subset_edgeSet hfp
        rw [SimpleGraph.edgeSet_fromEdgeSet] at this
        exact this.1
      have h0S : s(x, y) ∈ S := by
        have := h
        rw [SimpleGraph.fromEdgeSet_adj] at this
        exact this.1
      have hfne : f ≠ s(x, y) := fun h => hnot (h ▸ hfp)
      apply hfne
      have h1 : f ∈ S ∩ redPart E col x := Finset.mem_inter.2 ⟨hfS, hinc f hfS hxf⟩
      have h2 : s(x, y) ∈ S ∩ redPart E col x :=
        Finset.mem_inter.2 ⟨h0S, hinc _ h0S (Sym2.mem_mk_left _ _)⟩
      exact Finset.card_le_one.1 hcard _ h1 _ h2

lemma rp_main : ∀ (n : ℕ) (E : Finset (Sym2 V)), E.card = n →
    ∀ P ∈ (partitionPMF E).support, RPInv E P := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro E hE P hP
  rw [partitionPMF] at hP
  split_ifs at hP with h
  · simp only [PMF.mem_support_bind_iff, PMF.support_map, Set.mem_image] at hP
    obtain ⟨e, _, b, _, c, _, Q, hQ, rfl⟩ := hP
    apply rp_step
    exact ih _ (hE ▸ blueEdges_card_lt E e b c) _ rfl Q hQ
  · rw [PMF.support_pure, Set.mem_singleton_iff] at hP
    subst hP
    refine ⟨⟨by simp, by simp⟩, fun S hS => ?_⟩
    have : S = ∅ := by
      ext e; simp only [Finset.notMem_empty, iff_false]
      intro he; obtain ⟨p, hp, _⟩ := hS.1 e he; simp at hp
    subst this; exact isAcyclicSet_empty

theorem random_partition_indep_acyclic_core {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∀ P ∈ (partitionPMF G.edgeFinset).support,
      IsPartitionOf G.edgeFinset P ∧
        ∀ S : Finset (Sym2 V), IsPartIndep P S → IsAcyclicSet S :=
  rp_main _ _ rfl


end RP

section FO


open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma acyc_unique_parent {H : SimpleGraph V} (hH : H.IsAcyclic) {r x y z : V}
    (hy : H.Adj x y) (hz : H.Adj x z) (hr : H.Reachable r x)
    (hdy : H.dist r x = H.dist r y + 1) (hdz : H.dist r x = H.dist r z + 1) : y = z := by
  have hry : H.Reachable r y := hr.trans hy.reachable
  have hrz : H.Reachable r z := hr.trans hz.reachable
  obtain ⟨q, hq, hql⟩ := hr.exists_path_of_dist
  obtain ⟨py, hpy, hpyl⟩ := hry.exists_path_of_dist
  obtain ⟨pz, hpz, hpzl⟩ := hrz.exists_path_of_dist
  have notin : ∀ {w : V} (p : H.Walk r w), p.length = H.dist r w → H.dist r x = H.dist r w + 1 →
      x ∉ p.support := by
    intro w p hpl hd hx
    have h1 := SimpleGraph.dist_le (p.takeUntil x hx)
    have h2 := p.length_takeUntil_le hx
    omega
  have hyq : y ∈ q.support :=
    hH.mem_support_of_ne_mem_support_of_adj_of_isPath hq hpy hy (notin py hpyl hdy)
  have hzq : z ∈ q.support :=
    hH.mem_support_of_ne_mem_support_of_adj_of_isPath hq hpz hz (notin pz hpzl hdz)
  have e1 := hH.path_concat hpy hq hy.symm hyq
  have e2 := hH.path_concat hpz hq hz.symm hzq
  have := congrArg (fun w => w.reverse.snd) (e1.symm.trans e2)
  simpa [SimpleGraph.Walk.reverse_concat] using this

lemma forest_orient (S : Finset (Sym2 V)) (hS : IsAcyclicSet S) (hloop : ∀ f ∈ S, ¬ f.IsDiag)
    (v : Sym2 V → ℝ) :
    ∃ C : Finset (V × V), (∀ c ∈ C, s(c.1, c.2) ∈ S ∧ c.1 ≠ c.2) ∧
      (∀ c ∈ C, ∀ c' ∈ C, c.1 = c'.1 → c = c') ∧
      ∑ c ∈ C, v s(c.1, c.2) = ∑ f ∈ S, v f := by
  set H := SimpleGraph.fromEdgeSet (S : Set (Sym2 V)) with hHdef
  have hH : H.IsAcyclic := hS
  let rt : V → V := fun z => Quot.out (H.connectedComponentMk z)
  have hrt : ∀ z, H.Reachable (rt z) z := by
    intro z
    apply SimpleGraph.ConnectedComponent.exact
    exact Quot.out_eq _
  have hrt_adj : ∀ a b, H.Adj a b → rt a = rt b := by
    intro a b h
    simp only [rt]
    rw [SimpleGraph.ConnectedComponent.sound h.reachable]
  let φ : Sym2 V → V × V := fun f =>
    if H.dist (rt f.out.1) f.out.2 < H.dist (rt f.out.1) f.out.1 then (f.out.1, f.out.2)
    else (f.out.2, f.out.1)
  have hφs : ∀ f, s((φ f).1, (φ f).2) = f := by
    intro f
    simp only [φ]
    split_ifs
    · exact Quot.out_eq f
    · rw [Sym2.eq_swap]; exact Quot.out_eq f
  have hφprop : ∀ f ∈ S, H.Adj (φ f).1 (φ f).2 ∧
      H.dist (rt (φ f).1) (φ f).1 = H.dist (rt (φ f).1) (φ f).2 + 1 := by
    intro f hf
    have hadj : H.Adj f.out.1 f.out.2 := by
      rw [hHdef, SimpleGraph.fromEdgeSet_adj]
      refine ⟨by rw [show s(f.out.1, f.out.2) = f from Quot.out_eq f]; exact Finset.mem_coe.2 hf, ?_⟩
      intro h
      apply hloop f hf
      rw [← Quot.out_eq f]
      exact Sym2.mk_isDiag_iff.2 h
    have hreach := hrt f.out.1
    have hor := hH.dist_eq_dist_add_one_of_adj_of_reachable (rt f.out.1) hadj hreach
    simp only [φ]
    split_ifs with hlt
    · refine ⟨hadj, ?_⟩
      dsimp only
      omega
    · refine ⟨hadj.symm, ?_⟩
      dsimp only
      rw [← hrt_adj _ _ hadj]
      omega
  refine ⟨S.image φ, ?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hc
    exact ⟨by rw [hφs]; exact hf, (hφprop f hf).1.ne⟩
  · intro c hc c' hc' h1
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hc
    obtain ⟨f', hf', rfl⟩ := Finset.mem_image.1 hc'
    obtain ⟨ha, hd⟩ := hφprop f hf
    obtain ⟨ha', hd'⟩ := hφprop f' hf'
    rw [← h1] at ha' hd'
    have := acyc_unique_parent hH ha ha' (hrt _) hd hd'
    exact Prod.ext h1 this
  · rw [Finset.sum_image]
    · exact Finset.sum_congr rfl (fun f _ => by rw [hφs])
    · intro f _ f' _ h
      rw [← hφs f, ← hφs f', h]


end FO

section PM


open Classical

lemma pmfExp_bind' {α β : Type*} [Fintype α] [Fintype β] (p : PMF α) (g : α → PMF β)
    (f : β → ℝ) : pmfExp (p.bind g) f = pmfExp p (fun a => pmfExp (g a) f) := by
  unfold pmfExp
  simp_rw [PMF.bind_apply, tsum_fintype]
  simp_rw [ENNReal.toReal_sum (fun a _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
    (PMF.apply_ne_top _ _)), ENNReal.toReal_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _; ring

lemma pmfExp_pure' {α : Type*} [Fintype α] (a : α) (f : α → ℝ) :
    pmfExp (PMF.pure a) f = f a := by
  unfold pmfExp
  simp only [PMF.pure_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb; simp [hb]
  · simp

lemma pmfExp_map' {α β : Type*} [Fintype α] [Fintype β] (p : PMF α) (h : α → β)
    (f : β → ℝ) : pmfExp (p.map h) f = pmfExp p (fun a => f (h a)) := by
  rw [← PMF.bind_pure_comp, pmfExp_bind']
  simp [Function.comp, pmfExp_pure']

lemma pmfExp_const' {α : Type*} [Fintype α] (p : PMF α) (K : ℝ) :
    pmfExp p (fun _ => K) = K := by
  unfold pmfExp
  rw [← Finset.sum_mul]
  have : ∑ a, (p a).toReal = 1 := by
    rw [← ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top _ _)]
    have := p.tsum_coe
    rw [tsum_fintype] at this
    rw [this]; simp
  rw [this, one_mul]

lemma pmfExp_add' {α : Type*} [Fintype α] (p : PMF α) (f g : α → ℝ) :
    pmfExp p (fun a => f a + g a) = pmfExp p f + pmfExp p g := by
  unfold pmfExp
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro a _; ring

lemma pmfExp_sum' {α ι : Type*} [Fintype α] (p : PMF α) (s : Finset ι) (f : ι → α → ℝ) :
    pmfExp p (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, pmfExp p (f i) := by
  unfold pmfExp
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

lemma pmfExp_mul' {α : Type*} [Fintype α] (μ : PMF α) (f : α → ℝ) (c : ℝ) :
    pmfExp μ (fun a => c * f a) = c * pmfExp μ f := by
  unfold pmfExp; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; ring

lemma pmfExp_mono' {α : Type*} [Fintype α] (μ : PMF α) (f g : α → ℝ)
    (h : ∀ a ∈ μ.support, f a ≤ g a) : pmfExp μ f ≤ pmfExp μ g := by
  unfold pmfExp
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : a ∈ μ.support
  · exact mul_le_mul_of_nonneg_left (h a ha) ENNReal.toReal_nonneg
  · rw [PMF.mem_support_iff, not_not] at ha
    simp [ha]

lemma pmfExp_uniform' {α : Type*} [Fintype α] [Nonempty α] (f : α → ℝ) :
    pmfExp (PMF.uniformOfFintype α) f = (1 / (Fintype.card α : ℝ)) * ∑ a, f a := by
  unfold pmfExp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a _
  simp [PMF.uniformOfFintype_apply, ENNReal.toReal_inv]

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def flipAt (x : V) : Equiv.Perm (V → Bool) :=
  Function.Involutive.toPerm (fun c => Function.update c x (!c x)) (by
    intro c; ext z; by_cases h : z = x <;> simp [Function.update, h])

lemma flipAt_apply_self (x : V) (c : V → Bool) : flipAt x c x = !c x := by
  show Function.update c x (!c x) x = !c x
  simp

lemma flipAt_apply_ne (x : V) (c : V → Bool) (z : V) (h : z ≠ x) : flipAt x c z = c z := by
  show Function.update c x (!c x) z = c z
  simp [h]

lemma sum_one_var (y : V) (F : Bool → ℝ) :
    ∑ c : V → Bool, F (c y) = (Fintype.card (V → Bool) : ℝ) / 2 * (F true + F false) := by
  have h1 : ∑ c : V → Bool, F (c y) = ∑ c : V → Bool, F (!c y) := by
    rw [← Equiv.sum_comp (flipAt y)]
    simp [flipAt_apply_self]
  have h2 : ∑ c : V → Bool, (F (c y) + F (!c y)) = ∑ _c : V → Bool, (F true + F false) := by
    apply Finset.sum_congr rfl; intro c _; cases c y <;> simp [add_comm]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← h1] at h2
  linarith

lemma sum_two_var (x y : V) (hxy : x ≠ y) (F : Bool → Bool → ℝ) :
    ∑ c : V → Bool, F (c x) (c y) = (Fintype.card (V → Bool) : ℝ) / 4 *
      (F true true + F true false + F false true + F false false) := by
  have hx : ∀ G : (V → Bool) → ℝ, ∑ c, G c = ∑ c, G (flipAt x c) :=
    fun G => (Equiv.sum_comp (flipAt x) G).symm
  have hy : ∀ G : (V → Bool) → ℝ, ∑ c, G c = ∑ c, G (flipAt y c) :=
    fun G => (Equiv.sum_comp (flipAt y) G).symm
  have e1 : ∑ c : V → Bool, F (c x) (c y) = ∑ c : V → Bool, F (!c x) (c y) := by
    rw [hx]; simp [flipAt_apply_self, flipAt_apply_ne x _ y (Ne.symm hxy)]
  have e2 : ∑ c : V → Bool, F (c x) (c y) = ∑ c : V → Bool, F (c x) (!c y) := by
    rw [hy]; simp [flipAt_apply_self, flipAt_apply_ne y _ x hxy]
  have e3 : ∑ c : V → Bool, F (c x) (c y) = ∑ c : V → Bool, F (!c x) (!c y) := by
    rw [e1, hy]; simp [flipAt_apply_self, flipAt_apply_ne y _ x hxy]
  have h4 : ∑ c : V → Bool, (F (c x) (c y) + F (!c x) (c y) + F (c x) (!c y) + F (!c x) (!c y))
      = ∑ _c : V → Bool, (F true true + F true false + F false true + F false false) := by
    apply Finset.sum_congr rfl; intro c _
    cases c x <;> cases c y <;> simp <;> ring
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h4
  rw [← e1, ← e2, ← e3] at h4
  linarith

/-- the weight -/
noncomputable def wt (a b : Bool) : ℝ :=
  if a = true ∧ b = false then 1 else if a = false ∧ b = false then 1 / 3 else 0

lemma wt_nonneg (a b : Bool) : 0 ≤ wt a b := by
  unfold wt; split_ifs <;> norm_num

lemma caseA (x y : V) (hxy : x ≠ y) :
    ∑ c : V → Bool, wt (c x) (c y) = (Fintype.card (V → Bool) : ℝ) / 3 := by
  rw [sum_two_var x y hxy]; simp [wt]; ring

lemma caseB (y : V) (a : Bool) :
    ∑ c : V → Bool, wt a (c y) = (Fintype.card (V → Bool) : ℝ) / 2 * (wt a true + wt a false) :=
  sum_one_var y (wt a)

lemma caseC (x : V) (b : Bool) :
    ∑ c : V → Bool, wt (c x) b = (Fintype.card (V → Bool) : ℝ) / 2 * (wt true b + wt false b) :=
  sum_one_var x (fun a => wt a b)

lemma round_prob (e : Sym2 V) (he : ¬ e.IsDiag) (x y : V) (hxy : x ≠ y) :
    1 / 3 ≤ pmfExp (PMF.uniformOfFintype Bool) (fun b =>
      pmfExp (PMF.uniformOfFintype (V → Bool)) (fun c =>
        wt (roundColoring e b c x) (roundColoring e b c y))) := by
  have hne : e.out.1 ≠ e.out.2 := by
    intro h; apply he; rw [← Quot.out_eq e]; exact (Sym2.mk_isDiag_iff).2 h
  have hN : (0 : ℝ) < Fintype.card (V → Bool) := by exact_mod_cast Fintype.card_pos
  simp only [pmfExp_uniform', Fintype.card_bool, Fintype.sum_bool]
  have rc : ∀ b c z, roundColoring e b c z =
      if z = e.out.1 then b else if z = e.out.2 then !b else c z := fun _ _ _ => rfl
  simp only [rc]
  generalize e.out.1 = u at hne ⊢
  generalize e.out.2 = w at hne ⊢
  by_cases hxu : x = u <;> by_cases hxw : x = w <;> by_cases hyu : y = u <;>
    by_cases hyw : y = w
  all_goals (try subst hxu)
  all_goals (try subst hxw)
  all_goals (try subst hyu)
  all_goals (try subst hyw)
  all_goals (try (exact absurd rfl hne))
  all_goals (try (exact absurd rfl hxy))
  all_goals simp only [if_true, if_false, Bool.not_true, Bool.not_false, ite_true, ite_false,
    ne_eq, not_false_eq_true, *]
  all_goals (try simp only [caseA x y hxy, caseB, caseC, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul])
  all_goals (try simp only [wt])
  all_goals (try norm_num)
  all_goals (try field_simp)
  all_goals (try norm_num)


end PM

section TP
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

def ValidC (E : Finset (Sym2 V)) (C : Finset (V × V)) : Prop :=
  (∀ c ∈ C, s(c.1, c.2) ∈ E ∧ c.1 ≠ c.2) ∧ (∀ c ∈ C, ∀ c' ∈ C, c.1 = c'.1 → c = c')

lemma partMax_nonneg' (p : Finset (Sym2 V)) (v : Sym2 V → ℝ) (hv : ∀ e, 0 ≤ v e) :
    0 ≤ partMax p v := by
  unfold partMax
  split_ifs with h
  · obtain ⟨e, he⟩ := h
    exact (hv e).trans (Finset.le_sup' v he)
  · exact le_refl _

lemma round_lower (E : Finset (Sym2 V)) (col : V → Bool) (C : Finset (V × V)) (hC : ValidC E C)
    (v : Sym2 V → ℝ) (hv : ∀ e, 0 ≤ v e) (Q : Finset (Finset (Sym2 V)))
    (hQ : IsPartitionOf (blueEdges E col) Q) :
    ∑ c ∈ C, v s(c.1, c.2) * (if col c.1 = true ∧ col c.2 = false then 1 else 0) +
      partitionValue Q v ≤ partitionValue (roundParts E col ∪ Q) v := by
  have hdisj : Disjoint (roundParts E col) Q := by
    rw [Finset.disjoint_left]
    intro p hp hpQ
    obtain ⟨⟨x, hx, rfl⟩, ⟨f, hf⟩⟩ := rp_mem_roundParts.1 hp
    have hxf := (rp_mem_redPart.1 hf).2.1
    have := (rp_mem_blue.1 ((hQ.1 _ hpQ).2 hf)).2 x hxf
    simp_all
  unfold partitionValue
  rw [Finset.sum_union hdisj]
  refine add_le_add ?_ le_rfl
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  set CR := C.filter (fun c => col c.1 = true ∧ col c.2 = false)
  have hmem : ∀ c ∈ CR, s(c.1, c.2) ∈ redPart E col c.1 := by
    intro c hc
    have hf := Finset.mem_filter.1 hc
    rw [rp_mem_redPart]
    exact ⟨(hC.1 c hf.1).1, Sym2.mem_mk_left _ _, c.2, Sym2.mem_mk_right _ _, hf.2.2⟩
  calc ∑ c ∈ CR, v s(c.1, c.2) ≤ ∑ c ∈ CR, partMax (redPart E col c.1) v := by
        apply Finset.sum_le_sum
        intro c hc
        unfold partMax
        rw [dif_pos ⟨_, hmem c hc⟩]
        exact Finset.le_sup' v (hmem c hc)
    _ = ∑ p ∈ CR.image (fun c => redPart E col c.1), partMax p v := by
        rw [Finset.sum_image]
        intro c hc c' hc' h
        have hc1 := hmem c hc
        rw [show redPart E col c.1 = redPart E col c'.1 from h] at hc1
        have hx := (Finset.mem_filter.1 hc).2.1
        have hx' := (Finset.mem_filter.1 hc').2.1
        have := rp_red_eq hx (Sym2.mem_mk_left _ _) hc1 hx'
        exact hC.2 c (Finset.mem_filter.1 hc).1 c' (Finset.mem_filter.1 hc').1 this
    _ ≤ ∑ p ∈ roundParts E col, partMax p v := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hp
          rw [rp_mem_roundParts]
          exact ⟨⟨c.1, (Finset.mem_filter.1 hc).2.1, rfl⟩, ⟨_, hmem c hc⟩⟩
        · intro p _ _; exact partMax_nonneg' p v hv

lemma wt_split (a b : Bool) (t : ℝ) :
    t * wt a b = t * (if a = true ∧ b = false then 1 else 0) +
      t * (if a = false ∧ b = false then 1 else 0) / 3 := by
  unfold wt
  cases a <;> cases b <;> simp <;> ring

lemma claim_main (v : Sym2 V → ℝ) (hv : ∀ e, 0 ≤ v e) : ∀ (n : ℕ) (E : Finset (Sym2 V)),
    E.card = n → ∀ C : Finset (V × V), ValidC E C →
      ∑ c ∈ C, v s(c.1, c.2) ≤ 3 * pmfExp (partitionPMF E) (fun P => partitionValue P v) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro E hE C hC
  rw [partitionPMF]
  split_ifs with h
  · simp only [pmfExp_bind', pmfExp_map']
    -- lower bound for the innermost expectation
    have hinner : ∀ (e : {e // e ∈ properEdges E}) (b : Bool) (c : V → Bool),
        ∑ q ∈ C, v s(q.1, q.2) * wt (roundColoring e.1 b c q.1) (roundColoring e.1 b c q.2) ≤
          pmfExp (partitionPMF (blueEdges E (roundColoring e.1 b c)))
            (fun Q => partitionValue (roundParts E (roundColoring e.1 b c) ∪ Q) v) := by
      intro e b c
      set col := roundColoring e.1 b c
      set E' := blueEdges E col
      have hlt : E'.card < n := hE ▸ blueEdges_card_lt E e b c
      set CB := C.filter (fun q => col q.1 = false ∧ col q.2 = false)
      have hCB : ValidC E' CB := by
        refine ⟨fun q hq => ?_, fun q hq q' hq' h => hC.2 q (Finset.mem_filter.1 hq).1 q'
          (Finset.mem_filter.1 hq').1 h⟩
        have hf := Finset.mem_filter.1 hq
        have hqC := hf.1
        have h1 := hf.2.1
        have h2 := hf.2.2
        refine ⟨?_, (hC.1 q hqC).2⟩
        rw [rp_mem_blue]
        refine ⟨(hC.1 q hqC).1, fun y hy => ?_⟩
        rcases Sym2.mem_iff.1 hy with rfl | rfl
        · exact h1
        · exact h2
      have hIH := ih _ hlt E' rfl CB hCB
      have hmono := pmfExp_mono' (partitionPMF E')
        (fun Q => ∑ q ∈ C, v s(q.1, q.2) * (if col q.1 = true ∧ col q.2 = false then 1 else 0) +
          partitionValue Q v)
        (fun Q => partitionValue (roundParts E col ∪ Q) v)
        (fun Q hQ => round_lower E col C hC v hv Q (rp_main _ E' rfl Q hQ).1)
      rw [pmfExp_add', pmfExp_const'] at hmono
      refine le_trans (le_of_eq ?_) (le_trans (add_le_add le_rfl (by rw [← Finset.sum_div]; linarith : ∑ q ∈ CB,
        v s(q.1, q.2) / 3 ≤ pmfExp (partitionPMF E') fun P => partitionValue P v)) hmono)
      simp only [wt_split, Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro q _
      split_ifs <;> simp
    have hbound : ∀ e : {e // e ∈ properEdges E},
        (∑ q ∈ C, v s(q.1, q.2)) / 3 ≤
        pmfExp (PMF.uniformOfFintype Bool) (fun b => pmfExp (PMF.uniformOfFintype (V → Bool))
          (fun c => pmfExp (partitionPMF (blueEdges E (roundColoring e.1 b c)))
            (fun Q => partitionValue (roundParts E (roundColoring e.1 b c) ∪ Q) v))) := by
      intro e
      have hnd : ¬ e.1.IsDiag := (Finset.mem_filter.1 e.2).2
      calc (∑ q ∈ C, v s(q.1, q.2)) / 3 = ∑ q ∈ C, v s(q.1, q.2) * (1 / 3) := by
            rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro q _; ring
        _ ≤ ∑ q ∈ C, v s(q.1, q.2) * pmfExp (PMF.uniformOfFintype Bool) (fun b =>
              pmfExp (PMF.uniformOfFintype (V → Bool)) (fun c =>
                wt (roundColoring e.1 b c q.1) (roundColoring e.1 b c q.2))) := by
            apply Finset.sum_le_sum
            intro q hq
            exact mul_le_mul_of_nonneg_left (round_prob e.1 hnd q.1 q.2 (hC.1 q hq).2) (hv _)
        _ = pmfExp (PMF.uniformOfFintype Bool) (fun b =>
              pmfExp (PMF.uniformOfFintype (V → Bool)) (fun c =>
                ∑ q ∈ C, v s(q.1, q.2) * wt (roundColoring e.1 b c q.1)
                  (roundColoring e.1 b c q.2))) := by
            simp only [pmfExp_sum', pmfExp_mul']
        _ ≤ _ := by
            apply pmfExp_mono'; intro b _
            apply pmfExp_mono'; intro c _
            exact hinner e b c
    have := pmfExp_mono' (PMF.uniformOfFinset (properEdges E).attach (by simpa using h))
      (fun _ => (∑ q ∈ C, v s(q.1, q.2)) / 3) _ (fun e _ => hbound e)
    rw [pmfExp_const'] at this
    linarith
  · have hC0 : C = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro q hq
      apply h
      refine ⟨s(q.1, q.2), ?_⟩
      simp only [properEdges, Finset.mem_filter]
      exact ⟨(hC.1 q hq).1, fun hd => (hC.1 q hq).2 (Sym2.mk_isDiag_iff.1 hd)⟩
    subst hC0
    rw [pmfExp_pure']
    simp [partitionValue]

theorem graphic_three_partition_property_core {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    IsPartitionScheme G.edgeFinset (partitionPMF G.edgeFinset) 3 := by
  refine ⟨fun P hP => rp_main _ _ rfl P hP, fun v hv => ?_⟩
  unfold OPT
  obtain ⟨S, hS, hSeq⟩ := Finset.exists_mem_eq_sup' ⟨∅, empty_mem_acyclicSubsets G.edgeFinset⟩
    (fun S => ∑ e ∈ S, v e)
  rw [hSeq]
  unfold acyclicSubsets at hS
  obtain ⟨hSE, hSac⟩ := Finset.mem_filter.1 hS
  rw [Finset.mem_powerset] at hSE
  have hloop : ∀ f ∈ S, ¬ f.IsDiag := by
    intro f hf
    exact G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.1 (hSE hf))
  obtain ⟨C, hC1, hC2, hCsum⟩ := forest_orient S hSac hloop v
  rw [← hCsum]
  exact claim_main v hv _ G.edgeFinset rfl C
    ⟨fun c hc => ⟨hSE (hC1 c hc).1, (hC1 c hc).2⟩, hC2⟩

end TP


end TPpart

theorem graphic_matroid_secretary_competitive_core {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : Sym2 V → ℝ) (hv : ∀ e, 0 ≤ v e) :
    (∀ P ∈ (partitionPMF G.edgeFinset).support, ∀ π : Equiv.Perm (Fin G.edgeFinset.card),
        partitionSecretaryOutput G.edgeFinset v P π ⊆ G.edgeFinset ∧
          IsAcyclicSet (partitionSecretaryOutput G.edgeFinset v P π)) ∧
      OPT G.edgeFinset v ≤
        3 * Real.exp 1 * expectedAlgValue G.edgeFinset v (partitionPMF G.edgeFinset) := by
  have h := partition_property_competitive_core G (partitionPMF G.edgeFinset) 3
    (graphic_three_partition_property_core G) v hv
  refine ⟨h.1, ?_⟩
  have := h.2
  linarith [show Real.exp 1 * 3 * expectedAlgValue G.edgeFinset v (partitionPMF G.edgeFinset) =
    3 * Real.exp 1 * expectedAlgValue G.edgeFinset v (partitionPMF G.edgeFinset) by ring]

end SecretaryWD.Graphic

open SecretaryWD.Graphic


theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : Sym2 V → ℝ) (hv : ∀ e, 0 ≤ v e) :
    (∀ P ∈ (partitionPMF G.edgeFinset).support, ∀ π : Equiv.Perm (Fin G.edgeFinset.card),
        partitionSecretaryOutput G.edgeFinset v P π ⊆ G.edgeFinset ∧
          IsAcyclicSet (partitionSecretaryOutput G.edgeFinset v P π)) ∧
      OPT G.edgeFinset v ≤
        3 * Real.exp 1 * expectedAlgValue G.edgeFinset v (partitionPMF G.edgeFinset) := by
  exact graphic_matroid_secretary_competitive_core G v hv
