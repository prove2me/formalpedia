-- Prove2me | solution 1 for SecretaryWD.DiscUpper.class_payoff_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T08:22:34.843623+00:00
-- url     : https://prove2.me/submissions/41f8081e-05b1-4212-b137-89f7a3f96e3b

import Mathlib
import Definitions.Def_SecretaryWD_DiscUpper_Algorithm



namespace SecretaryWD.DiscUpper

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


theorem cs_generic (m : ℕ) (hm : 1 ≤ m) (k : Fin m → L) (hk : Function.Injective k) :
    (m.factorial : ℝ) / Real.exp 1 ≤
        ((Finset.univ.filter fun σ : Equiv.Perm (Fin m) =>
            ∃ t : Fin m, classicalSecretary m (fun s => k (σ s)) = some t ∧
              ∀ e : Fin m, k e ≤ k (σ t)).card : ℝ) := by
  have hf0 : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  suffices H : 1 / Real.exp 1 ≤ (1 / (m.factorial : ℝ)) *
        ((Finset.univ.filter fun σ : Equiv.Perm (Fin m) =>
            ∃ t : Fin m, classicalSecretary m (fun s => k (σ s)) = some t ∧
              ∀ e : Fin m, k e ≤ k (σ t)).card : ℝ) by
    have := mul_le_mul_of_nonneg_left H hf0.le
    rw [← mul_assoc, mul_one_div_cancel hf0.ne', one_mul] at this
    calc (m.factorial : ℝ) / Real.exp 1 = m.factorial * (1 / Real.exp 1) := by ring
      _ ≤ _ := this
  obtain ⟨e₀, _, he₀⟩ := Finset.exists_max_image Finset.univ k ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  replace he₀ : ∀ e, k e ≤ k e₀ := fun e => he₀ e (Finset.mem_univ _)
  set r := Nat.floor ((m : ℝ) / Real.exp 1) with hr
  have hfilt : (Finset.univ.filter fun σ : Equiv.Perm (Fin m) =>
            ∃ t : Fin m, classicalSecretary m (fun s => k (σ s)) = some t ∧
              ∀ e : Fin m, k e ≤ k (σ t)) = Finset.univ.filter (SuccP k r) := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  rw [hfilt]
  have hmain := an_main m hm r hr
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
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

lemma tieKey_inj {k : ℕ} (v : Fin k → ℝ) : Function.Injective (tieKey v) := by
  intro a b h
  have := congrArg (fun p => OrderDual.ofDual (ofLex p).2) h
  simpa [tieKey] using this

lemma tieKey_le {k : ℕ} (v : Fin k → ℝ) (a b : Fin k) (h : tieKey v a ≤ tieKey v b) :
    v a ≤ v b := by
  unfold tieKey at h
  rw [Prod.Lex.toLex_le_toLex] at h
  rcases h with h | ⟨h, _⟩
  · exact h.le
  · exact h.le

/-- extension of a permutation of `Fin s.card` to `Fin n`. -/
noncomputable def extP {n : ℕ} (s : Finset (Fin n)) (σ : Equiv.Perm (Fin s.card)) :
    Equiv.Perm (Fin n) :=
  σ.extendDomain (s.orderIsoOfFin rfl).toEquiv

lemma extP_apply {n : ℕ} (s : Finset (Fin n)) (σ : Equiv.Perm (Fin s.card)) (k : Fin s.card) :
    extP s σ (s.orderEmbOfFin rfl k) = s.orderEmbOfFin rfl (σ k) := by
  unfold extP
  rw [← Finset.coe_orderIsoOfFin_apply, ← Finset.coe_orderIsoOfFin_apply]
  exact Equiv.Perm.extendDomain_apply_image σ (s.orderIsoOfFin rfl).toEquiv k


lemma pay_nonneg {n : ℕ} (d v : Fin n → ℝ) (hd : ∀ t, 0 ≤ d t) (hv : ∀ e, 0 ≤ v e) (c : ℕ)
    (π : Equiv.Perm (Fin n)) : 0 ≤ classPayoff d v c π := by
  unfold classPayoff
  split
  · exact le_rfl
  · exact mul_nonneg (hd _) (hv _)

lemma pay_success {n : ℕ} (d v : Fin n → ℝ) (c : ℕ) (π : Equiv.Perm (Fin n))
    (σ : Equiv.Perm (Fin (discountClass d c).card)) (t : Fin (discountClass d c).card)
    (ht : classicalSecretary (discountClass d c).card
      (fun k => tieKey v (π ((discountClass d c).orderEmbOfFin rfl (σ k)))) = some t) :
    classPayoff d v c (π * extP (discountClass d c) σ) =
      d ((discountClass d c).orderEmbOfFin rfl t) *
        v (π ((discountClass d c).orderEmbOfFin rfl (σ t))) := by
  unfold classPayoff
  have hx : (fun k => tieKey v ((π * extP (discountClass d c) σ)
      ((discountClass d c).orderEmbOfFin rfl k))) =
      (fun k => tieKey v (π ((discountClass d c).orderEmbOfFin rfl (σ k)))) := by
    funext k; rw [Equiv.Perm.mul_apply, extP_apply]
  rw [hx, ht]
  simp only [Equiv.Perm.mul_apply, extP_apply]

theorem cpl_core (n : ℕ) (d v : Fin n → ℝ)
    (hd : ∀ t, 0 ≤ d t) (hv : ∀ e, 0 ≤ v e) (c : ℕ) :
    optClass d v c / (2 * Real.exp 1) ≤ classValue d v c := by
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  unfold optClass classValue uniformAvg
  have hnf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  rcases Nat.eq_zero_or_pos (discountClass d c).card with hm0 | hm
  · have hs : discountClass d c = ∅ := Finset.card_eq_zero.1 hm0
    simp only [hs, Finset.sum_empty, Finset.sum_const_zero, mul_zero, zero_div]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun π _ => pay_nonneg d v hd hv c π)
  set lo := dmax d / 2 ^ c with hlo
  have hsm : ∀ i ∈ discountClass d c, lo < d i ∧ d i ≤ 2 * lo := by
    intro i hi
    unfold discountClass at hi
    rw [Finset.mem_filter] at hi
    refine ⟨hi.2.1, ?_⟩
    rw [hlo]; have := hi.2.2; rw [mul_div_assoc] at this; exact this
  have hemb : ∀ k, (discountClass d c).orderEmbOfFin rfl k ∈ discountClass d c :=
    fun k => Finset.orderEmbOfFin_mem _ _ k
  have hlo0 : 0 ≤ lo := by
    have := hsm _ (hemb ⟨0, hm⟩); linarith
  have hne : (Finset.univ : Finset (Fin (discountClass d c).card)).Nonempty :=
    ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  obtain ⟨M, hM1, hM2⟩ : ∃ M : Equiv.Perm (Fin n) → ℝ,
      (∀ π k, v (π ((discountClass d c).orderEmbOfFin rfl k)) ≤ M π) ∧
      (∀ π, ∃ k, M π = v (π ((discountClass d c).orderEmbOfFin rfl k))) := by
    refine ⟨fun π => Finset.univ.sup' hne (fun k => v (π ((discountClass d c).orderEmbOfFin rfl k))),
      fun π k => Finset.le_sup' (fun k => v (π ((discountClass d c).orderEmbOfFin rfl k)))
        (Finset.mem_univ k), fun π => ?_⟩
    obtain ⟨k, _, hk⟩ := Finset.exists_mem_eq_sup' hne
      (fun k => v (π ((discountClass d c).orderEmbOfFin rfl k)))
    exact ⟨k, hk⟩
  have hM0 : ∀ π, 0 ≤ M π := fun π => (hv _).trans (hM1 π ⟨0, hm⟩)
  -- (A)
  have hA : ∀ π : Equiv.Perm (Fin n), (∑ t ∈ discountClass d c,
      if IsOptTime d v π t then d t * v (π t) else 0) ≤ 2 * lo * M π := by
    intro π
    by_cases h : ∃ t ∈ discountClass d c, IsOptTime d v π t
    · obtain ⟨t, hts, ht⟩ := h
      rw [Finset.sum_eq_single t]
      · rw [if_pos ht]
        have : t ∈ Set.range ((discountClass d c).orderEmbOfFin rfl) := by
          rw [Finset.range_orderEmbOfFin]; exact hts
        obtain ⟨k, rfl⟩ := this
        exact mul_le_mul (hsm _ hts).2 (hM1 π k) (hv _) (by linarith)
      · intro b _ hbt
        rw [if_neg]
        intro hb
        rcases lt_trichotomy b t with hlt | heq | hgt
        · exact absurd (ht.2 b hlt) (not_lt.2 (hb.1 t))
        · exact hbt heq
        · exact absurd (hb.2 t hgt) (not_lt.2 (ht.1 b))
      · intro hts'; exact absurd hts hts'
    · push_neg at h
      rw [Finset.sum_eq_zero (fun t ht => if_neg (h t ht))]
      exact mul_nonneg (by linarith) (hM0 π)
  -- (B)
  have hB : ∀ π : Equiv.Perm (Fin n),
      ((discountClass d c).card.factorial : ℝ) / Real.exp 1 * (lo * M π) ≤
        ∑ σ : Equiv.Perm (Fin (discountClass d c).card),
          classPayoff d v c (π * extP (discountClass d c) σ) := by
    intro π
    set K : Fin (discountClass d c).card → Lex (ℝ × (Fin n)ᵒᵈ) :=
      fun k => tieKey v (π ((discountClass d c).orderEmbOfFin rfl k)) with hK
    have hKi : Function.Injective K := fun a b h =>
      ((discountClass d c).orderEmbOfFin rfl).injective (π.injective (tieKey_inj v h))
    have hcs := cs_generic _ hm K hKi
    calc ((discountClass d c).card.factorial : ℝ) / Real.exp 1 * (lo * M π)
        ≤ ((Finset.univ.filter fun σ : Equiv.Perm (Fin (discountClass d c).card) =>
            ∃ t, classicalSecretary _ (fun s => K (σ s)) = some t ∧
              ∀ e, K e ≤ K (σ t)).card : ℝ) * (lo * M π) :=
          mul_le_mul_of_nonneg_right hcs (mul_nonneg hlo0 (hM0 π))
      _ ≤ ∑ σ ∈ (Finset.univ.filter fun σ : Equiv.Perm (Fin (discountClass d c).card) =>
            ∃ t, classicalSecretary _ (fun s => K (σ s)) = some t ∧
              ∀ e, K e ≤ K (σ t)), classPayoff d v c (π * extP (discountClass d c) σ) := by
          rw [← nsmul_eq_mul]
          apply Finset.card_nsmul_le_sum
          intro σ hσ
          rw [Finset.mem_filter] at hσ
          obtain ⟨t, ht, hmax⟩ := hσ.2
          rw [pay_success d v c π σ t ht]
          obtain ⟨k0, hk0⟩ := hM2 π
          have h1 : M π ≤ v (π ((discountClass d c).orderEmbOfFin rfl (σ t))) := by
            rw [hk0]; exact tieKey_le v _ _ (hmax k0)
          exact mul_le_mul (hsm _ (hemb t)).1.le h1 (hM0 π) (hd _)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun σ _ _ => pay_nonneg d v hd hv c _)
  -- (C)
  have hC : ∑ π : Equiv.Perm (Fin n), classPayoff d v c π =
      (1 / ((discountClass d c).card.factorial : ℝ)) *
        ∑ π : Equiv.Perm (Fin n), ∑ σ : Equiv.Perm (Fin (discountClass d c).card),
          classPayoff d v c (π * extP (discountClass d c) σ) := by
    rw [Finset.sum_comm]
    have : ∀ σ : Equiv.Perm (Fin (discountClass d c).card),
        ∑ π : Equiv.Perm (Fin n), classPayoff d v c (π * extP (discountClass d c) σ) =
          ∑ π : Equiv.Perm (Fin n), classPayoff d v c π := fun σ =>
      Equiv.sum_comp (Equiv.mulRight (extP (discountClass d c) σ)) (classPayoff d v c)
    rw [Finset.sum_congr rfl (fun σ _ => this σ), Finset.sum_const, Finset.card_univ,
      Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
    have : (0 : ℝ) < (discountClass d c).card.factorial := by exact_mod_cast Nat.factorial_pos _
    field_simp
  rw [hC]
  set S := ∑ π : Equiv.Perm (Fin n), lo * M π with hS
  have hA' := Finset.sum_le_sum (fun π (_ : π ∈ Finset.univ) => hA π)
  have hB' := Finset.sum_le_sum (fun π (_ : π ∈ Finset.univ) => hB π)
  rw [← Finset.mul_sum] at hB'
  have hA'' : ∑ π : Equiv.Perm (Fin n), 2 * lo * M π = 2 * S := by
    rw [hS, Finset.mul_sum]; apply Finset.sum_congr rfl; intro π _; ring
  rw [hA''] at hA'
  have hmf : (0 : ℝ) < (discountClass d c).card.factorial := by exact_mod_cast Nat.factorial_pos _
  have key : (∑ π : Equiv.Perm (Fin n), ∑ t ∈ discountClass d c,
      if IsOptTime d v π t then d t * v (π t) else 0) / (2 * Real.exp 1) ≤
      (1 / ((discountClass d c).card.factorial : ℝ)) *
        ∑ π : Equiv.Perm (Fin n), ∑ σ : Equiv.Perm (Fin (discountClass d c).card),
          classPayoff d v c (π * extP (discountClass d c) σ) := by
    calc _ ≤ 2 * S / (2 * Real.exp 1) := div_le_div_of_nonneg_right hA' (by positivity)
      _ = (1 / ((discountClass d c).card.factorial : ℝ)) *
          (((discountClass d c).card.factorial : ℝ) / Real.exp 1 * S) := by
          field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hB' (by positivity)
  calc _ = 1 / (n.factorial : ℝ) * ((∑ π : Equiv.Perm (Fin n), ∑ t ∈ discountClass d c,
      if IsOptTime d v π t then d t * v (π t) else 0) / (2 * Real.exp 1)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left key (by positivity)

end SecretaryWD.DiscUpper

open SecretaryWD.DiscUpper


theorem solution (n : ℕ) (d v : Fin n → ℝ)
    (hd : ∀ t, 0 ≤ d t) (hv : ∀ e, 0 ≤ v e) (c : ℕ) (hc : 1 ≤ c) :
    optClass d v c / (2 * Real.exp 1) ≤ classValue d v c := by
  exact cpl_core n d v hd hv c
