-- Prove2me | solution 1 for SecretaryWD.Graphic.classical_secretary_guarantee
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T07:09:53.116709+00:00
-- url     : https://prove2.me/submissions/ae6c39c4-59b1-47ad-9962-9d6985995621

import Mathlib
import Definitions.Def_SecretaryWD_DiscUpper_ClassicalSecretary

set_option autoImplicit false

namespace DA01

/-! ## Analytic part -/

lemma log_succ_div_le (t : ℝ) (ht : 0 < t) :
    Real.log ((t + 1) / t) ≤ 1 / (2 * t) + 1 / (2 * (t + 1)) := by
  have hy : 0 < (t + 1) / t := by positivity
  have h1 : (1 : ℝ) ≤ (t + 1) / t := by rw [le_div_iff₀ ht]; linarith
  have := Real.self_le_sinh_iff.2 (Real.log_nonneg h1)
  rw [Real.sinh_log hy] at this
  have e : ((t + 1) / t - ((t + 1) / t)⁻¹) / 2 = 1 / (2 * t) + 1 / (2 * (t + 1)) := by
    field_simp
    ring
  linarith

lemma harm_trap (r : ℕ) (hr : 1 ≤ r) (m : ℕ) (hrm : r ≤ m) :
    Real.log ((m : ℝ) / r) + 1 / (2 * (r : ℝ)) - 1 / (2 * (m : ℝ)) ≤
      ∑ t ∈ Finset.Ico r m, (1 / (t : ℝ)) := by
  induction m, hrm using Nat.le_induction with
  | base =>
    have : (r : ℝ) ≠ 0 := by positivity
    simp [this]
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top hn]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le hr hn)
    have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
    have key := log_succ_div_le n hn0
    have hl : Real.log (((n + 1 : ℕ) : ℝ) / r) =
        Real.log ((n : ℝ) / r) + Real.log (((n : ℝ) + 1) / n) := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      congr 1
      push_cast
      field_simp
    have h2 : (1 : ℝ) / n = 1 / (2 * n) + 1 / (2 * n) := by ring
    rw [hl]
    push_cast
    linarith

lemma floor_facts (m : ℕ) (h3 : 3 ≤ m) :
    1 ≤ ⌊(m : ℝ) / Real.exp 1⌋₊ ∧ ⌊(m : ℝ) / Real.exp 1⌋₊ < m := by
  have hE1 : 2.7182818283 < Real.exp 1 := Real.exp_one_gt_d9
  have hEpos : 0 < Real.exp 1 := Real.exp_pos 1
  have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast h3
  constructor
  · rw [Nat.one_le_floor_iff, le_div_iff₀ hEpos]
    have : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    linarith
  · have h1 : ((⌊(m : ℝ) / Real.exp 1⌋₊ : ℕ) : ℝ) ≤ m / Real.exp 1 :=
      Nat.floor_le (by positivity)
    have h2 : (m : ℝ) / Real.exp 1 < m := by
      rw [div_lt_iff₀ hEpos]; nlinarith
    exact_mod_cast lt_of_le_of_lt h1 h2

lemma analytic (m : ℕ) (hm : 3 ≤ m) :
    1 / Real.exp 1 ≤ ((⌊(m : ℝ) / Real.exp 1⌋₊ : ℕ) / (m : ℝ)) *
      ∑ t ∈ Finset.Ico ⌊(m : ℝ) / Real.exp 1⌋₊ m, (1 / (t : ℝ)) := by
  obtain ⟨hr1, hrm⟩ := floor_facts m hm
  set E := Real.exp 1 with hE
  set r := ⌊(m : ℝ) / E⌋₊ with hr
  have hE1 : 2.7182818283 < E := Real.exp_one_gt_d9
  have hE2 : E < 2.7182818286 := Real.exp_one_lt_d9
  have hEpos : 0 < E := by linarith
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hfl1 : (r : ℝ) ≤ m / E := Nat.floor_le (by positivity)
  have hfl2 : (m : ℝ) / E < r + 1 := Nat.lt_floor_add_one _
  have hEr : E * r ≤ m := by rw [le_div_iff₀ hEpos] at hfl1; linarith
  have hEr2 : (m : ℝ) < E * (r + 1) := by rw [div_lt_iff₀ hEpos] at hfl2; linarith
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hS := harm_trap r hr1 m hrm.le
  have hrpos : (0 : ℝ) < r := by linarith
  have hlog : 2 - E * r / m ≤ Real.log ((m : ℝ) / r) := by
    have h1 := Real.log_le_sub_one_of_pos (show 0 < E * r / m by positivity)
    have h2 : Real.log (E * r / m) = 1 - Real.log ((m : ℝ) / r) := by
      rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        hE, Real.log_exp, Real.log_div (by positivity) (by positivity)]
      ring
    linarith
  have hS2 : 2 - E * r / m + 1 / (2 * (r : ℝ)) - 1 / (2 * (m : ℝ)) ≤
      ∑ t ∈ Finset.Ico r m, (1 / (t : ℝ)) := by linarith
  have key : 1 / E ≤ (r / m) * (2 - E * r / m + 1 / (2 * (r : ℝ)) - 1 / (2 * (m : ℝ))) := by
    have eq : (r / m) * (2 - E * r / m + 1 / (2 * (r : ℝ)) - 1 / (2 * (m : ℝ))) =
        (E * r * (2 * m - E * r) + E * (m - r) / 2) / (E * m ^ 2) := by
      field_simp
      ring
    rw [eq, div_le_div_iff₀ hEpos (by positivity)]
    suffices h : (m : ℝ) ^ 2 ≤ E * r * (2 * m - E * r) + E * (m - r) / 2 by nlinarith
    rcases (show r = 1 ∨ 2 ≤ r by omega) with h1 | h2
    · have hm6 : (m : ℝ) < 6 := by rw [h1] at hEr2; push_cast at hEr2; linarith
      have hm6' : m < 6 := by exact_mod_cast hm6
      rw [h1]
      push_cast
      interval_cases m <;> nlinarith [mul_pos (sub_pos.2 hE1) (sub_pos.2 hE2)]
    · have h2R : (2 : ℝ) ≤ r := by exact_mod_cast h2
      nlinarith [mul_nonneg (sub_nonneg.2 hEr) (sub_nonneg.2 hEr2.le),
        mul_nonneg (by linarith : (0 : ℝ) ≤ E - 1) (by linarith : (0 : ℝ) ≤ r - 2),
        mul_nonneg hEpos.le (show 0 ≤ (E - 1) * r - (m - E * r) by
          nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ E - 1) (by linarith : (0 : ℝ) ≤ r - 2)])]
  calc 1 / E ≤ _ := key
    _ ≤ _ := mul_le_mul_of_nonneg_left hS2 (by positivity)


section comb
variable {α : Type*} [LinearOrder α]

def B {m : ℕ} (k : Fin m → α) (es t s : Fin m) : Finset (Equiv.Perm (Fin m)) :=
  Finset.univ.filter (fun σ => σ t = es ∧ ∀ u : Fin m, u < t → u ≠ s → k (σ u) < k (σ s))

lemma mem_B_swap {m : ℕ} (k : Fin m → α) (es t s s' : Fin m) (hs : s < t) (hs' : s' < t)
    (σ : Equiv.Perm (Fin m)) (h : σ ∈ B k es t s) : σ * Equiv.swap s s' ∈ B k es t s' := by
  simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (ne_of_gt hs) (ne_of_gt hs')]
    exact h1
  · intro u hu hus'
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
    by_cases hus : u = s
    · rw [hus, Equiv.swap_apply_left]
      exact h2 s' hs' (fun h => hus' (hus.trans h.symm))
    · rw [Equiv.swap_apply_of_ne_of_ne hus hus']
      exact h2 u hu hus

lemma card_B_eq {m : ℕ} (k : Fin m → α) (es t s s' : Fin m) (hs : s < t) (hs' : s' < t) :
    (B k es t s).card = (B k es t s').card := by
  apply Finset.card_bij (fun σ _ => σ * Equiv.swap s s')
  · intro σ hσ
    exact mem_B_swap k es t s s' hs hs' σ hσ
  · intro a _ b _ h
    exact mul_right_cancel h
  · intro τ hτ
    refine ⟨τ * Equiv.swap s s', ?_, ?_⟩
    · have := mem_B_swap k es t s' s hs' hs τ hτ
      rwa [Equiv.swap_comm] at this
    · rw [mul_assoc, Equiv.swap_mul_self, mul_one]

lemma C_eq {m : ℕ} (k : Fin m → α) (hk : Function.Injective k) (es t : Fin m)
    (ht : 0 < (t : ℕ)) :
    Finset.univ.filter (fun σ : Equiv.Perm (Fin m) => σ t = es) =
      (Finset.Iio t).biUnion (fun s => B k es t s) := by
  ext σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, B,
    Finset.mem_Iio]
  constructor
  · intro h
    have hne : (Finset.Iio t).Nonempty :=
      ⟨⟨0, lt_of_le_of_lt (Nat.zero_le _) t.isLt⟩, Finset.mem_Iio.2 (Fin.lt_def.2 ht)⟩
    obtain ⟨s, hs, hmax⟩ := Finset.exists_max_image _ (fun u => k (σ u)) hne
    rw [Finset.mem_Iio] at hs
    refine ⟨s, hs, h, fun u hu hus =>
      lt_of_le_of_ne (hmax u (Finset.mem_Iio.2 hu)) (fun heq => hus (σ.injective (hk heq)))⟩
  · rintro ⟨s, _, h, _⟩
    exact h

lemma card_C_eq {m : ℕ} (k : Fin m → α) (hk : Function.Injective k) (es t s : Fin m)
    (hs : s < t) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin m) => σ t = es)).card =
      (t : ℕ) * (B k es t s).card := by
  have ht : 0 < (t : ℕ) := lt_of_le_of_lt (Nat.zero_le _) (Fin.lt_def.1 hs)
  rw [C_eq k hk es t ht, Finset.card_biUnion]
  · rw [Finset.sum_congr rfl (fun s' hs' => card_B_eq k es t s' s (Finset.mem_Iio.1 hs') hs)]
    rw [Finset.sum_const, smul_eq_mul, Fin.card_Iio]
  · intro a ha b hb hab
    rw [Function.onFun, Finset.disjoint_left]
    intro σ h1 h2
    simp only [Finset.coe_Iio, Set.mem_Iio] at ha hb
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact lt_asymm (h1.2 b hb (Ne.symm hab)) (h2.2 a ha hab)

lemma card_fiber (n : ℕ) (t e e' : Fin n) :
    (Finset.univ.filter (fun π : Equiv.Perm (Fin n) => π t = e)).card =
    (Finset.univ.filter (fun π : Equiv.Perm (Fin n) => π t = e')).card := by
  apply Finset.card_bij (fun π _ => Equiv.swap e e' * π)
  · intro π hπ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ ⊢
    simp [Equiv.Perm.mul_apply, hπ]
  · intro a _ b _ h
    exact mul_left_cancel h
  · intro b hb
    refine ⟨Equiv.swap e e' * b, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      simp [Equiv.Perm.mul_apply, hb]
    · exact Equiv.swap_mul_self_mul e e' b

lemma card_fiber_mul (n : ℕ) (t e : Fin n) :
    (n : ℝ) * ((Finset.univ.filter (fun π : Equiv.Perm (Fin n) => π t = e)).card : ℝ)
      = (n.factorial : ℝ) := by
  have h1 : (Finset.univ : Finset (Equiv.Perm (Fin n))).card =
      ∑ e' ∈ (Finset.univ : Finset (Fin n)),
        (Finset.univ.filter (fun π : Equiv.Perm (Fin n) => π t = e')).card :=
    Finset.card_eq_sum_card_fiberwise (fun π _ => Finset.mem_univ (π t))
  have h2 : ∑ e' ∈ (Finset.univ : Finset (Fin n)),
        (Finset.univ.filter (fun π : Equiv.Perm (Fin n) => π t = e')).card
      = n * (Finset.univ.filter (fun π : Equiv.Perm (Fin n) => π t = e)).card := by
    rw [Finset.sum_congr rfl (fun e' _ => card_fiber n t e' e)]
    simp
  rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at h1
  rw [h1, h2]
  push_cast
  ring

lemma card_B_real {m : ℕ} (k : Fin m → α) (hk : Function.Injective k) (es t s : Fin m)
    (hs : s < t) :
    ((B k es t s).card : ℝ) = (m.factorial : ℝ) / ((m : ℝ) * ((t : ℕ) : ℝ)) := by
  have h1 := card_fiber_mul m t es
  have h2 := card_C_eq k hk es t s hs
  have ht : (0 : ℝ) < ((t : ℕ) : ℝ) := by
    exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) (Fin.lt_def.1 hs))
  have hm : (0 : ℝ) < m := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) t.isLt)
  rw [h2] at h1
  push_cast at h1
  rw [eq_div_iff (by positivity), ← h1]
  ring

lemma main_ge {m : ℕ} (k : Fin m → α) (hk : Function.Injective k) (es : Fin m)
    (G : Finset (Equiv.Perm (Fin m))) (rr : Fin m) (hr : 0 < (rr : ℕ))
    (hG : ∀ t s σ, rr ≤ t → s < rr → σ ∈ B k es t s → σ ∈ G) :
    ((rr : ℕ) : ℝ) / m * ∑ i ∈ Finset.Ico (rr : ℕ) m, 1 / (i : ℝ) ≤
      1 / (m.factorial : ℝ) * G.card := by
  classical
  set U := (Finset.Ici rr).biUnion (fun t => (Finset.Iio rr).biUnion (fun s => B k es t s))
    with hU
  have hsub : U ⊆ G := by
    intro σ hσ
    simp only [U, Finset.mem_biUnion, Finset.mem_Ici, Finset.mem_Iio] at hσ
    obtain ⟨t, ht, s, hs, h⟩ := hσ
    exact hG t s σ ht hs h
  have hcardU : (U.card : ℝ) =
      ∑ t ∈ Finset.Ici rr, ∑ s ∈ Finset.Iio rr, ((B k es t s).card : ℝ) := by
    rw [hU, Finset.card_biUnion]
    · push_cast
      refine Finset.sum_congr rfl (fun t ht => ?_)
      rw [Finset.card_biUnion]
      · push_cast
        rfl
      · intro a ha b hb hab
        rw [Function.onFun, Finset.disjoint_left]
        intro σ h1 h2
        have ht' := Finset.mem_Ici.1 ht
        simp only [Finset.coe_Iio, Set.mem_Iio] at ha hb
        simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
        exact lt_asymm (h1.2 b (lt_of_lt_of_le hb ht') (Ne.symm hab))
          (h2.2 a (lt_of_lt_of_le ha ht') hab)
    · intro a _ b _ hab
      rw [Function.onFun, Finset.disjoint_left]
      intro σ h1 h2
      simp only [Finset.mem_biUnion, B, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      obtain ⟨_, _, h1, _⟩ := h1
      obtain ⟨_, _, h2, _⟩ := h2
      exact hab (σ.injective (h1.trans h2.symm))
  have hval : ∑ t ∈ Finset.Ici rr, ∑ s ∈ Finset.Iio rr, ((B k es t s).card : ℝ)
      = ∑ t ∈ Finset.Ici rr, ((rr : ℕ) : ℝ) * ((m.factorial : ℝ) / ((m : ℝ) * ((t : ℕ) : ℝ))) := by
    refine Finset.sum_congr rfl (fun t ht => ?_)
    rw [Finset.sum_congr rfl (fun s hs => card_B_real k hk es t s
      (lt_of_lt_of_le (Finset.mem_Iio.1 hs) (Finset.mem_Ici.1 ht)))]
    rw [Finset.sum_const, Fin.card_Iio, nsmul_eq_mul]
  have hmap : (Finset.Ici rr).map Fin.valEmbedding = Finset.Ico (rr : ℕ) m := by
    ext i
    simp only [Finset.mem_map, Finset.mem_Ici, Fin.valEmbedding_apply, Finset.mem_Ico]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨Fin.le_def.1 ha, a.isLt⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨i, h2⟩, Fin.le_def.2 h1, rfl⟩
  have hreidx : ∑ t ∈ Finset.Ici rr, (1 : ℝ) / ((t : ℕ) : ℝ) =
      ∑ i ∈ Finset.Ico (rr : ℕ) m, 1 / (i : ℝ) := by
    rw [← hmap, Finset.sum_map]
    rfl
  have hfact : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have hm : (0 : ℝ) < m := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) rr.isLt)
  calc ((rr : ℕ) : ℝ) / m * ∑ i ∈ Finset.Ico (rr : ℕ) m, 1 / (i : ℝ)
      = 1 / (m.factorial : ℝ) *
          ∑ t ∈ Finset.Ici rr, ((rr : ℕ) : ℝ) * ((m.factorial : ℝ) / ((m : ℝ) * ((t : ℕ) : ℝ))) := by
        rw [← hreidx, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun t ht => ?_)
        have : (0 : ℝ) < ((t : ℕ) : ℝ) := by
          have := Fin.le_def.1 (Finset.mem_Ici.1 ht)
          exact_mod_cast (lt_of_lt_of_le hr this)
        field_simp
    _ = 1 / (m.factorial : ℝ) * U.card := by rw [hcardU, hval]
    _ ≤ 1 / (m.factorial : ℝ) * G.card := by
        gcongr

end comb

/-! ## The rule -/

lemma cs_eq_some {α : Type*} [LinearOrder α] {m : ℕ} (x : Fin m → α) (t : Fin m)
    (ht : ⌊(m : ℝ) / Real.exp 1⌋₊ ≤ t.val ∧ ∀ s : Fin m, s < t → x s < x t)
    (hpre : ∀ u : Fin m, u < t →
      ¬ (⌊(m : ℝ) / Real.exp 1⌋₊ ≤ u.val ∧ ∀ s : Fin m, s < u → x s < x u)) :
    SecretaryWD.DiscUpper.classicalSecretary m x = some t := by
  unfold SecretaryWD.DiscUpper.classicalSecretary
  rw [List.find?_eq_some_iff_getElem]
  refine ⟨decide_eq_true ht, t.val, by simp, by simp, fun j hj => ?_⟩
  have hjm : j < m := lt_trans hj t.isLt
  have := hpre ⟨j, hjm⟩ (Fin.lt_def.2 hj)
  simp only [List.getElem_finRange, Bool.not_eq_true', decide_eq_false_iff_not]
  exact this

lemma tieKey_inj {m : ℕ} (v : Fin m → ℝ) :
    Function.Injective (SecretaryWD.DiscUpper.tieKey v) := by
  intro a b h
  unfold SecretaryWD.DiscUpper.tieKey at h
  have := congrArg (fun p => OrderDual.ofDual (ofLex p).2) h
  simpa using this


open SecretaryWD.DiscUpper in
lemma mem_G_gen {m : ℕ} (v : Fin m → ℝ) (es : Fin m) (hes : ∀ e, tieKey v e ≤ tieKey v es)
    (σ : Equiv.Perm (Fin m)) (t : Fin m) (hσt : σ t = es)
    (hrt : ⌊(m : ℝ) / Real.exp 1⌋₊ ≤ t.val)
    (hpre : ∀ u : Fin m, u < t → ⌊(m : ℝ) / Real.exp 1⌋₊ ≤ u.val →
      ∃ s, s < u ∧ tieKey v (σ u) < tieKey v (σ s)) :
    ∃ t : Fin m, classicalSecretary m (fun s => tieKey v (σ s)) = some t ∧
      ∀ e : Fin m, tieKey v e ≤ tieKey v (σ t) := by
  refine ⟨t, cs_eq_some _ t ⟨hrt, fun s hs => ?_⟩ (fun u hu h => ?_),
    fun e => by rw [hσt]; exact hes e⟩
  · show tieKey v (σ s) < tieKey v (σ t)
    rw [hσt]
    refine lt_of_le_of_ne (hes _) (fun h => ?_)
    have h' : σ s = es := tieKey_inj v h
    exact (ne_of_lt hs) (σ.injective (h'.trans hσt.symm))
  · obtain ⟨h1, h2⟩ := h
    obtain ⟨s, hs, hlt⟩ := hpre u hu h1
    exact lt_asymm hlt (h2 s hs)

open SecretaryWD.DiscUpper in
lemma final (m : ℕ) (hm : 1 ≤ m) (v : Fin m → ℝ) (G : Finset (Equiv.Perm (Fin m)))
    (hG : ∀ σ : Equiv.Perm (Fin m), (∃ t : Fin m,
      classicalSecretary m (fun s => tieKey v (σ s)) = some t ∧
        ∀ e : Fin m, tieKey v e ≤ tieKey v (σ t)) → σ ∈ G) :
    1 / Real.exp 1 ≤ (1 / (m.factorial : ℝ)) * (G.card : ℝ) := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  obtain ⟨es, -, hes⟩ := Finset.exists_max_image Finset.univ (tieKey v) Finset.univ_nonempty
  have hes' : ∀ e, tieKey v e ≤ tieKey v es := fun e => hes e (Finset.mem_univ e)
  have hE1 : 2.7182818283 < Real.exp 1 := Real.exp_one_gt_d9
  have hEpos : 0 < Real.exp 1 := Real.exp_pos 1
  by_cases h3 : 3 ≤ m
  · obtain ⟨hr1, hrm⟩ := floor_facts m h3
    have hA := analytic m h3
    have hB := main_ge (tieKey v) (tieKey_inj v) es G ⟨⌊(m : ℝ) / Real.exp 1⌋₊, hrm⟩ hr1
      (fun t s σ ht hs hσ => by
        simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
        apply hG
        refine mem_G_gen v es hes' σ t hσ.1 (Fin.le_def.1 ht)
          (fun u hu hru => ⟨s, ?_, hσ.2 u hu ?_⟩)
        · exact Fin.lt_def.2 (lt_of_lt_of_le (Fin.lt_def.1 hs) hru)
        · exact ne_of_gt (Fin.lt_def.2 (lt_of_lt_of_le (Fin.lt_def.1 hs) hru)))
    exact le_trans hA hB
  · have hm2 : m ≤ 2 := by omega
    have hr0 : ⌊(m : ℝ) / Real.exp 1⌋₊ = 0 := by
      rw [Nat.floor_eq_zero, div_lt_one hEpos]
      have : (m : ℝ) ≤ 2 := by exact_mod_cast hm2
      linarith
    let t0 : Fin m := ⟨0, hm⟩
    have hsub : Finset.univ.filter (fun σ : Equiv.Perm (Fin m) => σ t0 = es) ⊆ G := by
      intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
      apply hG
      refine mem_G_gen v es hes' σ t0 hσ (hr0.le.trans (Nat.zero_le _)) (fun u hu _ => ?_)
      exact absurd (Fin.lt_def.1 hu) (Nat.not_lt_zero _)
    have hc := card_fiber_mul m t0 es
    have hcard : ((Finset.univ.filter (fun σ : Equiv.Perm (Fin m) => σ t0 = es)).card : ℝ)
        ≤ G.card := by
      exact_mod_cast Finset.card_le_card hsub
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
    have hmR : (m : ℝ) ≤ 2 := by exact_mod_cast hm2
    have hfact : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
    calc 1 / Real.exp 1 ≤ 1 / (m : ℝ) := one_div_le_one_div_of_le hmpos (by linarith)
      _ = 1 / (m.factorial : ℝ) *
          ((Finset.univ.filter (fun σ : Equiv.Perm (Fin m) => σ t0 = es)).card : ℝ) := by
          rw [div_mul_eq_mul_div, one_mul, eq_div_iff hfact.ne', ← hc]
          field_simp
      _ ≤ 1 / (m.factorial : ℝ) * G.card := by gcongr

end DA01

theorem solution (m : ℕ) (hm : 1 ≤ m) (v : Fin m → ℝ) :
    1 / Real.exp 1 ≤
      (1 / (m.factorial : ℝ)) *
        ((Finset.univ.filter fun σ : Equiv.Perm (Fin m) =>
            ∃ t : Fin m, SecretaryWD.DiscUpper.classicalSecretary m (fun s => SecretaryWD.DiscUpper.tieKey v (σ s)) = some t ∧
              ∀ e : Fin m, SecretaryWD.DiscUpper.tieKey v e ≤ SecretaryWD.DiscUpper.tieKey v (σ t)).card : ℝ) := by
  exact DA01.final m hm v _ (fun σ h => Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
