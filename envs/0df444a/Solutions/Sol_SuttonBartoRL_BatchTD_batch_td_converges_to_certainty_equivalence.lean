-- Prove2me | solution 1 for SuttonBartoRL.BatchTD.batch_td_converges_to_certainty_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T13:43:22.309183+00:00
-- url     : https://prove2.me/submissions/4b3d17a6-c592-4d9a-884b-c0ce856fccaa

import Mathlib
import Definitions.Def_SuttonBartoRL_BatchTD_Episodes
import Definitions.Def_SuttonBartoRL_BatchTD_BatchUpdating

set_option autoImplicit false

open Filter Topology

namespace SuttonBartoRL.BatchTD.Pf0403

open Matrix

lemma stateAt_some_lt {X : Type} {e : Episode X} {t : ℕ} {x : X} (h : stateAt e t = some x) :
    t < e.length := by
  by_contra hc
  push Not at hc
  simp [stateAt, List.getElem?_eq_none hc] at h

variable {S : Type} [Fintype S] [DecidableEq S]

lemma visitCount_ne_zero_iff (b : Batch S) (s : S) :
    visitCount b s ≠ 0 ↔ ∃ e ∈ b, ∃ t, stateAt e t = some s := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    apply h
    unfold visitCount
    rw [List.sum_eq_zero_iff]
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro t _ ht
    exact hc e he t ht
  · rintro ⟨e, he, t, ht⟩ h
    unfold visitCount at h
    rw [List.sum_eq_zero_iff] at h
    have := h _ (List.mem_map.2 ⟨e, he, rfl⟩)
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at this
    exact this (Finset.mem_range.2 (stateAt_some_lt ht)) ht

lemma transCount_ne_zero_iff (b : Batch S) (s : S) (j : Option S) :
    transCount b s j ≠ 0 ↔ ∃ e ∈ b, ∃ t, stateAt e t = some s ∧ stateAt e (t + 1) = j := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    apply h
    unfold transCount
    rw [List.sum_eq_zero_iff]
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro t _ ⟨ht1, ht2⟩
    exact hc e he t ht1 ht2
  · rintro ⟨e, he, t, ht, ht2⟩ h
    unfold transCount at h
    rw [List.sum_eq_zero_iff] at h
    have := h _ (List.mem_map.2 ⟨e, he, rfl⟩)
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at this
    exact this (Finset.mem_range.2 (stateAt_some_lt ht)) ⟨ht, ht2⟩

lemma sum_transCount (b : Batch S) (s : S) :
    ∑ j : Option S, transCount b s j = visitCount b s := by
  induction b with
  | nil => simp [transCount, visitCount]
  | cons e b ih =>
    simp only [transCount, visitCount, List.map_cons, List.sum_cons] at ih ⊢
    rw [Finset.sum_add_distrib, ih]
    congr 1
    rw [Finset.card_eq_sum_card_fiberwise (f := fun t => stateAt e (t + 1)) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.filter_filter]

lemma visitSum_cons (e : Episode S) (b : Batch S) (s : S) (f : Episode S → ℕ → ℝ) :
    visitSum (e :: b) s f =
      (∑ t ∈ Finset.range e.length, if stateAt e t = some s then f e t else 0) + visitSum b s f := by
  simp [visitSum]

lemma visitSum_congr (b : Batch S) (s : S) (f g : Episode S → ℕ → ℝ)
    (h : ∀ e ∈ b, ∀ t, stateAt e t = some s → f e t = g e t) : visitSum b s f = visitSum b s g := by
  unfold visitSum
  congr 1
  apply List.map_congr_left
  intro e he
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs with ht
  · exact h e he t ht
  · rfl

lemma visitSum_eq_zero (b : Batch S) (s : S) (f : Episode S → ℕ → ℝ)
    (hf : ∀ e ∈ b, ∀ t, stateAt e t = some s → f e t = 0) : visitSum b s f = 0 := by
  unfold visitSum
  rw [List.sum_eq_zero]
  intro x hx
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
  apply Finset.sum_eq_zero
  intro t _
  split_ifs with h
  · exact hf e he t h
  · rfl

lemma visitSum_add (b : Batch S) (s : S) (f g : Episode S → ℕ → ℝ) :
    visitSum b s (fun e t => f e t + g e t) = visitSum b s f + visitSum b s g := by
  induction b with
  | nil => simp [visitSum]
  | cons e b ih =>
    rw [visitSum_cons, visitSum_cons, visitSum_cons, ih]
    have : (∑ t ∈ Finset.range e.length, if stateAt e t = some s then f e t + g e t else 0) =
        (∑ t ∈ Finset.range e.length, if stateAt e t = some s then f e t else 0) +
        (∑ t ∈ Finset.range e.length, if stateAt e t = some s then g e t else 0) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun t _ => by split_ifs <;> simp
    rw [this]; ring

lemma visitSum_mul (b : Batch S) (s : S) (c : ℝ) (f : Episode S → ℕ → ℝ) :
    visitSum b s (fun e t => c * f e t) = c * visitSum b s f := by
  induction b with
  | nil => simp [visitSum]
  | cons e b ih =>
    rw [visitSum_cons, visitSum_cons, ih, mul_add, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun t _ => by split_ifs <;> simp

lemma visitSum_sub (b : Batch S) (s : S) (f g : Episode S → ℕ → ℝ) :
    visitSum b s (fun e t => f e t - g e t) = visitSum b s f - visitSum b s g := by
  have h := visitSum_add b s f (fun e t => (-1) * g e t)
  rw [visitSum_mul] at h
  have : (fun e t => f e t - g e t) = (fun e t => f e t + (-1) * g e t) := by
    funext e t; ring
  rw [this, h]; ring

lemma visitSum_finsetSum {ι : Type} (F : Finset ι) (b : Batch S) (s : S)
    (f : ι → Episode S → ℕ → ℝ) :
    visitSum b s (fun e t => ∑ i ∈ F, f i e t) = ∑ i ∈ F, visitSum b s (f i) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact visitSum_eq_zero b s _ fun _ _ _ _ => rfl
  | insert a F ha ih =>
    simp only [Finset.sum_insert ha]
    rw [visitSum_add, ih]

lemma visitCount_eq (b : Batch S) (s : S) :
    (visitCount b s : ℝ) = visitSum b s (fun _ _ => 1) := by
  induction b with
  | nil => simp [visitCount, visitSum]
  | cons e b ih =>
    rw [visitSum_cons, ← ih]
    simp only [visitCount, List.map_cons, List.sum_cons, Nat.cast_add]
    congr 1
    rw [Finset.card_filter, Nat.cast_sum]
    exact Finset.sum_congr rfl fun t _ => by split_ifs <;> simp

lemma transCount_eq (b : Batch S) (s : S) (j : Option S) :
    (transCount b s j : ℝ) = visitSum b s (fun e t => if stateAt e (t + 1) = j then 1 else 0) := by
  induction b with
  | nil => simp [transCount, visitSum]
  | cons e b ih =>
    rw [visitSum_cons, ← ih]
    simp only [transCount, List.map_cons, List.sum_cons, Nat.cast_add]
    congr 1
    rw [Finset.card_filter, Nat.cast_sum]
    exact Finset.sum_congr rfl fun t _ => by split_ifs <;> simp_all

lemma transRewardSum_eq_zero (b : Batch S) (s : S) (j : Option S) (h : transCount b s j = 0) :
    transRewardSum b s j = 0 := by
  apply visitSum_eq_zero
  intro e he t ht
  split_ifs with h2
  · exact absurd h ((transCount_ne_zero_iff b s j).2 ⟨e, he, t, ht, h2⟩)
  · rfl

lemma tdIncrement_linear (γ : ℝ) (b : Batch S) (V : S → ℝ) (s : S) :
    tdIncrement γ b V s = ∑ j : Option S, transRewardSum b s j
      + γ * ∑ s' : S, (transCount b s (some s') : ℝ) * V s' - (visitCount b s : ℝ) * V s := by
  have h1 : tdIncrement γ b V s = visitSum b s (fun e t =>
      (∑ j : Option S, (if stateAt e (t + 1) = j then nextReward e t else 0))
      + γ * (∑ s' : S, V s' * (if stateAt e (t + 1) = some s' then 1 else 0)) - V s * 1) := by
    unfold tdIncrement
    apply visitSum_congr
    intro e _ t ht
    unfold tdError
    rw [ht]
    rcases h : stateAt e (t + 1) with _ | x
    · simp [extV]
    · simp [extV]
  rw [h1]
  simp only [visitSum_sub, visitSum_add, visitSum_mul, visitSum_finsetSum]
  simp only [← transCount_eq, ← visitCount_eq]
  rw [show (∑ j : Option S, transRewardSum b s j) = ∑ j : Option S, visitSum b s
    (fun e t => if stateAt e (t + 1) = j then nextReward e t else 0) from rfl]
  rw [show (∑ s' : S, (transCount b s (some s') : ℝ) * V s') =
    ∑ s' : S, V s' * (transCount b s (some s') : ℝ) from
      Finset.sum_congr rfl fun _ _ => mul_comm _ _]
  ring

theorem tdIncrement_eq (γ : ℝ) (b : Batch S) (V : S → ℝ) (s : S) :
    tdIncrement γ b V s =
      (visitCount b s : ℝ) * (mlExpectedReward b s + γ * (mlMatrix b *ᵥ V) s - V s) := by
  rw [tdIncrement_linear]
  have hn0 : visitCount b s = 0 → ∀ j, transCount b s j = 0 := by
    intro h j
    have := sum_transCount b s
    rw [h, Finset.sum_eq_zero_iff] at this
    exact this j (Finset.mem_univ _)
  have hR : (visitCount b s : ℝ) * mlExpectedReward b s = ∑ j, transRewardSum b s j := by
    unfold mlExpectedReward
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold mlProb mlReward
    by_cases hc : transCount b s j = 0
    · rw [transRewardSum_eq_zero b s j hc]; simp [hc]
    · have hn : visitCount b s ≠ 0 := fun h => hc (hn0 h j)
      have hn' : (visitCount b s : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
      have hc' : (transCount b s j : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hc
      field_simp
  have hP : (visitCount b s : ℝ) * (mlMatrix b *ᵥ V) s =
      ∑ s', (transCount b s (some s') : ℝ) * V s' := by
    show (visitCount b s : ℝ) * ∑ s', mlMatrix b s s' * V s' = _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s' _ => ?_
    unfold mlMatrix mlProb
    by_cases hn : visitCount b s = 0
    · simp [hn, hn0 hn]
    · have hn' : (visitCount b s : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
      field_simp
  linear_combination -hR - γ * hP

noncomputable def depth (b : Batch S) (s : S) : ℕ :=
  sInf {k | ∃ e ∈ b, ∃ t, t + k = e.length ∧ stateAt e t = some s}

lemma depth_spec (b : Batch S) (s : S) (hs : visitCount b s ≠ 0) :
    1 ≤ depth b s ∧ depth b s ≤ (b.map List.length).sum ∧
    ∃ e ∈ b, ∃ t, t + depth b s = e.length ∧ stateAt e t = some s := by
  obtain ⟨e, he, t, ht⟩ := (visitCount_ne_zero_iff b s).1 hs
  have hne : {k | ∃ e ∈ b, ∃ t, t + k = e.length ∧ stateAt e t = some s}.Nonempty :=
    ⟨e.length - t, e, he, t, by have := stateAt_some_lt ht; omega, ht⟩
  obtain ⟨e', he', t', hlen, ht'⟩ := Nat.sInf_mem hne
  have hlt := stateAt_some_lt ht'
  have hle : e'.length ≤ (b.map List.length).sum :=
    List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map.2 ⟨e', he', rfl⟩)
  refine ⟨?_, ?_, e', he', t', hlen, ht'⟩
  · unfold depth; omega
  · unfold depth; omega

lemma depth_le (b : Batch S) (s : S) (e : Episode S) (he : e ∈ b) (t k : ℕ)
    (hk : t + k = e.length) (ht : stateAt e t = some s) : depth b s ≤ k :=
  Nat.sInf_le ⟨e, he, t, hk, ht⟩

theorem weight_exists (b : Batch S) :
    ∃ w : S → ℝ, (∀ s, 0 ≤ w s) ∧ (∀ s, visitCount b s ≠ 0 → 0 < w s) ∧
      ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ s, (mlMatrix b *ᵥ w) s ≤ ρ * w s := by
  set N : ℝ := ∑ s, (visitCount b s : ℝ) with hN
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  set c : ℝ := 1 / (2 * (N + 1)) with hc_def
  have hc0 : 0 < c := by positivity
  have hc1 : c < 1 := by
    rw [hc_def, div_lt_one (by positivity)]; linarith
  have h2c : 1 / (N + 1) = 2 * c := by rw [hc_def]; field_simp
  set L : ℕ := (b.map List.length).sum with hL
  set w : S → ℝ := fun s => 1 - c ^ depth b s with hw
  have hw0 : ∀ s, 0 ≤ w s := fun s => by
    have := pow_le_one₀ (n := depth b s) hc0.le hc1.le
    simp only [hw]; linarith
  have hw1 : ∀ s, w s ≤ 1 := fun s => by
    have := pow_nonneg hc0.le (depth b s)
    simp only [hw]; linarith
  have hcL0 : 0 < c ^ L := pow_pos hc0 L
  have hcL1 : c ^ L ≤ 1 := pow_le_one₀ hc0.le hc1.le
  refine ⟨w, hw0, ?_, 1 - c ^ L, by linarith, by linarith, ?_⟩
  · intro s hs
    obtain ⟨hD1, -, -⟩ := depth_spec b s hs
    have : c ^ depth b s < 1 := pow_lt_one₀ hc0.le hc1 (by omega)
    simp only [hw]; linarith
  · intro s
    by_cases hs : visitCount b s = 0
    · have : (mlMatrix b *ᵥ w) s = 0 := by
        show ∑ s', mlMatrix b s s' * w s' = 0
        simp [mlMatrix, mlProb, hs]
      rw [this]
      exact mul_nonneg (by linarith) (hw0 s)
    · obtain ⟨hD1, hDL, e, he, t, hlen, ht⟩ := depth_spec b s hs
      have hn' : (visitCount b s : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hs
      have hnpos : (0 : ℝ) < visitCount b s := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hn')
      have hnN : (visitCount b s : ℝ) ≤ N :=
        Finset.single_le_sum (f := fun s => (visitCount b s : ℝ)) (fun _ _ => Nat.cast_nonneg _)
          (Finset.mem_univ s)
      -- the next state of the minimal visit
      have hcj : transCount b s (stateAt e (t + 1)) ≠ 0 :=
        (transCount_ne_zero_iff b s _).2 ⟨e, he, t, ht, rfl⟩
      have hwj : extV w (stateAt e (t + 1)) ≤ 1 - c ^ (depth b s - 1) := by
        rcases hj : stateAt e (t + 1) with _ | x
        · have := pow_le_one₀ (n := depth b s - 1) hc0.le hc1.le
          simp only [extV]; linarith
        · have hdx : depth b x ≤ depth b s - 1 :=
            depth_le b x e he (t + 1) (depth b s - 1) (by omega) hj
          have := pow_le_pow_of_le_one hc0.le hc1.le hdx
          simp only [extV, hw]; linarith
      set p : Option S → ℝ := fun j => mlProb b s j with hp
      set u : Option S → ℝ := fun j => extV w j with hu
      have hp0 : ∀ j, 0 ≤ p j := fun j => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      have hu1 : ∀ j, u j ≤ 1 := by
        intro j; rcases j with _ | x
        · simp [hu, extV]
        · simp only [hu, extV]; exact hw1 x
      have hPw : (mlMatrix b *ᵥ w) s = ∑ j, p j * u j := by
        show ∑ s', mlMatrix b s s' * w s' = _
        rw [Fintype.sum_option]
        simp [hp, hu, extV, mlMatrix]
      have hpsum : ∑ j, p j = 1 := by
        simp only [hp, mlProb]
        rw [← Finset.sum_div, ← Nat.cast_sum, sum_transCount, div_self hn']
      have hsplit : ∑ j, p j * u j = ∑ j, p j - ∑ j, p j * (1 - u j) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      have hsingle : p (stateAt e (t + 1)) * (1 - u (stateAt e (t + 1))) ≤ ∑ j, p j * (1 - u j) :=
        Finset.single_le_sum (f := fun j => p j * (1 - u j))
          (fun j _ => mul_nonneg (hp0 j) (by linarith [hu1 j])) (Finset.mem_univ _)
      have hpj : 2 * c ≤ p (stateAt e (t + 1)) := by
        rw [← h2c]
        simp only [hp, mlProb]
        have h1 : (1 : ℝ) ≤ transCount b s (stateAt e (t + 1)) := by
          exact_mod_cast Nat.one_le_iff_ne_zero.2 hcj
        rw [div_le_div_iff₀ (by linarith) hnpos]
        nlinarith
      have huj : c ^ (depth b s - 1) ≤ 1 - u (stateAt e (t + 1)) := by
        simp only [hu]; linarith
      have hprod : 2 * c * c ^ (depth b s - 1) ≤
          p (stateAt e (t + 1)) * (1 - u (stateAt e (t + 1))) :=
        mul_le_mul hpj huj (pow_nonneg hc0.le _) (hp0 _)
      have hpowD : c ^ depth b s = c * c ^ (depth b s - 1) := by
        rw [← pow_succ']; congr 1; omega
      have hLD : c ^ L ≤ c ^ depth b s := pow_le_pow_of_le_one hc0.le hc1.le hDL
      have hwS : w s = 1 - c ^ depth b s := rfl
      rw [hPw, hsplit, hpsum]
      nlinarith [hw1 s]

lemma abs_mulVec_le {P : Matrix S S ℝ} (hP : ∀ i j, 0 ≤ P i j) {g w : S → ℝ} {K : ℝ}
    (h : ∀ j, |g j| ≤ K * w j) (i : S) : |(P *ᵥ g) i| ≤ K * (P *ᵥ w) i := by
  show |∑ j, P i j * g j| ≤ K * ∑ j, P i j * w j
  calc |∑ j, P i j * g j| ≤ ∑ j, |P i j * g j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, P i j * (K * w j) := Finset.sum_le_sum fun j _ => by
        rw [abs_mul, abs_of_nonneg (hP i j)]; exact mul_le_mul_of_nonneg_left (h j) (hP i j)
    _ = K * ∑ j, P i j * w j := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring

lemma pow_mulVec_bound {P : Matrix S S ℝ} (hP : ∀ i j, 0 ≤ P i j) {w : S → ℝ} {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hw : ∀ i, (P *ᵥ w) i ≤ ρ * w i)
    {f : S → ℝ} {M : ℝ} (hM0 : 0 ≤ M) (hf : ∀ j, |f j| ≤ M * w j) (k : ℕ) (i : S) :
    |(P ^ k *ᵥ f) i| ≤ ρ ^ k * M * w i := by
  induction k generalizing i with
  | zero => simpa using hf i
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    calc |(P *ᵥ (P ^ k *ᵥ f)) i| ≤ (ρ ^ k * M) * (P *ᵥ w) i := abs_mulVec_le hP ih i
      _ ≤ (ρ ^ k * M) * (ρ * w i) := mul_le_mul_of_nonneg_left (hw i) (by positivity)
      _ = ρ ^ (k + 1) * M * w i := by ring

lemma bound_exists (w f : S → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hf : ∀ i, w i = 0 → f i = 0) :
    ∃ M, 0 ≤ M ∧ ∀ j, |f j| ≤ M * w j := by
  refine ⟨∑ i, |f i| / w i, Finset.sum_nonneg fun i _ => div_nonneg (abs_nonneg _) (hw0 i),
    fun j => ?_⟩
  rcases (hw0 j).eq_or_lt with h | h
  · rw [hf j h.symm, abs_zero, ← h, mul_zero]
  · have : |f j| / w j ≤ ∑ i, |f i| / w i :=
      Finset.single_le_sum (f := fun i => |f i| / w i)
        (fun i _ => div_nonneg (abs_nonneg _) (hw0 i)) (Finset.mem_univ j)
    rwa [div_le_iff₀ h] at this

lemma summable_series {P : Matrix S S ℝ} (hP : ∀ i j, 0 ≤ P i j) {w : S → ℝ} {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hw : ∀ i, (P *ᵥ w) i ≤ ρ * w i)
    {f : S → ℝ} {M : ℝ} (hM0 : 0 ≤ M) (hf : ∀ j, |f j| ≤ M * w j)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (i : S) :
    Summable fun k : ℕ => γ ^ k * (P ^ k *ᵥ f) i := by
  refine Summable.of_norm_bounded (g := fun k : ℕ => ρ ^ k * (M * w i))
    ((summable_geometric_of_lt_one hρ0 hρ1).mul_right _) ?_
  intro k
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hγ0 k)]
  have hb := pow_mulVec_bound hP hρ0 hw hM0 hf k i
  have hg1 : γ ^ k ≤ 1 := pow_le_one₀ hγ0 hγ1
  calc γ ^ k * |(P ^ k *ᵥ f) i| ≤ 1 * (ρ ^ k * M * w i) :=
        mul_le_mul hg1 hb (abs_nonneg _) zero_le_one
    _ = ρ ^ k * (M * w i) := by ring

lemma series_fixed {P : Matrix S S ℝ} {f : S → ℝ} {γ : ℝ}
    (hs : ∀ i, Summable fun k : ℕ => γ ^ k * (P ^ k *ᵥ f) i) (i : S) :
    (∑' k : ℕ, γ ^ k * (P ^ k *ᵥ f) i) =
      f i + γ * (P *ᵥ fun j => ∑' k : ℕ, γ ^ k * (P ^ k *ᵥ f) j) i := by
  rw [(hs i).tsum_eq_zero_add]
  congr 1
  · simp
  · have h : HasSum (fun k : ℕ => γ * ∑ j, P i j * (γ ^ k * (P ^ k *ᵥ f) j))
        (γ * ∑ j, P i j * ∑' k : ℕ, γ ^ k * (P ^ k *ᵥ f) j) :=
      (hasSum_sum fun j _ => ((hs j).hasSum.mul_left (P i j))).mul_left γ
    show _ = γ * ∑ j, P i j * ∑' k : ℕ, γ ^ k * (P ^ k *ᵥ f) j
    rw [← h.tsum_eq]
    congr 1
    funext k
    rw [pow_succ' P k, ← Matrix.mulVec_mulVec, pow_succ' γ k]
    show γ * γ ^ k * ∑ j, P i j * (P ^ k *ᵥ f) j = _
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring

theorem affine_iter_tendsto {P : Matrix S S ℝ} (hP : ∀ i j, 0 ≤ P i j)
    {w : S → ℝ} (hw0 : ∀ i, 0 ≤ w i) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hw : ∀ i, (P *ᵥ w) i ≤ ρ * w i)
    (d : S → ℕ) (hwpos : ∀ i, d i ≠ 0 → 0 < w i)
    (hclosed : ∀ i j, P i j ≠ 0 → d j ≠ 0)
    (r v : S → ℝ) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hv : ∀ i, v i = r i + γ * (P *ᵥ v) i)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α * (1 + ∑ i, (d i : ℝ)) ≤ 1)
    (x₀ : S → ℝ) (i : S) :
    Tendsto (fun m : ℕ =>
        ((fun x : S → ℝ => fun s => x s + α * ((d s : ℝ) * (r s + γ * (P *ᵥ x) s - x s)))^[m]
          x₀) i)
      atTop (𝓝 (if d i = 0 then x₀ i else v i)) := by
  set F := (fun x : S → ℝ => fun s => x s + α * ((d s : ℝ) * (r s + γ * (P *ᵥ x) s - x s)))
    with hF
  set t : S → ℝ := fun s => if d s = 0 then x₀ s else v s with ht
  have hPt : P *ᵥ t = P *ᵥ v := by
    funext s
    show ∑ j, P s j * t j = ∑ j, P s j * v j
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : d j = 0
    · have : P s j = 0 := by
        by_contra h; exact hclosed s j h hj
      simp [this]
    · simp [ht, hj]
  have hdsum0 : 0 ≤ ∑ i, (d i : ℝ) := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hdle : ∀ s, α * (d s : ℝ) ≤ 1 := fun s => by
    have h1 : (d s : ℝ) ≤ ∑ i, (d i : ℝ) :=
      Finset.single_le_sum (f := fun i => (d i : ℝ)) (fun j _ => Nat.cast_nonneg _)
        (Finset.mem_univ s)
    nlinarith
  have hα1' : α ≤ 1 := by nlinarith
  set q : ℝ := 1 - α * (1 - ρ) with hq
  have hq0 : 0 ≤ q := by
    rw [hq]; nlinarith
  have hq1 : q < 1 := by
    rw [hq]; nlinarith
  obtain ⟨M, hM0, hM⟩ := bound_exists w (fun s => x₀ s - t s) hw0 (by
    intro s hs
    have : d s = 0 := by
      by_contra h; exact (hwpos s h).ne' hs
    simp [ht, this])
  have inv : ∀ m : ℕ, ∀ s, (d s = 0 → (F^[m] x₀) s = x₀ s) ∧
      |(F^[m] x₀) s - t s| ≤ q ^ m * M * w s := by
    intro m
    induction m with
    | zero => intro s; exact ⟨fun _ => rfl, by simpa using hM s⟩
    | succ m ih =>
      intro s
      rw [Function.iterate_succ_apply']
      set y := F^[m] x₀ with hy
      by_cases hds : d s = 0
      · have hFy : F y s = y s := by simp [hF, hds]
        have hys : y s = x₀ s := (ih s).1 hds
        refine ⟨fun _ => hFy.trans hys, ?_⟩
        rw [hFy, hys]
        simp only [ht, hds, if_true, sub_self, abs_zero]
        have := hw0 s
        positivity
      · refine ⟨fun h => absurd h hds, ?_⟩
        have hts : t s = v s := by simp [ht, hds]
        have hd1 : (1 : ℝ) ≤ d s := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hds
        set a : ℝ := α * d s with ha
        have ha1 : a ≤ 1 := hdle s
        have haα : α ≤ a := by rw [ha]; nlinarith
        have e1 : (P *ᵥ (y - t)) s = (P *ᵥ y) s - (P *ᵥ v) s := by
          rw [Matrix.mulVec_sub, hPt]; rfl
        have key : F y s - t s = (1 - a) * (y s - t s) + a * γ * (P *ᵥ (y - t)) s := by
          rw [e1, hts]
          simp only [hF]
          linear_combination (-α * (d s : ℝ)) * hv s
        have hb1 : |(P *ᵥ (y - t)) s| ≤ (q ^ m * M) * (P *ᵥ w) s :=
          abs_mulVec_le hP (fun j => by simpa [Pi.sub_apply] using (ih j).2) s
        have hb2 : (P *ᵥ w) s ≤ ρ * w s := hw s
        have hZ : 0 ≤ q ^ m * M := mul_nonneg (pow_nonneg hq0 m) hM0
        have hb3 : |(P *ᵥ (y - t)) s| ≤ (q ^ m * M) * (ρ * w s) :=
          hb1.trans (mul_le_mul_of_nonneg_left hb2 hZ)
        have hy1 := (ih s).2
        rw [key]
        have hws := hw0 s
        have hW : 0 ≤ q ^ m * M * w s := mul_nonneg hZ hws
        calc |(1 - a) * (y s - t s) + a * γ * (P *ᵥ (y - t)) s|
            ≤ |(1 - a) * (y s - t s)| + |a * γ * (P *ᵥ (y - t)) s| := abs_add_le _ _
          _ = (1 - a) * |y s - t s| + (a * γ) * |(P *ᵥ (y - t)) s| := by
              rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - a),
                abs_of_nonneg (by positivity : (0 : ℝ) ≤ a * γ)]
          _ ≤ (1 - a) * (q ^ m * M * w s) + (a * γ) * ((q ^ m * M) * (ρ * w s)) := by
              gcongr <;> linarith
          _ = ((1 - a) + a * γ * ρ) * (q ^ m * M * w s) := by ring
          _ ≤ q * (q ^ m * M * w s) := by
              apply mul_le_mul_of_nonneg_right _ hW
              have h1 : 0 ≤ (a - α) * (1 - γ * ρ) := mul_nonneg (by linarith) (by nlinarith)
              have h2 : 0 ≤ α * ρ * (1 - γ) := mul_nonneg (mul_nonneg hα0.le hρ0) (by linarith)
              rw [hq]; nlinarith
          _ = q ^ (m + 1) * M * w s := by ring
  have hlim : Tendsto (fun m : ℕ => q ^ m * M * w i) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const (M * w i)
    simpa [mul_assoc] using this
  show Tendsto (fun m : ℕ => (F^[m] x₀) i) atTop (𝓝 (t i))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun m => norm_nonneg _)
    (fun m => by rw [Real.norm_eq_abs]; exact (inv m i).2) hlim

end SuttonBartoRL.BatchTD.Pf0403

open Filter Topology Matrix SuttonBartoRL.BatchTD in
theorem solution {S : Type} [Fintype S] [DecidableEq S]
    (b : Batch S) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    (∀ s : S, Summable fun k : ℕ => γ ^ k * (Matrix.mulVec (mlMatrix b ^ k) (mlExpectedReward b)) s) ∧
    ∃ αbar : ℝ, 0 < αbar ∧ ∀ α : ℝ, 0 < α → α < αbar → ∀ (V₀ : S → ℝ) (s : S),
      Tendsto (fun m : ℕ => batchTD α γ b V₀ m s) atTop
        (𝓝 (if visitCount b s = 0 then V₀ s else ceEstimate γ b s)) := by
  obtain ⟨w, hw0, hwpos, ρ, hρ0, hρ1, hw⟩ := Pf0403.weight_exists b
  have hP : ∀ i j, 0 ≤ mlMatrix b i j := fun i j =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  obtain ⟨M, hM0, hM⟩ := Pf0403.bound_exists w (mlExpectedReward b) hw0 (by
    intro s hs
    have hv0 : visitCount b s = 0 := by
      by_contra h; exact (hwpos s h).ne' hs
    simp [mlExpectedReward, mlProb, hv0])
  have hsum : ∀ s : S, Summable fun k : ℕ =>
      γ ^ k * (Matrix.mulVec (mlMatrix b ^ k) (mlExpectedReward b)) s :=
    fun s => Pf0403.summable_series hP hρ0 hρ1 hw hM0 hM hγ0 hγ1 s
  have hv : ∀ i, ceEstimate γ b i = mlExpectedReward b i + γ * (mlMatrix b *ᵥ ceEstimate γ b) i :=
    fun i => Pf0403.series_fixed hsum i
  have hclosed : ∀ i j, mlMatrix b i j ≠ 0 → visitCount b j ≠ 0 := by
    intro i j h
    have hc : transCount b i (some j) ≠ 0 := by
      intro hc; apply h; simp [mlMatrix, mlProb, hc]
    obtain ⟨e, he, t, _, ht2⟩ := (Pf0403.transCount_ne_zero_iff b i (some j)).1 hc
    exact (Pf0403.visitCount_ne_zero_iff b j).2 ⟨e, he, t + 1, ht2⟩
  refine ⟨hsum, 1 / (1 + ∑ i, (visitCount b i : ℝ)), by positivity, ?_⟩
  intro α hα0 hα1 V₀ s
  have hpos : (0 : ℝ) < 1 + ∑ i, (visitCount b i : ℝ) := by positivity
  have hα1' : α * (1 + ∑ i, (visitCount b i : ℝ)) ≤ 1 := by
    rw [lt_div_iff₀ hpos] at hα1; linarith
  have hstep : batchTDStep α γ b = fun x : S → ℝ => fun s => x s + α * ((visitCount b s : ℝ) *
      (mlExpectedReward b s + γ * (mlMatrix b *ᵥ x) s - x s)) := by
    funext x s
    simp only [batchTDStep, Pf0403.tdIncrement_eq]
  have := Pf0403.affine_iter_tendsto hP hw0 hρ0 hρ1 hw (fun s => visitCount b s) hwpos hclosed
    (mlExpectedReward b) (ceEstimate γ b) hγ0 hγ1 hv hα0 hα1' V₀ s
  unfold batchTD
  rw [hstep]
  exact this
