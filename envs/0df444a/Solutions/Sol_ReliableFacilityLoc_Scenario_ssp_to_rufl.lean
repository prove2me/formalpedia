-- Prove2me | solution 1 for ReliableFacilityLoc.Scenario.ssp_to_rufl
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T01:35:30.407277+00:00
-- url     : https://prove2.me/submissions/77b6b3a8-ceac-4944-b73b-26b9a368fa82

import Definitions.Def_ReliableFacilityLoc_Scenario_RUFL
import Definitions.Def_ReliableFacilityLoc_Scenario_SSP

open Finset ReliableFacilityLoc.Scenario

namespace RFL1Aux

open Classical

lemma bin_nonneg {x : ℝ} (h : x = 0 ∨ x = 1) : 0 ≤ x := by rcases h with h|h <;> simp [h]
lemma bin_le_one {x : ℝ} (h : x = 0 ∨ x = 1) : x ≤ 1 := by rcases h with h|h <;> simp [h]

lemma two_le_sum {ι : Type*} {s : Finset ι} {f : ι → ℝ} (hf : ∀ x ∈ s, 0 ≤ f x) {a b : ι}
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) (hfa : f a = 1) (hfb : f b = 1) :
    2 ≤ ∑ x ∈ s, f x := by
  have hsub : ({a, b} : Finset ι) ⊆ s := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x hx _ => hf x hx)
  rw [Finset.sum_pair hab, hfa, hfb] at this
  linarith

lemma unique_one {ι : Type*} [Fintype ι] {f : ι → ℝ} (hb : ∀ x, f x = 0 ∨ f x = 1)
    (hs : ∑ x, f x = 1) : ∃ k, f k = 1 ∧ ∀ k', k' ≠ k → f k' = 0 := by
  by_cases h : ∃ k, f k = 1
  · obtain ⟨k, hk⟩ := h
    refine ⟨k, hk, fun k' hk'ne => ?_⟩
    rcases hb k' with h0 | h1
    · exact h0
    · have := two_le_sum (s := univ) (fun x _ => bin_nonneg (hb x)) (mem_univ k') (mem_univ k)
        hk'ne h1 hk
      linarith
  · push Not at h
    have : ∑ x, f x = 0 := Finset.sum_eq_zero (fun x _ => (hb x).resolve_right (h x))
    linarith

lemma sum_Iio_last {n : ℕ} (f : Fin (n + 1) → ℝ) :
    ∑ s ∈ Iio (Fin.last n), f s = ∑ s : Fin n, f s.castSucc := by
  rw [Fin.Iio_last_eq_map, Finset.sum_map]
  rfl

/-- real indicator of a boolean -/
noncomputable def ind (b : Bool) : ℝ := if b = true then 1 else 0

lemma ind_bin (b : Bool) : ind b = 0 ∨ ind b = 1 := by cases b <;> simp [ind]

section RUFL

variable {I J R : ℕ} {D : Instance I J R} {X : Fin J → ℝ}
  {Y P : Fin I → Fin (J + 1) → Fin (R + 1) → ℝ}

lemma Y_nonneg (h : D.IsRUFLFeasible X Y P) (i j r) : 0 ≤ Y i j r :=
  bin_nonneg (h.Y_binary i j r)

lemma Y_last_reg (h : D.IsRUFLFeasible X Y P) (i : Fin I) (k : Fin J) :
    Y i k.castSucc (Fin.last R) = 0 := by
  have h1 := h.level_one i (Fin.last R)
  have h2 := h.emergency_once i
  rw [Fin.sum_univ_castSucc] at h1 h2
  rw [sum_Iio_last] at h1
  have hsum : ∑ j : Fin J, Y i j.castSucc (Fin.last R) = 0 := by linarith
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Y_nonneg h i _ _)).1 hsum k (mem_univ k)

lemma Y_level_unique (h : D.IsRUFLFeasible X Y P) (i : Fin I) (k : Fin (J + 1))
    (l r : Fin (R + 1)) (hl : Y i k l = 1) (hr : Y i k r = 1) : l = r := by
  by_contra hne
  induction k using Fin.lastCases with
  | last =>
    have := two_le_sum (s := univ) (fun x _ => Y_nonneg h i (Fin.last J) x) (mem_univ l)
      (mem_univ r) hne hl hr
    have h2 := h.emergency_once i
    linarith
  | cast k =>
    have hlR : l ≠ Fin.last R := fun e => by rw [e, Y_last_reg h] at hl; norm_num at hl
    have hrR : r ≠ Fin.last R := fun e => by rw [e, Y_last_reg h] at hr; norm_num at hr
    have hl' : l ∈ Iio (Fin.last R) := mem_Iio.2 (Fin.lt_last_iff_ne_last.2 hlR)
    have hr' : r ∈ Iio (Fin.last R) := mem_Iio.2 (Fin.lt_last_iff_ne_last.2 hrR)
    have := two_le_sum (fun x _ => Y_nonneg h i k.castSucc x) hl' hr' hne hl hr
    have h2 := h.open_only i k
    have h3 := bin_le_one (h.X_binary k)
    linarith

lemma Y_reg_open (h : D.IsRUFLFeasible X Y P) (i : Fin I) (k : Fin J) (r : Fin (R + 1))
    (hr : Y i k.castSucc r = 1) : X k = 1 := by
  have hrR : r ≠ Fin.last R := fun e => by rw [e, Y_last_reg h] at hr; norm_num at hr
  have hr' : r ∈ Iio (Fin.last R) := mem_Iio.2 (Fin.lt_last_iff_ne_last.2 hrR)
  have h1 := Finset.single_le_sum (fun x _ => Y_nonneg h i k.castSucc x) hr'
  have h2 := h.open_only i k
  rcases h.X_binary k with h0 | h0
  · rw [hr] at h1; linarith
  · exact h0

/-- facility `k` was used at some level `< r` -/
def U (Y : Fin I → Fin (J + 1) → Fin (R + 1) → ℝ) (i : Fin I) (r : ℕ) (k : Fin (J + 1)) :
    Prop := ∃ l : Fin (R + 1), (l : ℕ) < r ∧ Y i k l = 1

lemma no_emerg_before (h : D.IsRUFLFeasible X Y P) (i : Fin I) (j : Fin (J + 1))
    (r : Fin (R + 1)) (hr : Y i j r = 1) : ¬ U Y i r (Fin.last J) := by
  rintro ⟨l, hl, hY⟩
  have h1 := h.level_one i r
  have hA := Finset.single_le_sum (fun x _ => Y_nonneg h i x r) (mem_univ j)
  have hB := Finset.single_le_sum (fun x _ => Y_nonneg h i (Fin.last J) x)
    (mem_Iio.2 (show l < r from hl))
  rw [hr] at hA
  rw [hY] at hB
  linarith

lemma not_used_before (h : D.IsRUFLFeasible X Y P) (i : Fin I) (j : Fin (J + 1))
    (r : Fin (R + 1)) (hr : Y i j r = 1) : ¬ U Y i r j := by
  rintro ⟨l, hl, hY⟩
  have := Y_level_unique h i j l r hY hr
  rw [this] at hl
  exact lt_irrefl _ hl

lemma level_struct (h : D.IsRUFLFeasible X Y P) (i : Fin I) (r : Fin (R + 1))
    (hU : ¬ U Y i r (Fin.last J)) :
    ∃ k0, Y i k0 r = 1 ∧ ∀ k, k ≠ k0 → Y i k r = 0 := by
  have h1 := h.level_one i r
  have hz : ∑ s ∈ Iio r, Y i (Fin.last J) s = 0 := by
    apply Finset.sum_eq_zero
    intro s hs
    rcases h.Y_binary i (Fin.last J) s with h0 | h0
    · exact h0
    · exact absurd ⟨s, Fin.lt_def.1 (mem_Iio.1 hs), h0⟩ hU
  rw [hz, add_zero] at h1
  exact unique_one (h.Y_binary i · r) h1

lemma exists_emerg (h : D.IsRUFLFeasible X Y P) (i : Fin I) :
    ∃ s, Y i (Fin.last J) s = 1 := by
  obtain ⟨k, hk, -⟩ := unique_one (h.Y_binary i (Fin.last J)) (h.emergency_once i)
  exact ⟨k, hk⟩

/-- `Q_r = Π_{k used before r} q_k` -/
noncomputable def Q (D : Instance I J R) (Y : Fin I → Fin (J + 1) → Fin (R + 1) → ℝ) (i : Fin I)
    (r : ℕ) : ℝ := ∏ k : Fin J, if U Y i r k.castSucc then D.q k else 1

/-- `G_r(ω)`: all facilities at levels `< r` fail in `ω`. -/
noncomputable def G (Y : Fin I → Fin (J + 1) → Fin (R + 1) → ℝ) (i : Fin I) (r : ℕ)
    (ω : FailureScenario J) : ℝ :=
  ∏ k : Fin (J + 1), if U Y i r k then ind (!(delta ω k)) else 1

lemma U_succ (i : Fin I) (r : ℕ) (hr : r < R + 1) (k : Fin (J + 1)) :
    U Y i (r + 1) k ↔ U Y i r k ∨ Y i k ⟨r, hr⟩ = 1 := by
  constructor
  · rintro ⟨l, hl, hY⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hl with h1 | h1
    · exact Or.inl ⟨l, h1, hY⟩
    · right
      have : l = ⟨r, hr⟩ := Fin.ext h1
      rw [← this]; exact hY
  · rintro (⟨l, hl, hY⟩ | hY)
    · exact ⟨l, by omega, hY⟩
    · exact ⟨⟨r, hr⟩, by simp, hY⟩

lemma U_zero (i : Fin I) (k : Fin (J + 1)) : ¬ U Y i 0 k := by
  rintro ⟨l, hl, -⟩; omega

lemma P_formula (h : D.IsRUFLFeasible X Y P) (i : Fin I) :
    ∀ (r : ℕ) (hr : r < R + 1), ¬ U Y i r (Fin.last J) →
      ∀ j, P i j ⟨r, hr⟩ = (1 - D.qExt j) * Q D Y i r := by
  intro r
  induction r with
  | zero =>
    intro hr _ j
    have := h.prob_zero i j
    simp only [Q, U_zero, if_false, prod_const_one, mul_one]
    exact this
  | succ n ih =>
    intro hr hU j
    have hn : n < R + 1 := by omega
    have hUn : ¬ U Y i n (Fin.last J) := fun hu => hU ((U_succ i n hn _).2 (Or.inl hu))
    have hYJ : Y i (Fin.last J) ⟨n, hn⟩ ≠ 1 := fun hy => hU ((U_succ i n hn _).2 (Or.inr hy))
    have hps := h.prob_succ i j ⟨n, by omega⟩
    have e1 : (⟨n, by omega⟩ : Fin R).succ = (⟨n + 1, hr⟩ : Fin (R + 1)) := rfl
    have e2 : (⟨n, by omega⟩ : Fin R).castSucc = (⟨n, hn⟩ : Fin (R + 1)) := rfl
    rw [e1, e2] at hps
    rw [hps]
    obtain ⟨k0, hk0, hoth⟩ := level_struct h i ⟨n, hn⟩ hUn
    -- k0 is regular
    have hk0r : k0 ≠ Fin.last J := fun e => hYJ (e ▸ hk0)
    obtain ⟨k1, rfl⟩ := Fin.exists_castSucc_eq.2 hk0r
    have hsum : ∑ k : Fin J, D.q k / (1 - D.q k) * P i k.castSucc ⟨n, hn⟩ *
        Y i k.castSucc ⟨n, hn⟩ = D.q k1 * Q D Y i n := by
      rw [Finset.sum_eq_single k1]
      · rw [ih hn hUn, hk0]
        have hq : (1 - D.q k1) ≠ 0 := by linarith [D.q_lt_one k1]
        simp only [Instance.qExt, Fin.lastCases_castSucc]
        field_simp
      · intro b _ hb
        rw [hoth b.castSucc (fun e => hb (Fin.castSucc_injective _ e)), mul_zero]
      · intro hh; exact absurd (mem_univ k1) hh
    rw [hsum]
    -- Q (n+1) = q k1 * Q n
    have hk1n : ¬ U Y i n k1.castSucc := not_used_before h i _ _ hk0
    have hQ : Q D Y i (n + 1) = D.q k1 * Q D Y i n := by
      unfold Q
      rw [← Finset.mul_prod_erase _ _ (mem_univ k1), ← Finset.mul_prod_erase _ _ (mem_univ k1)]
      have hA : (if U Y i (n + 1) k1.castSucc then D.q k1 else 1) = D.q k1 := by
        rw [if_pos ((U_succ i n hn _).2 (Or.inr hk0))]
      have hB : (if U Y i n k1.castSucc then D.q k1 else 1) = 1 := by rw [if_neg hk1n]
      rw [hA, hB, one_mul]
      congr 1
      apply Finset.prod_congr rfl
      intro b hb
      have hb' : b ≠ k1 := Finset.ne_of_mem_erase hb
      have hyb : Y i b.castSucc ⟨n, hn⟩ ≠ 1 := by
        rw [hoth b.castSucc (fun e => hb' (Fin.castSucc_injective _ e))]; norm_num
      have : U Y i (n + 1) b.castSucc ↔ U Y i n b.castSucc := by
        rw [U_succ i n hn]; tauto
      rw [if_congr this rfl rfl]
    rw [hQ]


lemma bin_mul {a b : ℝ} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) : a * b = 0 ∨ a * b = 1 := by
  rcases ha with h | h <;> rcases hb with h' | h' <;> simp [h, h']

lemma bin_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ x ∈ s, f x = 0 ∨ f x = 1) :
    (∏ x ∈ s, f x) = 0 ∨ (∏ x ∈ s, f x) = 1 :=
  Finset.prod_induction f (fun x => x = 0 ∨ x = 1) (fun _ _ => bin_mul) (Or.inr rfl) hf

lemma nat_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ x ∈ s, f x = 0 ∨ f x = 1) :
    ∃ n : ℕ, (∑ x ∈ s, f x) = n := by
  refine Finset.sum_induction f (fun x => ∃ n : ℕ, x = n) ?_ ⟨0, by simp⟩ ?_
  · rintro a b ⟨m, rfl⟩ ⟨n, rfl⟩; exact ⟨m + n, by push_cast; ring⟩
  · intro x hx
    rcases hf x hx with h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩

lemma ind_not (b : Bool) : ind (!b) = 1 - ind b := by cases b <;> simp [ind]

lemma delta_last {J : ℕ} (ω : FailureScenario J) : delta ω (Fin.last J) = true := by
  simp [delta]

lemma delta_cs {J : ℕ} (ω : FailureScenario J) (k : Fin J) : delta ω k.castSucc = ω k := by
  simp [delta]

lemma scen_formula {I J R : ℕ} (D : Instance I J R) (S : Fin (J + 1) → Prop)
    (hSl : ¬ S (Fin.last J)) (j : Fin (J + 1)) (hj : ¬ S j) :
    ∑ ω : FailureScenario J, D.scenarioProb ω * ind (delta ω j) *
        ∏ k : Fin (J + 1), (if S k then ind (!(delta ω k)) else 1) =
      (1 - D.qExt j) * ∏ k : Fin J, (if S k.castSucc then D.q k else 1) := by
  set h : ∀ k : Fin J, Bool → ℝ := fun k b =>
    (if b then 1 - D.q k else D.q k) * (if j = k.castSucc then ind b else 1) *
      (if S k.castSucc then ind (!b) else 1) with hh
  have hind : ∀ ω : FailureScenario J,
      ind (delta ω j) = ∏ k : Fin J, (if j = k.castSucc then ind (ω k) else 1) := by
    intro ω
    induction j using Fin.lastCases with
    | last =>
      rw [delta_last]
      symm
      apply Finset.prod_eq_one
      intro k _
      rw [if_neg (fun e => Fin.castSucc_ne_last k e.symm)]
    | cast j0 =>
      rw [delta_cs]
      have : ∀ k : Fin J, (if j0.castSucc = k.castSucc then ind (ω k) else 1) =
          (if j0 = k then ind (ω k) else 1) := by
        intro k; simp [Fin.castSucc_inj]
      simp only [this]
      rw [Fintype.prod_ite_eq]
  have hG : ∀ ω : FailureScenario J,
      ∏ k : Fin (J + 1), (if S k then ind (!(delta ω k)) else 1) =
        ∏ k : Fin J, (if S k.castSucc then ind (!(ω k)) else 1) := by
    intro ω
    rw [Fin.prod_univ_castSucc, if_neg hSl, mul_one]
    simp only [delta_cs]
  have hsum : ∀ ω : FailureScenario J,
      D.scenarioProb ω * ind (delta ω j) *
        ∏ k : Fin (J + 1), (if S k then ind (!(delta ω k)) else 1) = ∏ k, h k (ω k) := by
    intro ω
    rw [hind, hG]
    simp only [Instance.scenarioProb, hh, Finset.prod_mul_distrib]
  simp only [hsum]
  rw [← Fintype.prod_sum h]
  have hb : ∀ k : Fin J, ∑ b, h k b =
      (if j = k.castSucc then 1 - D.q k else 1) * (if S k.castSucc then D.q k else 1) := by
    intro k
    rw [Fintype.sum_bool]
    by_cases h1 : j = k.castSucc
    · have h2 : ¬ S k.castSucc := h1 ▸ hj
      simp [hh, h1, h2, ind]
    · by_cases h2 : S k.castSucc
      · simp [hh, h1, h2, ind]
      · simp [hh, h1, h2, ind]
  simp only [hb]
  rw [Finset.prod_mul_distrib]
  congr 1
  induction j using Fin.lastCases with
  | last =>
    rw [Finset.prod_eq_one]
    · simp [Instance.qExt]
    · intro k _; rw [if_neg (fun e => Fin.castSucc_ne_last k e.symm)]
  | cast j0 =>
    have : ∀ k : Fin J, (if j0.castSucc = k.castSucc then 1 - D.q k else 1) =
        (if j0 = k then 1 - D.q k else 1) := by
      intro k; simp [Fin.castSucc_inj]
    simp only [this]
    rw [Fintype.prod_ite_eq]
    simp [Instance.qExt]

lemma G_zero (i : Fin I) (ω : FailureScenario J) : G Y i 0 ω = 1 := by
  unfold G
  apply Finset.prod_eq_one
  intro k _
  rw [if_neg (U_zero i k)]

lemma G_succ (h : D.IsRUFLFeasible X Y P) (i : Fin I) (r : ℕ) (hr : r < R + 1)
    (ω : FailureScenario J) :
    G Y i (r + 1) ω = G Y i r ω * (1 - ∑ k, Y i k ⟨r, hr⟩ * ind (delta ω k)) := by
  by_cases hJ : U Y i r (Fin.last J)
  · have h0 : G Y i r ω = 0 := by
      unfold G
      apply Finset.prod_eq_zero (mem_univ (Fin.last J))
      rw [if_pos hJ, delta_last]; simp [ind]
    have h1 : G Y i (r + 1) ω = 0 := by
      unfold G
      apply Finset.prod_eq_zero (mem_univ (Fin.last J))
      rw [if_pos ((U_succ i r hr _).2 (Or.inl hJ)), delta_last]; simp [ind]
    rw [h0, h1, zero_mul]
  · obtain ⟨k0, hk0, hoth⟩ := level_struct h i ⟨r, hr⟩ hJ
    have hs : ∑ k, Y i k ⟨r, hr⟩ * ind (delta ω k) = ind (delta ω k0) := by
      rw [Finset.sum_eq_single k0]
      · rw [hk0, one_mul]
      · intro b _ hb; rw [hoth b hb, zero_mul]
      · intro hh; exact absurd (mem_univ k0) hh
    rw [hs, ← ind_not]
    have hk0n : ¬ U Y i r k0 := not_used_before h i _ _ hk0
    unfold G
    have hpt : ∀ k, (if U Y i (r + 1) k then ind (!(delta ω k)) else 1) =
        (if U Y i r k then ind (!(delta ω k)) else 1) *
          (if k = k0 then ind (!(delta ω k)) else 1) := by
      intro k
      by_cases hk : k = k0
      · subst hk
        rw [if_pos ((U_succ i r hr _).2 (Or.inr hk0)), if_neg hk0n, if_pos rfl, one_mul]
      · have hyk : Y i k ⟨r, hr⟩ ≠ 1 := by rw [hoth k hk]; norm_num
        have : U Y i (r + 1) k ↔ U Y i r k := by rw [U_succ i r hr]; tauto
        rw [if_congr this rfl rfl, if_neg hk, mul_one]
    simp only [hpt]
    rw [Finset.prod_mul_distrib, Fintype.prod_ite_eq']

lemma telescope (h : D.IsRUFLFeasible X Y P) (i : Fin I) (ω : FailureScenario J) :
    ∑ r : Fin (R + 1), (∑ k, Y i k r * ind (delta ω k)) * G Y i r ω = 1 := by
  let a : ℕ → ℝ := fun r => if hr : r < R + 1 then
    (∑ k, Y i k ⟨r, hr⟩ * ind (delta ω k)) * G Y i r ω else 0
  have h1 : ∑ r : Fin (R + 1), (∑ k, Y i k r * ind (delta ω k)) * G Y i r ω =
      ∑ r ∈ range (R + 1), a r := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro r _
    simp only [a, dif_pos r.isLt]
  rw [h1]
  have h2 : ∀ r ∈ range (R + 1), a r = G Y i r ω - G Y i (r + 1) ω := by
    intro r hr
    have hr' := mem_range.1 hr
    simp only [a, dif_pos hr']
    rw [G_succ h i r hr' ω]; ring
  rw [Finset.sum_congr rfl h2, Finset.sum_range_sub', G_zero]
  obtain ⟨s, hs⟩ := exists_emerg h i
  have : G Y i (R + 1) ω = 0 := by
    unfold G
    apply Finset.prod_eq_zero (mem_univ (Fin.last J))
    rw [if_pos ⟨s, s.isLt, hs⟩, delta_last]; simp [ind]
  rw [this, sub_zero]

/-- SSP assignment induced by a RUFL assignment: serve by the first operating level. -/
noncomputable def Yss (Y : Fin I → Fin (J + 1) → Fin (R + 1) → ℝ) (i : Fin I) (j : Fin (J + 1))
    (ω : FailureScenario J) : ℝ :=
  ∑ r : Fin (R + 1), Y i j r * ind (delta ω j) * G Y i r ω

lemma G_bin (i : Fin I) (r : ℕ) (ω : FailureScenario J) : G Y i r ω = 0 ∨ G Y i r ω = 1 := by
  unfold G
  apply bin_prod
  intro k _
  split_ifs
  · exact ind_bin _
  · exact Or.inr rfl

lemma Yss_sum (h : D.IsRUFLFeasible X Y P) (i : Fin I) (ω : FailureScenario J) :
    ∑ j, Yss Y i j ω = 1 := by
  unfold Yss
  rw [Finset.sum_comm]
  rw [← telescope h i ω]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_mul]

lemma Yss_bin (h : D.IsRUFLFeasible X Y P) (i : Fin I) (j : Fin (J + 1))
    (ω : FailureScenario J) : Yss Y i j ω = 0 ∨ Yss Y i j ω = 1 := by
  have hterm : ∀ r ∈ (univ : Finset (Fin (R + 1))),
      Y i j r * ind (delta ω j) * G Y i r ω = 0 ∨ Y i j r * ind (delta ω j) * G Y i r ω = 1 :=
    fun r _ => bin_mul (bin_mul (h.Y_binary i j r) (ind_bin _)) (G_bin i r ω)
  have hnn : ∀ j', 0 ≤ Yss Y i j' ω := by
    intro j'
    apply Finset.sum_nonneg
    intro r _
    exact bin_nonneg (bin_mul (bin_mul (h.Y_binary i j' r) (ind_bin _)) (G_bin i r ω))
  obtain ⟨n, hn⟩ := nat_sum _ _ hterm
  have hle : Yss Y i j ω ≤ 1 := by
    rw [← Yss_sum h i ω]
    exact Finset.single_le_sum (fun j' _ => hnn j') (mem_univ j)
  unfold Yss at hle
  rw [hn] at hle
  have : n ≤ 1 := by exact_mod_cast hle
  unfold Yss
  rw [hn]
  interval_cases n <;> simp

lemma Yss_one (h : D.IsRUFLFeasible X Y P) (i : Fin I) (j : Fin (J + 1))
    (ω : FailureScenario J) (h1 : Yss Y i j ω = 1) :
    ∃ r, Y i j r = 1 ∧ delta ω j = true ∧ G Y i r ω = 1 := by
  by_contra hne
  push Not at hne
  have : Yss Y i j ω = 0 := by
    unfold Yss
    apply Finset.sum_eq_zero
    intro r _
    rcases h.Y_binary i j r with h0 | h0
    · rw [h0]; ring
    · cases hd : delta ω j
      · simp [ind]
      · rcases G_bin i r ω with g | g
        · rw [g, mul_zero]
        · exact absurd g (hne r h0 hd)
  rw [this] at h1; norm_num at h1

lemma Yss_feasible (h : D.IsRUFLFeasible X Y P) : D.IsSSPFeasible X (Yss Y) where
  serve_one := fun i ω => Yss_sum h i ω
  open_operating := by
    intro i j ω
    rcases Yss_bin h i j.castSucc ω with h0 | h1
    · rw [h0]
      apply mul_nonneg
      · split_ifs <;> norm_num
      · exact bin_nonneg (h.X_binary j)
    · obtain ⟨r, hY, hd, -⟩ := Yss_one h i _ ω h1
      rw [delta_cs] at hd
      rw [h1, hd, Y_reg_open h i j r hY]; norm_num
  X_binary := h.X_binary
  Y_binary := fun i j ω => Yss_bin h i j ω

lemma Yss_obj (h : D.IsRUFLFeasible X Y P) :
    D.sspObjective X (Yss Y) = D.ruflObjective X Y P := by
  unfold Instance.sspObjective Instance.ruflObjective
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  unfold Yss
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rcases h.Y_binary i j r with h0 | h0
  · simp [h0]
  · have hf := scen_formula D (U Y i r) (no_emerg_before h i j r h0) j (not_used_before h i j r h0)
    have hP := P_formula h i r.val r.isLt (no_emerg_before h i j r h0) j
    simp only [Fin.eta] at hP
    rw [h0, mul_one, hP]
    unfold Q
    rw [← hf, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω _
    unfold G
    ring

theorem rufl_to_ssp' (D : Instance I J R) (X : Fin J → ℝ)
    (Y P : Fin I → Fin (J + 1) → Fin (R + 1) → ℝ) (h : D.IsRUFLFeasible X Y P) :
    ∃ Y' : Fin I → Fin (J + 1) → FailureScenario J → ℝ,
      D.IsSSPFeasible X Y' ∧ D.sspObjective X Y' = D.ruflObjective X Y P :=
  ⟨Yss Y, Yss_feasible h, Yss_obj h⟩

end RUFL

section SSP

variable {I J R : ℕ}

lemma scenarioProb_nonneg (D : Instance I J R) (ω : FailureScenario J) :
    0 ≤ D.scenarioProb ω := by
  unfold Instance.scenarioProb
  apply Finset.prod_nonneg
  intro j _
  split_ifs
  · linarith [D.q_lt_one j]
  · exact D.q_nonneg j

lemma XExt_last {J : ℕ} (X : Fin J → ℝ) : XExt X (Fin.last J) = 1 := by simp [XExt]
lemma XExt_cs {J : ℕ} (X : Fin J → ℝ) (k : Fin J) : XExt X k.castSucc = X k := by simp [XExt]

lemma opOpen_last {J : ℕ} (X : Fin J → ℝ) (ω : FailureScenario J) :
    IsOperatingOpen X ω (Fin.last J) := ⟨delta_last ω, XExt_last X⟩

lemma ssp_one_opOpen {D : Instance I J R} {X : Fin J → ℝ}
    {Y : Fin I → Fin (J + 1) → FailureScenario J → ℝ} (h : D.IsSSPFeasible X Y)
    (i : Fin I) (ω : FailureScenario J) (k : Fin (J + 1)) (hk : Y i k ω = 1) :
    IsOperatingOpen X ω k := by
  induction k using Fin.lastCases with
  | last => exact opOpen_last X ω
  | cast k =>
    have h1 := h.open_operating i k ω
    rw [hk] at h1
    have hw : ω k = true := by
      by_contra hc
      rw [if_neg hc, zero_mul] at h1
      linarith
    have hx : X k = 1 := by
      rcases h.X_binary k with h0 | h0
      · rw [h0, mul_zero] at h1; linarith
      · exact h0
    exact ⟨by rw [delta_cs]; exact hw, by rw [XExt_cs]; exact hx⟩

lemma exists_nearest (D : Instance I J R) (X : Fin J → ℝ) (i : Fin I) (ω : FailureScenario J) :
    ∃ k, D.IsNearestServer X i ω k := by
  set S := univ.filter (fun k => IsOperatingOpen X ω k) with hS
  have hne : S.Nonempty := ⟨Fin.last J, by simp [hS, opOpen_last]⟩
  obtain ⟨k1, hk1S, hmin⟩ := S.exists_min_image (D.dExt i) hne
  set T := S.filter (fun k => D.dExt i k = D.dExt i k1) with hT
  have hTne : T.Nonempty := ⟨k1, by simp [hT, hk1S]⟩
  have hmem := mem_filter.1 (T.min'_mem hTne)
  refine ⟨T.min' hTne, ?_, ?_, ?_⟩
  · simpa [hS] using hmem.1
  · intro k' hk'
    rw [hmem.2]
    exact hmin k' (by simp [hS, hk'])
  · intro k' hk' hle
    apply T.min'_le
    rw [hT, mem_filter]
    refine ⟨by simp [hS, hk'], ?_⟩
    have := hmin k' (by simp [hS, hk'])
    rw [hmem.2] at hle
    linarith

lemma nearest_unique (D : Instance I J R) (X : Fin J → ℝ) (i : Fin I) (ω : FailureScenario J)
    (k1 k2 : Fin (J + 1)) (h1 : D.IsNearestServer X i ω k1) (h2 : D.IsNearestServer X i ω k2) :
    k1 = k2 :=
  le_antisymm (h1.2.2 k2 h2.1 (h2.2.1 k1 h1.1)) (h2.2.2 k1 h1.1 (h1.2.1 k2 h2.1))

/-- per-customer-scenario cost lower bound -/
lemma cost_lb {D : Instance I J R} {X : Fin J → ℝ}
    {Y : Fin I → Fin (J + 1) → FailureScenario J → ℝ} (h : D.IsSSPFeasible X Y)
    (i : Fin I) (ω : FailureScenario J) (k : Fin (J + 1)) (hk : D.IsNearestServer X i ω k) :
    D.dExt i k ≤ ∑ j, D.dExt i j * Y i j ω := by
  have : ∑ j, D.dExt i k * Y i j ω ≤ ∑ j, D.dExt i j * Y i j ω := by
    apply Finset.sum_le_sum
    intro j _
    rcases h.Y_binary i j ω with h0 | h0
    · rw [h0]; simp
    · rw [h0, mul_one, mul_one]
      exact hk.2.1 j (ssp_one_opOpen h i ω j h0)
  rw [← Finset.mul_sum, h.serve_one i ω, mul_one] at this
  exact this

lemma cost_eq_of_one {D : Instance I J R} {X : Fin J → ℝ}
    {Y : Fin I → Fin (J + 1) → FailureScenario J → ℝ} (h : D.IsSSPFeasible X Y)
    (i : Fin I) (ω : FailureScenario J) (k : Fin (J + 1)) (hk : Y i k ω = 1) :
    ∑ j, D.dExt i j * Y i j ω = D.dExt i k := by
  obtain ⟨k0, hk0, hoth⟩ := unique_one (h.Y_binary i · ω) (h.serve_one i ω)
  have : k = k0 := by
    by_contra hne; rw [hoth k hne] at hk; norm_num at hk
  subst this
  rw [Finset.sum_eq_single k]
  · rw [hk, mul_one]
  · intro b _ hb; rw [hoth b hb, mul_zero]
  · intro hh; exact absurd (mem_univ k) hh

lemma ssp_obj_eq (D : Instance I J R) (X : Fin J → ℝ)
    (Y : Fin I → Fin (J + 1) → FailureScenario J → ℝ) :
    D.sspObjective X Y = ∑ j, D.f j * X j +
      ∑ i, ∑ ω, D.lam i * D.scenarioProb ω * ∑ j, D.dExt i j * Y i j ω := by
  unfold Instance.sspObjective
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma ssp_obj_le (D : Instance I J R) (X : Fin J → ℝ)
    (Y Y' : Fin I → Fin (J + 1) → FailureScenario J → ℝ)
    (hle : ∀ i ω, ∑ j, D.dExt i j * Y i j ω ≤ ∑ j, D.dExt i j * Y' i j ω) :
    D.sspObjective X Y ≤ D.sspObjective X Y' := by
  rw [ssp_obj_eq, ssp_obj_eq]
  apply add_le_add (le_refl _)
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro ω _
  exact mul_le_mul_of_nonneg_left (hle i ω)
    (mul_nonneg (D.lam_nonneg i) (scenarioProb_nonneg D ω))

noncomputable def Ynear (D : Instance I J R) (X : Fin J → ℝ) (i : Fin I) (k : Fin (J + 1))
    (ω : FailureScenario J) : ℝ :=
  if D.IsNearestServer X i ω k then 1 else 0

lemma Ynear_feasible (D : Instance I J R) (X : Fin J → ℝ) (hX : ∀ j, X j = 0 ∨ X j = 1) :
    D.IsSSPFeasible X (Ynear D X) where
  serve_one := by
    intro i ω
    obtain ⟨k, hk⟩ := exists_nearest D X i ω
    rw [Finset.sum_eq_single k]
    · simp [Ynear, hk]
    · intro b _ hb
      have : ¬ D.IsNearestServer X i ω b := fun hb' => hb (nearest_unique D X i ω b k hb' hk)
      simp [Ynear, this]
    · intro hh; exact absurd (mem_univ k) hh
  open_operating := by
    intro i j ω
    unfold Ynear
    by_cases hn : D.IsNearestServer X i ω j.castSucc
    · have h1 := hn.1
      rw [IsOperatingOpen, delta_cs, XExt_cs] at h1
      rw [if_pos hn, h1.1, h1.2]; norm_num
    · rw [if_neg hn]
      apply mul_nonneg
      · split_ifs <;> norm_num
      · exact bin_nonneg (hX j)
  X_binary := hX
  Y_binary := by
    intro i j ω; unfold Ynear; split_ifs <;> simp

theorem ssp_nearest_normalization' (D : Instance I J R) (X : Fin J → ℝ)
    (Y : Fin I → Fin (J + 1) → FailureScenario J → ℝ) (h : D.IsSSPOptimal X Y) :
    ∃ Y' : Fin I → Fin (J + 1) → FailureScenario J → ℝ,
      D.IsSSPOptimal X Y' ∧ ∀ i ω k, Y' i k ω = 1 ↔ D.IsNearestServer X i ω k := by
  have hF := Ynear_feasible D X h.1.X_binary
  refine ⟨Ynear D X, ⟨hF, fun X' Y' hf => le_trans ?_ (h.2 X' Y' hf)⟩, ?_⟩
  · apply ssp_obj_le
    intro i ω
    obtain ⟨k, hk⟩ := exists_nearest D X i ω
    rw [cost_eq_of_one hF i ω k (by simp [Ynear, hk])]
    exact cost_lb h.1 i ω k hk
  · intro i ω k
    unfold Ynear
    split_ifs with hn <;> simp [hn]

end SSP

section Rank

variable {α β : Type*} [LinearOrder β] (e : α → β) (O : Finset α)

def rank (k : α) : ℕ := #(O.filter (fun k' => e k' < e k))

lemma rank_lt {k : α} (hk : k ∈ O) : rank e O k < #O := by
  apply Finset.card_lt_card
  refine ⟨filter_subset _ _, fun hsub => ?_⟩
  have := hsub hk
  simp at this

lemma rank_strict {k1 k2 : α} (hk1 : k1 ∈ O) (h : e k1 < e k2) :
    rank e O k1 < rank e O k2 := by
  apply Finset.card_lt_card
  refine ⟨fun x hx => ?_, fun hsub => ?_⟩
  · rw [mem_filter] at hx ⊢
    exact ⟨hx.1, lt_trans hx.2 h⟩
  · have : k1 ∈ O.filter (fun k' => e k' < e k2) := mem_filter.2 ⟨hk1, h⟩
    have := hsub this
    simp at this

lemma rank_le_imp {k1 k2 : α} (hk2 : k2 ∈ O) (h : rank e O k1 ≤ rank e O k2) :
    e k1 ≤ e k2 := by
  by_contra hc
  push Not at hc
  have := rank_strict e O hk2 hc
  omega

lemma rank_inj (he : Function.Injective e) {k1 k2 : α} (hk1 : k1 ∈ O) (hk2 : k2 ∈ O)
    (h : rank e O k1 = rank e O k2) : k1 = k2 := by
  apply he
  exact le_antisymm (rank_le_imp e O hk2 h.le) (rank_le_imp e O hk1 h.ge)

lemma rank_surj (he : Function.Injective e) {r : ℕ} (hr : r < #O) :
    ∃ k ∈ O, rank e O k = r := by
  have := Finset.surjOn_of_injOn_of_card_le (s := O) (t := range #O) (rank e O)
    (fun k hk => by simpa using rank_lt e O hk)
    (fun k1 hk1 k2 hk2 h => rank_inj e O he hk1 hk2 h) (by simp)
  obtain ⟨k, hk, hkr⟩ := this (by simpa using hr)
  exact ⟨k, hk, hkr⟩

lemma rank_count [Fintype α] [DecidableEq α] (he : Function.Injective e) (r : ℕ) :
    ∑ k, (if k ∈ O ∧ rank e O k = r then (1 : ℝ) else 0) = if r < #O then 1 else 0 := by
  by_cases hr : r < #O
  · obtain ⟨k0, hk0, hkr⟩ := rank_surj e O he hr
    rw [if_pos hr, Finset.sum_eq_single k0]
    · rw [if_pos ⟨hk0, hkr⟩]
    · intro b _ hb
      rw [if_neg]
      rintro ⟨hbO, hbr⟩
      exact hb (rank_inj e O he hbO hk0 (hbr.trans hkr.symm))
    · intro hh; exact absurd (mem_univ k0) hh
  · rw [if_neg hr]
    apply Finset.sum_eq_zero
    intro k _
    rw [if_neg]
    rintro ⟨hkO, hkr⟩
    have := rank_lt e O hkO
    omega

end Rank

lemma sum_val_eq {n : ℕ} (c : ℕ) (hc : c < n) :
    ∑ r : Fin n, (if (r : ℕ) = c then (1 : ℝ) else 0) = 1 := by
  have : ∀ r : Fin n, ((r : ℕ) = c) ↔ r = ⟨c, hc⟩ := fun r => by
    constructor
    · intro h; exact Fin.ext h
    · intro h; rw [h]
  simp only [this]
  rw [Fintype.sum_ite_eq']

lemma sum_val_le_one {n : ℕ} (c : ℕ) :
    ∑ r : Fin n, (if (r : ℕ) = c then (1 : ℝ) else 0) ≤ 1 := by
  by_cases hc : c < n
  · rw [sum_val_eq c hc]
  · rw [Finset.sum_eq_zero]
    · norm_num
    · intro r _; rw [if_neg]; intro h; exact hc (h ▸ r.isLt)

lemma iio_count {n : ℕ} (r : Fin (n + 1)) (m : ℕ) :
    ∑ s ∈ Iio r, (if (s : ℕ) = m then (1 : ℝ) else 0) = if m < (r : ℕ) then 1 else 0 := by
  by_cases hm : m < (r : ℕ)
  · have hm' : m < n + 1 := lt_trans hm r.isLt
    rw [if_pos hm, Finset.sum_eq_single (⟨m, hm'⟩ : Fin (n + 1))]
    · simp
    · intro b _ hb
      rw [if_neg]; intro h; exact hb (Fin.ext h)
    · intro hh
      exact absurd (mem_Iio.2 (Fin.lt_def.2 hm)) hh
  · rw [if_neg hm]
    apply Finset.sum_eq_zero
    intro s hs
    have := Fin.lt_def.1 (mem_Iio.1 hs)
    rw [if_neg]; omega

section Construct

variable {I J R : ℕ}

/-- generic solution of the recursion (1e)–(1f) -/
noncomputable def Pn (D : Instance I J R) (Y : Fin I → Fin (J + 1) → Fin (R + 1) → ℝ)
    (i : Fin I) : ℕ → Fin (J + 1) → ℝ
  | 0 => fun j => 1 - D.qExt j
  | n + 1 => fun j => (1 - D.qExt j) * ∑ k : Fin J,
      D.q k / (1 - D.q k) * Pn D Y i n k.castSucc *
        (if h : n < R + 1 then Y i k.castSucc ⟨n, h⟩ else 0)

noncomputable def Pg (D : Instance I J R) (Y : Fin I → Fin (J + 1) → Fin (R + 1) → ℝ) :
    Fin I → Fin (J + 1) → Fin (R + 1) → ℝ := fun i j r => Pn D Y i r.val j

lemma Pg_zero (D : Instance I J R) (Y : Fin I → Fin (J + 1) → Fin (R + 1) → ℝ) (i j) :
    Pg D Y i j 0 = 1 - D.qExt j := rfl

lemma Pg_succ (D : Instance I J R) (Y : Fin I → Fin (J + 1) → Fin (R + 1) → ℝ) (i j)
    (r : Fin R) : Pg D Y i j r.succ = (1 - D.qExt j) * ∑ k : Fin J,
      D.q k / (1 - D.q k) * Pg D Y i k.castSucc r.castSucc * Y i k.castSucc r.castSucc := by
  simp only [Pg, Fin.val_succ, Pn, Fin.val_castSucc]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [dif_pos (by omega)]
  rfl

end Construct

section ToRUFL

variable {I J : ℕ} (D : Instance I J J) (X : Fin J → ℝ)

def key (i : Fin I) : Fin J → ℝ ×ₗ Fin J := fun k => toLex (D.d i k, k)

lemma key_inj (i : Fin I) : Function.Injective (key D i) := by
  intro a b h
  simp only [key] at h
  have := congrArg (fun x => (ofLex x).2) h
  simpa using this

lemma key_le (i : Fin I) {a b : Fin J} (h : key D i a ≤ key D i b) : D.d i a ≤ D.d i b := by
  simp only [key] at h
  rcases Prod.Lex.toLex_le_toLex.1 h with h1 | ⟨h1, -⟩
  · exact h1.le
  · exact h1.le

noncomputable def Oset (i : Fin I) : Finset (Fin J) :=
  univ.filter (fun k : Fin J => X k = 1 ∧ D.d i k ≤ D.phi i)

noncomputable def mcount (i : Fin I) : ℕ := #(Oset D X i)

lemma mcount_le (i : Fin I) : mcount D X i ≤ J := by
  unfold mcount
  calc #(Oset D X i) ≤ #(univ : Finset (Fin J)) := card_le_card (filter_subset _ _)
    _ = J := by simp

noncomputable def rk (i : Fin I) (k : Fin J) : ℕ := rank (key D i) (Oset D X i) k

noncomputable def Ylv (i : Fin I) (j : Fin (J + 1)) (r : Fin (J + 1)) : ℝ :=
  Fin.lastCases (motive := fun _ => ℝ) (if (r : ℕ) = mcount D X i then 1 else 0)
    (fun k => if k ∈ Oset D X i ∧ rk D X i k = (r : ℕ) then 1 else 0) j

lemma Ylv_last (i : Fin I) (r : Fin (J + 1)) :
    Ylv D X i (Fin.last J) r = if (r : ℕ) = mcount D X i then 1 else 0 := by
  simp [Ylv]

lemma Ylv_cs (i : Fin I) (k : Fin J) (r : Fin (J + 1)) :
    Ylv D X i k.castSucc r = if k ∈ Oset D X i ∧ rk D X i k = (r : ℕ) then 1 else 0 := by
  simp [Ylv]

lemma Ylv_feasible (hX : ∀ j, X j = 0 ∨ X j = 1) :
    D.IsRUFLFeasible X (Ylv D X) (Pg D (Ylv D X)) where
  level_one := by
    intro i r
    rw [Fin.sum_univ_castSucc]
    simp only [Ylv_cs, Ylv_last]
    rw [iio_count]
    have h2 : (∑ k, if k ∈ Oset D X i ∧ rk D X i k = (r : ℕ) then (1 : ℝ) else 0) =
        if (r : ℕ) < mcount D X i then 1 else 0 := by
      exact rank_count (key D i) (Oset D X i) (key_inj D i) (r : ℕ)
    rw [h2]
    split_ifs <;> (try norm_num) <;> omega
  open_only := by
    intro i k
    rw [sum_Iio_last]
    simp only [Ylv_cs, Fin.val_castSucc]
    by_cases hk : k ∈ Oset D X i
    · have hX1 : X k = 1 := (mem_filter.1 hk).2.1
      simp only [hk, true_and, hX1]
      have : ∀ r : Fin J, (if rk D X i k = (r : ℕ) then (1 : ℝ) else 0) =
          (if (r : ℕ) = rk D X i k then 1 else 0) := fun r => by
        simp only [eq_comm]
      simp only [this]
      exact sum_val_le_one _
    · simp only [hk, false_and, if_false, Finset.sum_const_zero]
      exact bin_nonneg (hX k)
  emergency_once := by
    intro i
    simp only [Ylv_last]
    exact sum_val_eq _ (by have := mcount_le D X i; omega)
  prob_zero := fun i j => Pg_zero D _ i j
  prob_succ := fun i j r => Pg_succ D _ i j r
  X_binary := hX
  Y_binary := by
    intro i j r
    induction j using Fin.lastCases with
    | last => rw [Ylv_last]; split_ifs <;> simp
    | cast k => rw [Ylv_cs]; split_ifs <;> simp

lemma G_one {R : ℕ} {Y : Fin I → Fin (J + 1) → Fin (R + 1) → ℝ} (i : Fin I) (r : ℕ)
    (ω : FailureScenario J) (h : G Y i r ω = 1) (k : Fin (J + 1)) (hk : U Y i r k) :
    delta ω k = false := by
  by_contra hc
  have : G Y i r ω = 0 := by
    unfold G
    apply Finset.prod_eq_zero (mem_univ k)
    rw [if_pos hk]
    simp only [Bool.not_eq_false] at hc
    rw [hc]; simp [ind]
  rw [this] at h; norm_num at h

lemma dExt_last (i : Fin I) : D.dExt i (Fin.last J) = D.phi i := by simp [Instance.dExt]
lemma dExt_cs (i : Fin I) (k : Fin J) : D.dExt i k.castSucc = D.d i k := by
  simp [Instance.dExt]

lemma rk_lt (i : Fin I) {k : Fin J} (hk : k ∈ Oset D X i) : rk D X i k < J + 1 := by
  have := rank_lt (key D i) (Oset D X i) hk
  have := mcount_le D X i
  unfold mcount at this
  unfold rk; omega

lemma Ylv_used (i : Fin I) {k : Fin J} (hk : k ∈ Oset D X i) (r : ℕ)
    (hr : rk D X i k < r) : U (Ylv D X) i r k.castSucc :=
  ⟨⟨rk D X i k, rk_lt D X i hk⟩, hr, by rw [Ylv_cs]; simp [hk]⟩

lemma Yss_cost (hX : ∀ j, X j = 0 ∨ X j = 1) (i : Fin I) (ω : FailureScenario J)
    (js : Fin (J + 1)) (hjs : Yss (Ylv D X) i js ω = 1) (k : Fin (J + 1))
    (hk : IsOperatingOpen X ω k) : D.dExt i js ≤ D.dExt i k := by
  have hF := Ylv_feasible D X hX
  obtain ⟨r, hY, hd, hG⟩ := Yss_one hF i js ω hjs
  have hfail := G_one i r ω hG
  induction js using Fin.lastCases with
  | last =>
    rw [Ylv_last] at hY
    have hrm : (r : ℕ) = mcount D X i := by
      by_contra hc; rw [if_neg hc] at hY; norm_num at hY
    induction k using Fin.lastCases with
    | last => exact le_refl _
    | cast k0 =>
      have hk0 := hk
      rw [IsOperatingOpen, delta_cs, XExt_cs] at hk0
      rw [dExt_last, dExt_cs]
      by_cases hO : k0 ∈ Oset D X i
      · have hlt : rk D X i k0 < r := by
          have := rank_lt (key D i) (Oset D X i) hO
          unfold rk; unfold mcount at hrm; omega
        have := hfail _ (Ylv_used D X i hO r hlt)
        rw [delta_cs, hk0.1] at this
        exact absurd this (by simp)
      · unfold Oset at hO
        simp only [mem_filter, mem_univ, true_and, not_and, not_le] at hO
        exact (hO hk0.2).le
  | cast k1 =>
    rw [Ylv_cs] at hY
    have hk1 : k1 ∈ Oset D X i ∧ rk D X i k1 = (r : ℕ) := by
      by_contra hc; rw [if_neg hc] at hY; norm_num at hY
    have hk1d : D.d i k1 ≤ D.phi i := (mem_filter.1 hk1.1).2.2
    rw [dExt_cs]
    induction k using Fin.lastCases with
    | last => rw [dExt_last]; exact hk1d
    | cast k0 =>
      have hk0 := hk
      rw [IsOperatingOpen, delta_cs, XExt_cs] at hk0
      rw [dExt_cs]
      by_cases hO : k0 ∈ Oset D X i
      · by_cases hlt : rk D X i k0 < r
        · have := hfail _ (Ylv_used D X i hO r hlt)
          rw [delta_cs, hk0.1] at this
          exact absurd this (by simp)
        · push Not at hlt
          apply key_le D i
          apply rank_le_imp (key D i) (Oset D X i) hO
          unfold rk at hk1 hlt
          omega
      · unfold Oset at hO
        simp only [mem_filter, mem_univ, true_and, not_and, not_le] at hO
        exact hk1d.trans (hO hk0.2).le

theorem ssp_to_rufl' (Y : Fin I → Fin (J + 1) → FailureScenario J → ℝ)
    (h : D.IsSSPFeasible X Y)
    (hY : ∀ i ω k, Y i k ω = 1 ↔ D.IsNearestServer X i ω k) :
    ∃ Y' P' : Fin I → Fin (J + 1) → Fin (J + 1) → ℝ,
      D.IsRUFLFeasible X Y' P' ∧ D.ruflObjective X Y' P' = D.sspObjective X Y := by
  have hF := Ylv_feasible D X h.X_binary
  refine ⟨Ylv D X, Pg D (Ylv D X), hF, ?_⟩
  rw [← Yss_obj hF, ssp_obj_eq, ssp_obj_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro ω _
  congr 1
  have hSF := Yss_feasible hF
  obtain ⟨z, hz, -⟩ := unique_one (hSF.Y_binary i · ω) (hSF.serve_one i ω)
  obtain ⟨y, hy, -⟩ := unique_one (h.Y_binary i · ω) (h.serve_one i ω)
  rw [cost_eq_of_one hSF i ω z hz, cost_eq_of_one h i ω y hy]
  have hyn := (hY i ω y).1 hy
  apply le_antisymm
  · exact Yss_cost D X h.X_binary i ω z hz y hyn.1
  · exact hyn.2.1 z (ssp_one_opOpen hSF i ω z hz)

end ToRUFL

end RFL1Aux

theorem solution {I J : ℕ} (D : Instance I J J) (X : Fin J → ℝ)
    (Y : Fin I → Fin (J + 1) → FailureScenario J → ℝ) (h : D.IsSSPFeasible X Y)
    (hY : ∀ i ω k, Y i k ω = 1 ↔ D.IsNearestServer X i ω k) :
    ∃ Y' P' : Fin I → Fin (J + 1) → Fin (J + 1) → ℝ,
      D.IsRUFLFeasible X Y' P' ∧ D.ruflObjective X Y' P' = D.sspObjective X Y :=
  RFL1Aux.ssp_to_rufl' D X Y h hY
