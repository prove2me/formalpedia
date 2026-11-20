-- Prove2me | solution 1 for TightReleaseSchedules.Stationary.Supplement.codebook_pulses
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T18:09:10.424252+00:00
-- url     : https://prove2.me/submissions/dc1e1804-ec95-42de-ac7f-bed6070a2fa5

import Definitions.Def_TightReleaseSchedules_Stationary_Supplement_pulse_class
import Mathlib

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary TightReleaseSchedules.Stationary.Supplement

noncomputable section

namespace TRS.Dev.CodebookPath

/-- Phase `p` is active at row `i` (as a natural number). -/
def Act {K : ℕ} (N h : ℕ) (Z : Fin K → Bool) (J : Fin K → Fin N) (p : Fin K) (i : ℕ) : Prop :=
  Z p = true ∧ 1 + (p.val * N + (J p).val) * h ≤ i ∧ i < 1 + (p.val * N + (J p).val + 1) * h

lemma lt_unique (N h : ℕ) (p q jp jq i : ℕ) (hjp : jp < N) (hpq : p < q)
    (h2 : i < 1 + (p * N + jp + 1) * h) (h3 : 1 + (q * N + jq) * h ≤ i) : False := by
  have h1 : p * N + jp + 1 ≤ q * N := by
    have : (p + 1) * N ≤ q * N := Nat.mul_le_mul_right _ hpq
    nlinarith
  have h4 : (p * N + jp + 1) * h ≤ (q * N + jq) * h := Nat.mul_le_mul_right _ (by omega)
  omega

lemma act_unique {K : ℕ} (N h : ℕ) (Z : Fin K → Bool) (J : Fin K → Fin N) (p q : Fin K) (i : ℕ)
    (hp : Act N h Z J p i) (hq : Act N h Z J q i) : p = q := by
  obtain ⟨_, a1, a2⟩ := hp
  obtain ⟨_, b1, b2⟩ := hq
  rcases lt_trichotomy p.val q.val with hl | he | hg
  · exact (lt_unique N h p.val q.val (J p).val (J q).val i (J p).2 hl a2 b1).elim
  · exact Fin.ext he
  · exact (lt_unique N h q.val p.val (J q).val (J p).val i (J q).2 hg b2 a1).elim

lemma pulsePath_of_act {T d K N M : ℕ} (h : ℕ) (u : Fin M → Vector d) (Z : Fin K → Bool)
    (J : Fin K → Fin N) (V : Fin K → Fin M) (i : Fin T) (p : Fin K)
    (hp : Act N h Z J p i.val) : pulsePath h u Z J V i = u (V p) := by
  unfold pulsePath
  rw [Finset.sum_eq_single p]
  · exact if_pos hp
  · intro q _ hqp
    rw [if_neg]
    intro hq
    exact hqp (act_unique N h Z J q p i.val hq hp)
  · intro h'; exact absurd (Finset.mem_univ p) h'

lemma pulsePath_of_none {T d K N M : ℕ} (h : ℕ) (u : Fin M → Vector d) (Z : Fin K → Bool)
    (J : Fin K → Fin N) (V : Fin K → Fin M) (i : Fin T)
    (hn : ∀ p, ¬ Act N h Z J p i.val) : pulsePath h u Z J V i = 0 := by
  unfold pulsePath
  exact Finset.sum_eq_zero fun p _ => if_neg (hn p)

lemma pulsePath_zero {T d K N M : ℕ} (h : ℕ) (u : Fin M → Vector d) (Z : Fin K → Bool)
    (J : Fin K → Fin N) (V : Fin K → Fin M) (i : Fin T) (hi : i.val = 0) :
    pulsePath h u Z J V i = 0 := by
  refine pulsePath_of_none h u Z J V i fun p hp => ?_
  have := hp.2.1
  omega

lemma norm_pulsePath_le {T d K N M : ℕ} (h : ℕ) (u : Fin M → Vector d) (Z : Fin K → Bool)
    (J : Fin K → Fin N) (V : Fin K → Fin M) (δ : ℝ) (hδ : 0 ≤ δ) (hu : ∀ v, ‖u v‖ ≤ δ)
    (i : Fin T) : ‖pulsePath h u Z J V i‖ ≤ δ := by
  by_cases hex : ∃ p, Act N h Z J p i.val
  · obtain ⟨p, hp⟩ := hex
    rw [pulsePath_of_act h u Z J V i p hp]; exact hu _
  · push Not at hex
    rw [pulsePath_of_none h u Z J V i hex]; simpa using hδ

/-- start row of phase `p` pulse -/
def sRow {K : ℕ} (N h : ℕ) (J : Fin K → Fin N) (p : Fin K) : ℕ := 1 + (p.val * N + (J p).val) * h
/-- end row (exclusive) of phase `p` pulse -/
def eRow {K : ℕ} (N h : ℕ) (J : Fin K → Fin N) (p : Fin K) : ℕ :=
  1 + (p.val * N + (J p).val + 1) * h

/-- one-sided charges of jump -/
def S1 {T d K N M : ℕ} (h : ℕ) (u : Fin M → Vector d) (Z : Fin K → Bool) (J : Fin K → Fin N)
    (V : Fin K → Fin M) (i : Fin T) : ℝ :=
  ∑ p : Fin K, if Z p = true ∧ i.val + 1 = sRow N h J p then ‖u (V p)‖ else 0

def S2 {T d K N M : ℕ} (h : ℕ) (u : Fin M → Vector d) (Z : Fin K → Bool) (J : Fin K → Fin N)
    (V : Fin K → Fin M) (i : Fin T) : ℝ :=
  ∑ p : Fin K, if Z p = true ∧ i.val + 1 = eRow N h J p then ‖u (V p)‖ else 0

lemma S1_nonneg {T d K N M : ℕ} (h : ℕ) (u : Fin M → Vector d) (Z : Fin K → Bool)
    (J : Fin K → Fin N) (V : Fin K → Fin M) (i : Fin T) : 0 ≤ S1 h u Z J V i :=
  Finset.sum_nonneg fun p _ => by split_ifs <;> positivity

lemma S2_nonneg {T d K N M : ℕ} (h : ℕ) (u : Fin M → Vector d) (Z : Fin K → Bool)
    (J : Fin K → Fin N) (V : Fin K → Fin M) (i : Fin T) : 0 ≤ S2 h u Z J V i :=
  Finset.sum_nonneg fun p _ => by split_ifs <;> positivity

lemma term_le_S1 {T d K N M : ℕ} (h : ℕ) (u : Fin M → Vector d) (Z : Fin K → Bool)
    (J : Fin K → Fin N) (V : Fin K → Fin M) (i : Fin T) (p : Fin K) (hZ : Z p = true)
    (he : i.val + 1 = sRow N h J p) : ‖u (V p)‖ ≤ S1 h u Z J V i := by
  unfold S1
  calc ‖u (V p)‖ = (if Z p = true ∧ i.val + 1 = sRow N h J p then ‖u (V p)‖ else 0) := by
        rw [if_pos ⟨hZ, he⟩]
    _ ≤ _ := Finset.single_le_sum (f := fun p => if Z p = true ∧ i.val + 1 = sRow N h J p
        then ‖u (V p)‖ else 0) (fun p _ => by split_ifs <;> positivity) (Finset.mem_univ p)

lemma term_le_S2 {T d K N M : ℕ} (h : ℕ) (u : Fin M → Vector d) (Z : Fin K → Bool)
    (J : Fin K → Fin N) (V : Fin K → Fin M) (i : Fin T) (p : Fin K) (hZ : Z p = true)
    (he : i.val + 1 = eRow N h J p) : ‖u (V p)‖ ≤ S2 h u Z J V i := by
  unfold S2
  calc ‖u (V p)‖ = (if Z p = true ∧ i.val + 1 = eRow N h J p then ‖u (V p)‖ else 0) := by
        rw [if_pos ⟨hZ, he⟩]
    _ ≤ _ := Finset.single_le_sum (f := fun p => if Z p = true ∧ i.val + 1 = eRow N h J p
        then ‖u (V p)‖ else 0) (fun p _ => by split_ifs <;> positivity) (Finset.mem_univ p)

/-- the jump bound -/
lemma jump_le {T d K N M : ℕ} (h : ℕ) (u : Fin M → Vector d) (Z : Fin K → Bool)
    (J : Fin K → Fin N) (V : Fin K → Fin M) (i : Fin T) (hi : i.val + 1 < T) :
    ‖pulsePath h u Z J V ⟨i.val + 1, hi⟩ - pulsePath h u Z J V i‖ ≤
      S1 h u Z J V i + S2 h u Z J V i := by
  have s1 := S1_nonneg h u Z J V i
  have s2 := S2_nonneg h u Z J V i
  set i' : Fin T := ⟨i.val + 1, hi⟩ with hi'
  by_cases hb : ∃ q, Act N h Z J q i'.val
  · obtain ⟨q, hq⟩ := hb
    rw [pulsePath_of_act h u Z J V i' q hq]
    have hqs : ¬ Act N h Z J q i.val → i.val + 1 = sRow N h J q := by
      intro hn
      obtain ⟨a, b, c⟩ := hq
      have a' : sRow N h J q ≤ i.val + 1 := b
      have c' : i.val + 1 < eRow N h J q := c
      by_contra hne
      have h3 : sRow N h J q ≤ i.val := by omega
      exact hn ⟨a, h3, by show i.val < eRow N h J q; omega⟩
    by_cases ha : ∃ p, Act N h Z J p i.val
    · obtain ⟨p, hp⟩ := ha
      rw [pulsePath_of_act h u Z J V i p hp]
      by_cases hpq : p = q
      · subst hpq; simp; positivity
      · have hqs' := hqs (fun hq' => hpq (act_unique N h Z J p q i.val hp hq'))
        have hpe : i.val + 1 = eRow N h J p := by
          obtain ⟨a, b, c⟩ := hp
          have c' : i.val < eRow N h J p := c
          have b' : sRow N h J p ≤ i.val := b
          by_contra hne
          exact hpq (act_unique N h Z J p q i'.val ⟨a, by show sRow N h J p ≤ i.val + 1; omega,
            by show i.val + 1 < eRow N h J p; omega⟩ hq)
        calc ‖u (V q) - u (V p)‖ ≤ ‖u (V q)‖ + ‖u (V p)‖ := norm_sub_le _ _
          _ ≤ S1 h u Z J V i + S2 h u Z J V i :=
            add_le_add (term_le_S1 h u Z J V i q hq.1 hqs') (term_le_S2 h u Z J V i p hp.1 hpe)
    · push Not at ha
      rw [pulsePath_of_none h u Z J V i ha, sub_zero]
      have := term_le_S1 h u Z J V i q hq.1 (hqs (ha q))
      linarith
  · push Not at hb
    rw [pulsePath_of_none h u Z J V i' hb, zero_sub, norm_neg]
    by_cases ha : ∃ p, Act N h Z J p i.val
    · obtain ⟨p, hp⟩ := ha
      rw [pulsePath_of_act h u Z J V i p hp]
      have hpe : i.val + 1 = eRow N h J p := by
        obtain ⟨a, b, c⟩ := hp
        have c' : i.val < eRow N h J p := c
        have b' : sRow N h J p ≤ i.val := b
        by_contra hne
        exact hb p ⟨a, by show sRow N h J p ≤ i.val + 1; omega,
          by show i.val + 1 < eRow N h J p; omega⟩
      have := term_le_S2 h u Z J V i p hp.1 hpe
      linarith
    · push Not at ha
      rw [pulsePath_of_none h u Z J V i ha]
      simp
      positivity

lemma sum_single_le {T : ℕ} (s : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    ∑ i : Fin T, (if i.val + 1 = s then c else 0) ≤ c := by
  by_cases hex : ∃ i0 : Fin T, i0.val + 1 = s
  · obtain ⟨i0, hi0⟩ := hex
    rw [Finset.sum_eq_single i0]
    · rw [if_pos hi0]
    · intro i _ hne
      rw [if_neg]
      intro hh; exact hne (Fin.ext (by omega))
    · intro h'; exact absurd (Finset.mem_univ i0) h'
  · push Not at hex
    rw [Finset.sum_eq_zero fun i _ => if_neg (hex i)]
    exact hc

lemma totalVariation_le {T d K N M : ℕ} (h : ℕ) (u : Fin M → Vector d) (Z : Fin K → Bool)
    (J : Fin K → Fin N) (V : Fin K → Fin M) (δ : ℝ) (hδ : 0 ≤ δ) (hu : ∀ v, ‖u v‖ ≤ δ) :
    totalVariation (pulsePath (T := T) h u Z J V) ≤ 2 * K * δ := by
  unfold totalVariation
  calc _ ≤ ∑ i : Fin T, (S1 h u Z J V i + S2 h u Z J V i) := by
        refine Finset.sum_le_sum fun i _ => ?_
        split_ifs with hi
        · exact jump_le h u Z J V i hi
        · exact add_nonneg (S1_nonneg h u Z J V i) (S2_nonneg h u Z J V i)
    _ = ∑ p : Fin K, ((∑ i : Fin T, (if i.val + 1 = sRow N h J p then
            (if Z p = true then ‖u (V p)‖ else 0) else 0)) +
          (∑ i : Fin T, (if i.val + 1 = eRow N h J p then
            (if Z p = true then ‖u (V p)‖ else 0) else 0))) := by
        unfold S1 S2
        simp only [Finset.sum_add_distrib]
        congr 1
        · rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun i _ => ?_
          by_cases h1 : Z p = true <;> by_cases h2 : i.val + 1 = sRow N h J p <;> simp [h1, h2]
        · rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun i _ => ?_
          by_cases h1 : Z p = true <;> by_cases h2 : i.val + 1 = eRow N h J p <;> simp [h1, h2]
    _ ≤ ∑ p : Fin K, (δ + δ) := by
        refine Finset.sum_le_sum fun p _ => ?_
        have hc : 0 ≤ (if Z p = true then ‖u (V p)‖ else 0) := by split_ifs <;> positivity
        have hcδ : (if Z p = true then ‖u (V p)‖ else 0) ≤ δ := by
          split_ifs
          · exact hu _
          · exact hδ
        exact add_le_add ((sum_single_le _ _ hc).trans hcδ) ((sum_single_le _ _ hc).trans hcδ)
    _ = 2 * K * δ := by simp; ring

lemma change_mem {T d K N M : ℕ} (h : ℕ) (u : Fin M → Vector d) (Z : Fin K → Bool)
    (J : Fin K → Fin N) (V : Fin K → Fin M) (i : Fin T) (hi : i.val + 1 < T)
    (hne : pulsePath h u Z J V ⟨i.val + 1, hi⟩ ≠ pulsePath h u Z J V i) :
    ∃ p : Fin K, Z p = true ∧ (i.val + 1 = sRow N h J p ∨ i.val + 1 = eRow N h J p) := by
  by_contra hcon
  push Not at hcon
  have h1 : S1 h u Z J V i = 0 := Finset.sum_eq_zero fun p _ => by
    rw [if_neg]
    intro ⟨hz, he⟩
    exact (hcon p hz).1 he
  have h2 : S2 h u Z J V i = 0 := Finset.sum_eq_zero fun p _ => by
    rw [if_neg]
    intro ⟨hz, he⟩
    exact (hcon p hz).2 he
  have := jump_le h u Z J V i hi
  rw [h1, h2, add_zero] at this
  exact hne (sub_eq_zero.1 (norm_le_zero_iff.1 this))

lemma changeCount_le {T d K N M : ℕ} (h : ℕ) (u : Fin M → Vector d) (Z : Fin K → Bool)
    (J : Fin K → Fin N) (V : Fin K → Fin M) :
    changeCount (pulsePath (T := T) h u Z J V) ≤ 2 * K := by
  unfold changeCount
  classical
  set A : Fin K → Finset (Fin T) := fun p =>
    Finset.univ.filter (fun i : Fin T => i.val + 1 = sRow N h J p) with hA
  set Bm : Fin K → Finset (Fin T) := fun p =>
    Finset.univ.filter (fun i : Fin T => i.val + 1 = eRow N h J p) with hB
  have hsub : (Finset.univ.filter (fun i : Fin T => ∃ hh : i.val + 1 < T,
      pulsePath h u Z J V ⟨i.val + 1, hh⟩ ≠ pulsePath h u Z J V i)) ⊆
      Finset.univ.biUnion (fun p : Fin K => A p ∪ Bm p) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨hh, hne⟩ := hi
    obtain ⟨p, _, hp⟩ := change_mem h u Z J V i hh hne
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union, hA, hB,
      Finset.mem_filter]
    exact ⟨p, by rcases hp with hp | hp; exact Or.inl hp; exact Or.inr hp⟩
  have c1 : ∀ p : Fin K, (A p).card ≤ 1 := fun p => by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [hA, Finset.mem_filter] at ha hb
    exact Fin.ext (by omega)
  have c2 : ∀ p : Fin K, (Bm p).card ≤ 1 := fun p => by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [hB, Finset.mem_filter] at ha hb
    exact Fin.ext (by omega)
  calc _ ≤ (Finset.univ.biUnion (fun p : Fin K => A p ∪ Bm p)).card := Finset.card_le_card hsub
    _ ≤ ∑ p : Fin K, (A p ∪ Bm p).card := Finset.card_biUnion_le
    _ ≤ ∑ p : Fin K, 2 := Finset.sum_le_sum fun p _ =>
        (Finset.card_union_le _ _).trans (by have := c1 p; have := c2 p; omega)
    _ = 2 * K := by simp; ring

end TRS.Dev.CodebookPath

end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary TightReleaseSchedules.Stationary.Supplement

noncomputable section

namespace TRS.Dev.CodebookPolicy
open TRS.Dev.CodebookPath

/-- start date of the slot pair of phase `n` -/
def sd {K : ℕ} (T N h : ℕ) (Z : Fin K → Bool) (J : Fin K → Fin N) (n : ℕ) : ℕ :=
  if hn : n < K then
    (if Z ⟨n, hn⟩ = true then 1 + (n * N + (J ⟨n, hn⟩).val) * h else 1 + n * N * h)
  else T

def ed {K : ℕ} (T N h : ℕ) (Z : Fin K → Bool) (J : Fin K → Fin N) (n : ℕ) : ℕ :=
  if hn : n < K then
    (if Z ⟨n, hn⟩ = true then 1 + (n * N + (J ⟨n, hn⟩).val + 1) * h else 1 + n * N * h)
  else T

def dt {K : ℕ} (T N h : ℕ) (Z : Fin K → Bool) (J : Fin K → Fin N) (n : ℕ) : ℕ :=
  if n % 2 = 0 then sd T N h Z J (n / 2) else ed T N h Z J (n / 2)

def hd {d K M : ℕ} (u : Fin M → Vector d) (Z : Fin K → Bool) (V : Fin K → Fin M) (n : ℕ) :
    Vector d :=
  if n % 2 = 0 then
    (if hn : n / 2 < K then (if Z ⟨n / 2, hn⟩ = true then u (V ⟨n / 2, hn⟩) else 0) else 0)
  else 0

section arith
variable {K : ℕ} (T N h : ℕ) (Z : Fin K → Bool) (J : Fin K → Fin N)

lemma sd_of (p : Fin K) (hZ : Z p = true) : sd T N h Z J p.val = sRow N h J p := by
  unfold sd sRow
  rw [dif_pos p.2]
  simp [hZ]

lemma ed_of (p : Fin K) (hZ : Z p = true) : ed T N h Z J p.val = eRow N h J p := by
  unfold ed eRow
  rw [dif_pos p.2]
  simp [hZ]

lemma sd_le_T (hT : 1 + K * N * h ≤ T) (n : ℕ) : sd T N h Z J n ≤ T := by
  unfold sd
  split_ifs with hn hz
  · have h1 : n * N + (J ⟨n, hn⟩).val + 1 ≤ K * N := by
      have := (J ⟨n, hn⟩).2
      have h2 : (n + 1) * N ≤ K * N := Nat.mul_le_mul_right _ hn
      nlinarith
    have : (n * N + (J ⟨n, hn⟩).val) * h ≤ K * N * h := Nat.mul_le_mul_right _ (by omega)
    omega
  · have h2 : (n + 1) * N ≤ K * N := Nat.mul_le_mul_right _ hn
    have : n * N * h ≤ K * N * h := Nat.mul_le_mul_right _ (by nlinarith)
    omega
  · exact le_rfl

lemma ed_le_T (hT : 1 + K * N * h ≤ T) (n : ℕ) : ed T N h Z J n ≤ T := by
  unfold ed
  split_ifs with hn hz
  · have h1 : n * N + (J ⟨n, hn⟩).val + 1 ≤ K * N := by
      have := (J ⟨n, hn⟩).2
      have h2 : (n + 1) * N ≤ K * N := Nat.mul_le_mul_right _ hn
      nlinarith
    have : (n * N + (J ⟨n, hn⟩).val + 1) * h ≤ K * N * h := Nat.mul_le_mul_right _ h1
    omega
  · have h2 : (n + 1) * N ≤ K * N := Nat.mul_le_mul_right _ hn
    have : n * N * h ≤ K * N * h := Nat.mul_le_mul_right _ (by nlinarith)
    omega
  · exact le_rfl

lemma sd_le_ed (hT : 1 + K * N * h ≤ T) (n : ℕ) : sd T N h Z J n ≤ ed T N h Z J n := by
  unfold sd ed
  split_ifs with hn hz
  · have : (n * N + (J ⟨n, hn⟩).val) * h ≤ (n * N + (J ⟨n, hn⟩).val + 1) * h :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  · exact le_rfl
  · exact le_rfl

lemma ed_le_sd_succ (hT : 1 + K * N * h ≤ T) (n : ℕ) :
    ed T N h Z J n ≤ sd T N h Z J (n + 1) := by
  by_cases hn1 : n + 1 < K
  · have hn : n < K := by omega
    have e1 : ed T N h Z J n ≤ 1 + (n + 1) * N * h := by
      unfold ed
      rw [dif_pos hn]
      split_ifs with hz
      · have h1 : n * N + (J ⟨n, hn⟩).val + 1 ≤ (n + 1) * N := by
          have := (J ⟨n, hn⟩).2
          nlinarith
        have : (n * N + (J ⟨n, hn⟩).val + 1) * h ≤ (n + 1) * N * h := Nat.mul_le_mul_right _ h1
        omega
      · have : n * N * h ≤ (n + 1) * N * h := Nat.mul_le_mul_right _ (by nlinarith)
        omega
    have e2 : 1 + (n + 1) * N * h ≤ sd T N h Z J (n + 1) := by
      unfold sd
      rw [dif_pos hn1]
      split_ifs with hz
      · have : (n + 1) * N * h ≤ ((n + 1) * N + (J ⟨n + 1, hn1⟩).val) * h :=
          Nat.mul_le_mul_right _ (by omega)
        omega
      · exact le_rfl
    exact e1.trans e2
  · have : sd T N h Z J (n + 1) = T := by unfold sd; rw [dif_neg hn1]
    rw [this]
    exact ed_le_T T N h Z J hT n

lemma dt_even (m : ℕ) : dt T N h Z J (2 * m) = sd T N h Z J m := by
  unfold dt
  have : 2 * m % 2 = 0 := by omega
  rw [if_pos this]
  congr 1
  omega

lemma dt_odd (m : ℕ) : dt T N h Z J (2 * m + 1) = ed T N h Z J m := by
  unfold dt
  have : ¬ (2 * m + 1) % 2 = 0 := by omega
  rw [if_neg this]
  congr 1
  omega

lemma dt_succ_le (hT : 1 + K * N * h ≤ T) (m : ℕ) :
    dt T N h Z J m ≤ dt T N h Z J (m + 1) := by
  rcases Nat.even_or_odd' m with ⟨k, hk | hk⟩
  · subst hk
    rw [dt_even, show 2 * k + 1 = 2 * k + 1 from rfl, dt_odd]
    exact sd_le_ed T N h Z J hT k
  · subst hk
    rw [dt_odd, show 2 * k + 1 + 1 = 2 * (k + 1) by ring, dt_even]
    exact ed_le_sd_succ T N h Z J hT k

lemma dt_mono (hT : 1 + K * N * h ≤ T) : Monotone (dt T N h Z J) :=
  monotone_nat_of_le_succ (dt_succ_le T N h Z J hT)

lemma dt_le_T (hT : 1 + K * N * h ≤ T) (n : ℕ) : dt T N h Z J n ≤ T := by
  unfold dt
  split_ifs
  · exact sd_le_T T N h Z J hT _
  · exact ed_le_T T N h Z J hT _

end arith

lemma foldl_none_list {α β : Type} (P : α → Prop) [DecidablePred P] (f : α → β) (w0 : β)
    (l : List α) (h : ∀ x ∈ l, ¬ P x) :
    l.foldl (fun w j => if P j then f j else w) w0 = w0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldl_cons, if_neg (h a (by simp))]
    exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx))

lemma foldl_last_list {B : ℕ} {β : Type} (P : Fin B → Prop) [DecidablePred P] (f : Fin B → β)
    (l : List (Fin B)) (hl : l.Pairwise (· < ·)) (s : Fin B) (hs : s ∈ l) (hPs : P s)
    (hlast : ∀ s', s < s' → ¬ P s') (w0 : β) :
    l.foldl (fun w j => if P j then f j else w) w0 = f s := by
  induction l generalizing w0 with
  | nil => simp at hs
  | cons a l ih =>
    rw [List.pairwise_cons] at hl
    rcases List.mem_cons.1 hs with rfl | hs'
    · simp only [List.foldl_cons, if_pos hPs]
      exact foldl_none_list P f _ l (fun x hx => hlast x (hl.1 x hx))
    · simp only [List.foldl_cons]
      exact ih hl.2 hs' _

lemma foldl_last {B : ℕ} {β : Type} (P : Fin B → Prop) [DecidablePred P] (f : Fin B → β)
    (s : Fin B) (hPs : P s) (hlast : ∀ s', s < s' → ¬ P s') (w0 : β) :
    (List.finRange B).foldl (fun w j => if P j then f j else w) w0 = f s :=
  foldl_last_list P f _ (List.pairwise_lt_finRange B) s (List.mem_finRange s) hPs hlast w0

lemma foldl_none {B : ℕ} {β : Type} (P : Fin B → Prop) [DecidablePred P] (f : Fin B → β)
    (hn : ∀ s, ¬ P s) (w0 : β) :
    (List.finRange B).foldl (fun w j => if P j then f j else w) w0 = w0 :=
  foldl_none_list P f w0 _ (fun x _ => hn x)

/-- the constant policy -/
def pol {d K M : ℕ} (T B N h : ℕ) (u : Fin M → Vector d) (Z : Fin K → Bool) (J : Fin K → Fin N)
    (V : Fin K → Fin M) : ReleasePolicy unitSeed T d B where
  date := fun j _ => dt T N h Z J j.val
  head := fun j _ => hd u Z V j.val

lemma hd_even {d K M : ℕ} (u : Fin M → Vector d) (Z : Fin K → Bool) (V : Fin K → Fin M)
    (p : Fin K) (hZ : Z p = true) : hd u Z V (2 * p.val) = u (V p) := by
  unfold hd
  have h1 : 2 * p.val % 2 = 0 := by omega
  have h2 : 2 * p.val / 2 < K := by omega
  rw [if_pos h1, dif_pos h2]
  have : (⟨2 * p.val / 2, h2⟩ : Fin K) = p := Fin.ext (by simp)
  rw [this, if_pos hZ]

lemma isCausal_pol {d K M : ℕ} (T B N h : ℕ) (u : Fin M → Vector d) (Z : Fin K → Bool)
    (J : Fin K → Fin N) (V : Fin K → Fin M) (hT : 1 + K * N * h ≤ T) :
    IsCausal (pol T B N h u Z J V) := by
  refine ⟨fun j _ => dt_le_T T N h Z J hT _, fun _ a b hab => dt_mono T N h Z J hT hab, ?_, ?_⟩
  · intro j n
    show @MeasurableSet _ (information unitSeed T d n) {_ω | dt T N h Z J j.val ≤ n}
    exact @MeasurableSet.const _ (information unitSeed T d n) _
  · intro j n
    show @Measurable _ _ (information unitSeed T d n) inferInstance
      (fun _ω => if dt T N h Z J j.val ≤ n then hd u Z V j.val else 0)
    by_cases hc : dt T N h Z J j.val ≤ n
    · simp only [hc, if_true]
      exact @measurable_const _ _ _ (information unitSeed T d n) _
    · simp only [hc, if_false]
      exact @measurable_const _ _ _ (information unitSeed T d n) _

lemma hasDet_pol {d K M : ℕ} (T B N h : ℕ) (u : Fin M → Vector d) (Z : Fin K → Bool)
    (J : Fin K → Fin N) (V : Fin K → Fin M) :
    HasDeterministicDates (pol T B N h u Z J V) :=
  fun j => ⟨dt T N h Z J j.val, fun _ => rfl⟩

lemma deployed_pol {d K M : ℕ} (T B N h : ℕ) (u : Fin M → Vector d) (Z : Fin K → Bool)
    (J : Fin K → Fin N) (V : Fin K → Fin M) (hT : 1 + K * N * h ≤ T) (hKB : 2 * K ≤ B)
    (ω : Transcript unitSeed T d) (i : Fin T) :
    deployed 0 (pol T B N h u Z J V) ω i = pulsePath h u Z J V i := by
  show List.foldl (fun w (j : Fin B) => if dt T N h Z J j.val ≤ i.val then hd u Z V j.val else w) 0
    (List.finRange B) = _
  by_cases hex : ∃ p, Act N h Z J p i.val
  · obtain ⟨p, hp⟩ := hex
    rw [pulsePath_of_act h u Z J V i p hp]
    have hs : 2 * p.val < B := by have := p.2; omega
    have hs1 : dt T N h Z J (2 * p.val + 1) = eRow N h J p := by
      rw [dt_odd]; exact ed_of T N h Z J p hp.1
    have := foldl_last (fun j : Fin B => dt T N h Z J j.val ≤ i.val) (fun j => hd u Z V j.val)
      ⟨2 * p.val, hs⟩ (by
        show dt T N h Z J (2 * p.val) ≤ i.val
        rw [dt_even, sd_of T N h Z J p hp.1]; exact hp.2.1) (by
        intro s' hs'
        have h1 : 2 * p.val + 1 ≤ s'.val := hs'
        have h2 := dt_mono T N h Z J hT h1
        rw [hs1] at h2
        have h3 : i.val < eRow N h J p := hp.2.2
        show ¬ (dt T N h Z J s'.val ≤ i.val)
        omega) 0
    rw [this]
    exact hd_even u Z V p hp.1
  · push Not at hex
    rw [pulsePath_of_none h u Z J V i hex]
    by_cases hP : ∃ j : Fin B, dt T N h Z J j.val ≤ i.val
    · obtain ⟨s, hsP, hsmax⟩ := Finset.exists_max_image
        (Finset.univ.filter (fun j : Fin B => dt T N h Z J j.val ≤ i.val)) (fun j => j.val)
        (by obtain ⟨j, hj⟩ := hP; exact ⟨j, by simp [hj]⟩)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hsP
      have hlast : ∀ s' : Fin B, s < s' → ¬ (dt T N h Z J s'.val ≤ i.val) := by
        intro s' hs' hc
        have := hsmax s' (by simp [hc])
        have h2 : s.val < s'.val := hs'
        omega
      rw [foldl_last (fun j : Fin B => dt T N h Z J j.val ≤ i.val) (fun j => hd u Z V j.val)
        s hsP hlast 0]
      show hd u Z V s.val = 0
      unfold hd
      by_cases he : s.val % 2 = 0
      · rw [if_pos he]
        by_cases hn : s.val / 2 < K
        · rw [dif_pos hn]
          by_cases hZ : Z ⟨s.val / 2, hn⟩ = true
          · exfalso
            set p : Fin K := ⟨s.val / 2, hn⟩ with hpdef
            have hs2 : s.val = 2 * p.val := by simp [hpdef]; omega
            have hsd : dt T N h Z J s.val = sRow N h J p := by
              rw [hs2, dt_even]; exact sd_of T N h Z J p hZ
            have hB1 : 2 * p.val + 1 < B := by have := p.2; omega
            have h1 := hlast ⟨2 * p.val + 1, hB1⟩ (by
              show s.val < 2 * p.val + 1
              omega)
            have h2 : ¬ (dt T N h Z J (2 * p.val + 1) ≤ i.val) := h1
            rw [dt_odd, ed_of T N h Z J p hZ] at h2
            apply hex p
            exact ⟨hZ, by rw [hsd] at hsP; exact hsP, by show i.val < eRow N h J p; omega⟩
          · rw [if_neg hZ]
        · rw [dif_neg hn]
      · rw [if_neg he]
    · push Not at hP
      exact foldl_none _ _ (fun s => not_le.2 (hP s)) _

end TRS.Dev.CodebookPolicy

end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary TightReleaseSchedules.Stationary.Supplement

noncomputable section

namespace TRS.Dev.CodebookDep
open TRS.Dev.CodebookPolicy

/-- truncation map defining the information σ-algebra -/
def trunc {s : RandomSeed} {T d : ℕ} (n : ℕ) (ω : Transcript s T d) :
    s.space × Data T d :=
  (ω.1, fun i : Fin T => if i.val < n then ω.2 i else (0, 0))

lemma info_set_congr {s : RandomSeed} {T d : ℕ} (n : ℕ) (A : Set (Transcript s T d))
    (hA : @MeasurableSet _ (information s T d n) A) (ω ω' : Transcript s T d)
    (h : trunc n ω = trunc n ω') : ω ∈ A ↔ ω' ∈ A := by
  have hA' : @MeasurableSet _ (MeasurableSpace.comap (trunc n : Transcript s T d → _) inferInstance) A :=
    hA
  obtain ⟨S, _, hS⟩ := hA'
  rw [← hS]
  simp only [Set.mem_preimage, h]

lemma info_fun_congr {s : RandomSeed} {T d : ℕ} (n : ℕ) (F : Transcript s T d → Vector d)
    (hF : @Measurable _ _ (information s T d n) inferInstance F) (ω ω' : Transcript s T d)
    (h : trunc n ω = trunc n ω') : F ω = F ω' := by
  have hm : @MeasurableSet _ (information s T d n) (F ⁻¹' {F ω}) :=
    hF (measurableSet_singleton (F ω))
  have := (info_set_congr n _ hm ω ω' h).1 (by simp)
  simpa using this.symm

lemma deployed_congr {s : RandomSeed} {T d B : ℕ} (θ₀ : Vector d) (π : ReleasePolicy s T d B)
    (hπ : IsCausal π) (i : Fin T) (ω ω' : Transcript s T d)
    (h : trunc i.val ω = trunc i.val ω') : deployed θ₀ π ω i = deployed θ₀ π ω' i := by
  have key : ∀ (j : Fin B) (w : Vector d),
      (if π.date j ω ≤ i.val then π.head j ω else w) =
        (if π.date j ω' ≤ i.val then π.head j ω' else w) := by
    intro j w
    have hset := info_set_congr i.val _ (hπ.2.2.1 j i.val) ω ω' h
    have hfun := info_fun_congr i.val _ (hπ.2.2.2 j i.val) ω ω' h
    by_cases hd : π.date j ω ≤ i.val
    · have hd' : π.date j ω' ≤ i.val := hset.1 hd
      rw [if_pos hd, if_pos hd']
      simpa [hd, hd'] using hfun
    · have hd' : ¬ π.date j ω' ≤ i.val := fun h' => hd (hset.2 h')
      rw [if_neg hd, if_neg hd']
  unfold deployed
  have : (fun (w : Vector d) (j : Fin B) => if π.date j ω ≤ i.val then π.head j ω else w) =
      (fun (w : Vector d) (j : Fin B) => if π.date j ω' ≤ i.val then π.head j ω' else w) :=
    funext fun w => funext fun j => key j w
  rw [this]

/-- cover lemma -/
lemma cover {s : RandomSeed} {T d B : ℕ} (θ₀ : Vector d) (π : ReleasePolicy s T d B)
    (near : Vector d → Prop) (ω : Transcript s T d) (a h : ℕ) (ia i : Fin T)
    (hia : ia.val = a) (hi : a ≤ i.val) (hih : i.val < a + h)
    (hpre : ¬ near (deployed θ₀ π ω ia))
    (hin : ∀ j : Fin B, a < π.date j ω → π.date j ω < a + h → ¬ near (π.head j ω)) :
    ¬ near (deployed θ₀ π ω i) := by
  unfold deployed at hpre ⊢
  by_cases hP : ∃ j : Fin B, π.date j ω ≤ i.val
  · obtain ⟨s', hsP, hsmax⟩ := Finset.exists_max_image
      (Finset.univ.filter (fun j : Fin B => π.date j ω ≤ i.val)) (fun j => j.val)
      (by obtain ⟨j, hj⟩ := hP; exact ⟨j, by simp [hj]⟩)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hsP
    have hlast : ∀ s'' : Fin B, s' < s'' → ¬ (π.date s'' ω ≤ i.val) := by
      intro s'' hs'' hc
      have := hsmax s'' (by simp [hc])
      have h2 : s'.val < s''.val := hs''
      omega
    rw [foldl_last (fun j : Fin B => π.date j ω ≤ i.val) (fun j => π.head j ω) s' hsP hlast θ₀]
    by_cases hda : π.date s' ω ≤ a
    · rw [foldl_last (fun j : Fin B => π.date j ω ≤ ia.val) (fun j => π.head j ω) s'
        (by simpa [hia] using hda) (fun s'' hs'' hc => hlast s'' hs'' (by omega)) θ₀] at hpre
      exact hpre
    · exact hin s' (by omega) (by omega)
  · push Not at hP
    rw [foldl_none (fun j : Fin B => π.date j ω ≤ i.val) (fun j => π.head j ω)
      (fun j => not_le.2 (hP j)) θ₀]
    rw [foldl_none (fun j : Fin B => π.date j ω ≤ ia.val) (fun j => π.head j ω)
      (fun j => by have := hP j; omega) θ₀] at hpre
    exact hpre

end TRS.Dev.CodebookDep

end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary

noncomputable section

namespace TRS.Dev.CodebookShear

lemma pdf_shift (m ε : ℝ) :
    gaussianPDF m 1 ε = gaussianPDF 0 1 ε * ENNReal.ofReal (Real.exp (ε * m - m ^ 2 / 2)) := by
  unfold gaussianPDF gaussianPDFReal
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [NNReal.coe_one, mul_one]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

lemma gauss_shift_lintegral (m : ℝ) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ ε, F (ε + m) ∂(gaussianReal 0 1) =
      ∫⁻ ε, F ε * ENNReal.ofReal (Real.exp (ε * m - m ^ 2 / 2)) ∂(gaussianReal 0 1) := by
  have h1 : ∫⁻ ε, F (ε + m) ∂(gaussianReal 0 1) = ∫⁻ ε, F ε ∂(gaussianReal m 1) := by
    have := gaussianReal_map_add_const (μ := 0) (v := 1) m
    rw [zero_add] at this
    rw [← this, lintegral_map hF (measurable_add_const m)]
  rw [h1, gaussianReal_of_var_ne_zero _ one_ne_zero, gaussianReal_of_var_ne_zero _ one_ne_zero,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF _ _) hF,
    lintegral_withDensity_eq_lintegral_mul (g := fun ε => F ε * ENNReal.ofReal (Real.exp (ε * m - m ^ 2 / 2)))
      _ (measurable_gaussianPDF _ _) (hF.mul (by fun_prop))]
  refine lintegral_congr fun ε => ?_
  simp only [Pi.mul_apply]
  rw [pdf_shift]; ring

abbrev Row (d : ℕ) := Vector d × ℝ

def rowMeasure (d : ℕ) : Measure (Row d) := (stdGaussian (Vector d)).prod (gaussianReal 0 1)

instance (d : ℕ) : IsProbabilityMeasure (rowMeasure d) := by
  unfold rowMeasure; infer_instance

def rowShear {d : ℕ} (e : Vector d) (r : Row d) : Row d := (r.1, r.2 + inner ℝ r.1 e)

def rowD {d : ℕ} (e : Vector d) (r : Row d) : ℝ :=
  Real.exp (r.2 * inner ℝ r.1 e - (inner ℝ r.1 e) ^ 2 / 2)

lemma measurable_rowShear {d : ℕ} (e : Vector d) : Measurable (rowShear e) := by
  unfold rowShear; fun_prop

lemma measurable_rowD {d : ℕ} (e : Vector d) : Measurable (rowD e) := by
  unfold rowD; fun_prop

lemma row_shear_lintegral {d : ℕ} (e : Vector d) (F : Row d → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ r, F (rowShear e r) ∂(rowMeasure d) =
      ∫⁻ r, F r * ENNReal.ofReal (rowD e r) ∂(rowMeasure d) := by
  unfold rowMeasure
  rw [lintegral_prod (fun r : Row d => F (rowShear e r)) ((hF.comp (measurable_rowShear e)).aemeasurable),
    lintegral_prod (fun r : Row d => F r * ENNReal.ofReal (rowD e r))
      ((hF.mul (measurable_rowD e).ennreal_ofReal).aemeasurable)]
  refine lintegral_congr fun x => ?_
  have := gauss_shift_lintegral (inner ℝ x e) (fun ε => F (x, ε)) (hF.comp measurable_prodMk_left)
  simpa [rowShear, rowD] using this

lemma row_shear_map {d : ℕ} (e : Vector d) :
    (rowMeasure d).map (rowShear e) =
      (rowMeasure d).withDensity (fun r => ENNReal.ofReal (rowD e r)) := by
  ext s hs
  rw [Measure.map_apply (measurable_rowShear e) hs, withDensity_apply _ hs,
    ← lintegral_indicator hs, ← lintegral_indicator_one (measurable_rowShear e hs)]
  have := row_shear_lintegral e (s.indicator 1) (measurable_one.indicator hs)
  have h2 : ∫⁻ a, (rowShear e ⁻¹' s).indicator 1 a ∂rowMeasure d =
      ∫⁻ r, s.indicator 1 (rowShear e r) ∂rowMeasure d := by
    refine lintegral_congr fun r => ?_
    by_cases h : rowShear e r ∈ s <;> simp [h, Set.indicator]
  rw [h2, this]
  refine lintegral_congr fun r => ?_
  by_cases h : r ∈ s <;> simp [h, Set.indicator]

lemma gauss_exp_sq (σ2 : ℝ≥0) (h : 2 * (σ2 : ℝ) < 1) :
    ∫ t, Real.exp (t ^ 2) ∂(gaussianReal 0 σ2) = 1 / Real.sqrt (1 - 2 * σ2) := by
  by_cases h0 : σ2 = 0
  · subst h0; simp [gaussianReal_zero_var]
  have hpos : (0 : ℝ) < σ2 := by positivity
  rw [integral_gaussianReal_eq_integral_smul h0]
  have hb : (0 : ℝ) < 1 / (2 * σ2) - 1 := by
    rw [sub_pos, lt_div_iff₀ (by positivity)]; linarith
  have : ∀ x : ℝ, gaussianPDFReal 0 σ2 x • Real.exp (x ^ 2) =
      (Real.sqrt (2 * Real.pi * σ2))⁻¹ * Real.exp (-(1 / (2 * σ2) - 1) * x ^ 2) := by
    intro x
    unfold gaussianPDFReal
    rw [smul_eq_mul, mul_assoc, ← Real.exp_add]
    congr 2
    field_simp
    ring
  simp_rw [this]
  rw [integral_const_mul, integral_gaussian]
  rw [← Real.sqrt_inv, ← Real.sqrt_mul (by positivity), one_div]
  congr 1
  field_simp
  have h1 : (1 - (σ2 : ℝ) * 2) ≠ 0 := by linarith
  ring_nf
  first | rfl | (rw [Real.sqrt_inv]) 

lemma eps_sq_lintegral (m : ℝ) :
    ∫⁻ ε, ENNReal.ofReal (Real.exp (ε * m - m ^ 2 / 2)) ^ 2 ∂(gaussianReal 0 1) =
      ENNReal.ofReal (Real.exp (m ^ 2)) := by
  have hint : Integrable (fun ε : ℝ => Real.exp (-(m ^ 2)) * Real.exp ((2 * m) * ε))
      (gaussianReal 0 1) := (integrable_exp_mul_gaussianReal (2 * m)).const_mul _
  have h1 : ∀ ε : ℝ, ENNReal.ofReal (Real.exp (ε * m - m ^ 2 / 2)) ^ 2 =
      ENNReal.ofReal (Real.exp (-(m ^ 2)) * Real.exp ((2 * m) * ε)) := by
    intro ε
    rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 2
    push_cast
    ring
  simp_rw [h1]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun ε =>
    by positivity), integral_const_mul]
  congr 1
  have := congrFun (mgf_id_gaussianReal (μ := 0) (v := 1)) (2 * m)
  simp only [mgf, id] at this
  rw [this, ← Real.exp_add]
  congr 1
  simp; ring

lemma stdGaussian_inner_exp_sq {d : ℕ} (e : Vector d) (h : 2 * ‖e‖ ^ 2 < 1) :
    ∫ x, Real.exp (inner ℝ x e ^ 2) ∂(stdGaussian (Vector d)) = 1 / Real.sqrt (1 - 2 * ‖e‖ ^ 2) := by
  set L : StrongDual ℝ (Vector d) := innerSL ℝ e
  have hL : ∀ x, L x = inner ℝ x e := fun x => by simp [L, real_inner_comm]
  have hmap := IsGaussian.map_eq_gaussianReal (μ := stdGaussian (Vector d)) L
  rw [integral_strongDual_stdGaussian, variance_dual_stdGaussian] at hmap
  have hn : ‖L‖ = ‖e‖ := by simp [L]
  rw [hn] at hmap
  have hnn : ((‖e‖ ^ 2).toNNReal : ℝ) = ‖e‖ ^ 2 := Real.coe_toNNReal _ (by positivity)
  have := gauss_exp_sq (‖e‖ ^ 2).toNNReal (by rw [hnn]; exact h)
  rw [hnn] at this
  rw [← this, ← hmap, integral_map L.continuous.aemeasurable (by fun_prop)]
  simp [hL]

lemma pi_withDensity {ι : Type} [Fintype ι] {X : Type} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] (f : ι → X → ℝ) (hf : ∀ i, Measurable (f i))
    (hnn : ∀ i x, 0 ≤ f i x) (hint : ∀ i, Integrable (f i) ν) :
    (Measure.pi (fun _ : ι => ν)).withDensity (fun z => ENNReal.ofReal (∏ i, f i (z i))) =
      Measure.pi (fun i => ν.withDensity (fun x => ENNReal.ofReal (f i x))) := by
  refine (Measure.pi_eq fun s hs => ?_).symm
  have hbox : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  rw [withDensity_apply _ hbox]
  have h1 : ∀ z : ι → X, (Set.univ.pi s).indicator (fun z => ENNReal.ofReal (∏ i, f i (z i))) z =
      ENNReal.ofReal (∏ i, (s i).indicator (f i) (z i)) := by
    intro z
    by_cases hz : z ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hz]
      have : ∏ i, f i (z i) = ∏ i, (s i).indicator (f i) (z i) :=
        Finset.prod_congr rfl fun i _ => (Set.indicator_of_mem (hz i (Set.mem_univ i)) _).symm
      rw [this]
    · rw [Set.indicator_of_notMem hz]
      have : ∃ i, z i ∉ s i := by
        by_contra hc
        push Not at hc
        exact hz fun i _ => hc i
      obtain ⟨i, hi⟩ := this
      have : ∏ i, (s i).indicator (f i) (z i) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)
      rw [this]; simp
  rw [← lintegral_indicator hbox]
  simp_rw [h1]
  have hint2 : ∀ i, Integrable ((s i).indicator (f i)) ν := fun i => (hint i).indicator (hs i)
  have hnn2 : ∀ i x, 0 ≤ (s i).indicator (f i) x := fun i x =>
    Set.indicator_nonneg (fun y _ => hnn i y) x
  rw [← ofReal_integral_eq_lintegral_ofReal
    (Integrable.fintype_prod (f := fun i x => (s i).indicator (f i) x) hint2)
    (Filter.Eventually.of_forall fun z => Finset.prod_nonneg fun i _ => hnn2 i _),
    integral_fintype_prod_eq_prod (fun i x => (s i).indicator (f i) x),
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (hnn2 i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hs i), integral_indicator (hs i),
    ofReal_integral_eq_lintegral_ofReal (hint i).restrict
    (Filter.Eventually.of_forall fun x => hnn i x)]

lemma rowD_lintegral {d : ℕ} (e : Vector d) :
    ∫⁻ r, ENNReal.ofReal (rowD e r) ∂(rowMeasure d) = 1 := by
  have := congrArg (fun m => m Set.univ) (row_shear_map e)
  simp only [Measure.map_apply (measurable_rowShear e) MeasurableSet.univ, Set.preimage_univ,
    measure_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
  exact this.symm

lemma rowD_integrable {d : ℕ} (e : Vector d) : Integrable (rowD e) (rowMeasure d) := by
  refine ⟨(measurable_rowD e).aestronglyMeasurable, ?_⟩
  have h : ∀ r, ‖rowD e r‖ₑ = ENNReal.ofReal (rowD e r) := fun r => by
    rw [Real.enorm_eq_ofReal (show 0 ≤ rowD e r from (Real.exp_pos _).le)]
  simp only [HasFiniteIntegral, h, rowD_lintegral]
  exact ENNReal.one_lt_top

lemma rowD_sq_lintegral {d : ℕ} (e : Vector d) (h : 2 * ‖e‖ ^ 2 < 1) :
    ∫⁻ r, ENNReal.ofReal (rowD e r ^ 2) ∂(rowMeasure d) =
      ENNReal.ofReal (1 / Real.sqrt (1 - 2 * ‖e‖ ^ 2)) := by
  have hpos : 0 < 1 / Real.sqrt (1 - 2 * ‖e‖ ^ 2) := by
    have : 0 < 1 - 2 * ‖e‖ ^ 2 := by linarith
    positivity
  have hint : Integrable (fun x : Vector d => Real.exp (inner ℝ x e ^ 2)) (stdGaussian (Vector d)) := by
    apply Integrable.of_integral_ne_zero
    rw [stdGaussian_inner_exp_sq e h]; exact hpos.ne'
  unfold rowMeasure
  rw [lintegral_prod (fun r : Row d => ENNReal.ofReal (rowD e r ^ 2))
    (((measurable_rowD e).pow_const 2).ennreal_ofReal.aemeasurable)]
  have h1 : ∀ x : Vector d, ∫⁻ ε, ENNReal.ofReal (rowD e (x, ε) ^ 2) ∂(gaussianReal 0 1) =
      ENNReal.ofReal (Real.exp (inner ℝ x e ^ 2)) := by
    intro x
    rw [← eps_sq_lintegral (inner ℝ x e)]
    refine lintegral_congr fun ε => ?_
    rw [← ENNReal.ofReal_pow (Real.exp_pos _).le]
    rfl
  simp_rw [h1]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x =>
    (Real.exp_pos _).le), stdGaussian_inner_exp_sq e h]

lemma rowD_sq_integrable {d : ℕ} (e : Vector d) (h : 2 * ‖e‖ ^ 2 < 1) :
    Integrable (fun r => rowD e r ^ 2) (rowMeasure d) := by
  refine ⟨((measurable_rowD e).pow_const 2).aestronglyMeasurable, ?_⟩
  have h1 : ∀ r, ‖rowD e r ^ 2‖ₑ = ENNReal.ofReal (rowD e r ^ 2) := fun r => by
    rw [Real.enorm_eq_ofReal (show 0 ≤ rowD e r ^ 2 by positivity)]
  simp only [HasFiniteIntegral, h1, rowD_sq_lintegral e h]
  exact ENNReal.ofReal_lt_top

lemma rowD_sq_integral {d : ℕ} (e : Vector d) (h : 2 * ‖e‖ ^ 2 < 1) :
    ∫ r, rowD e r ^ 2 ∂(rowMeasure d) = 1 / Real.sqrt (1 - 2 * ‖e‖ ^ 2) := by
  have hpos : 0 < 1 / Real.sqrt (1 - 2 * ‖e‖ ^ 2) := by
    have : 0 < 1 - 2 * ‖e‖ ^ 2 := by linarith
    positivity
  have := rowD_sq_lintegral e h
  rw [← ofReal_integral_eq_lintegral_ofReal (rowD_sq_integrable e h)
    (Filter.Eventually.of_forall fun r => by positivity)] at this
  exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun r => by positivity) hpos.le).1 this

def shearG {T d : ℕ} (e : Fin T → Vector d) (z : GaussianRows T d) : GaussianRows T d :=
  fun i => rowShear (e i) (z i)

def densG {T d : ℕ} (e : Fin T → Vector d) (z : GaussianRows T d) : ℝ :=
  ∏ i, rowD (e i) (z i)

lemma measurable_shearG {T d : ℕ} (e : Fin T → Vector d) : Measurable (shearG e) :=
  measurable_pi_lambda _ fun i => (measurable_rowShear (e i)).comp (measurable_pi_apply i)

lemma measurable_densG {T d : ℕ} (e : Fin T → Vector d) : Measurable (densG e) :=
  Finset.measurable_prod _ fun i _ => (measurable_rowD (e i)).comp (measurable_pi_apply i)

lemma densG_nonneg {T d : ℕ} (e : Fin T → Vector d) (z : GaussianRows T d) : 0 ≤ densG e z :=
  Finset.prod_nonneg fun i _ => (Real.exp_pos _).le

lemma shearG_map {T d : ℕ} (e : Fin T → Vector d) :
    (gaussianRows T d).map (shearG e) =
      (gaussianRows T d).withDensity (fun z => ENNReal.ofReal (densG e z)) := by
  unfold gaussianRows
  have h1 : Measure.pi (fun _ : Fin T => (stdGaussian (Vector d)).prod (gaussianReal 0 1)) =
      Measure.pi (fun _ : Fin T => rowMeasure d) := rfl
  rw [h1]
  have h2 : shearG (T := T) e = fun z i => rowShear (e i) (z i) := rfl
  rw [h2]
  have : ∀ i : Fin T, SigmaFinite ((rowMeasure d).map (rowShear (e i))) := fun i => inferInstance
  rw [Measure.pi_map_pi (fun i => (measurable_rowShear (e i)).aemeasurable)]
  unfold densG
  rw [pi_withDensity (rowMeasure d) (fun i => rowD (e i)) (fun i => measurable_rowD (e i))
    (fun i r => (Real.exp_pos _).le) (fun i => rowD_integrable (e i))]
  congr 1
  funext i
  exact row_shear_map (e i)

lemma shearG_lintegral {T d : ℕ} (e : Fin T → Vector d) (F : GaussianRows T d → ℝ≥0∞)
    (hF : Measurable F) :
    ∫⁻ z, F (shearG e z) ∂(gaussianRows T d) =
      ∫⁻ z, ENNReal.ofReal (densG e z) * F z ∂(gaussianRows T d) := by
  rw [← lintegral_map hF (measurable_shearG e), shearG_map,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_densG e).ennreal_ofReal hF]
  rfl

lemma densG_sq_integral {T d : ℕ} (e : Fin T → Vector d) (h : ∀ i, 2 * ‖e i‖ ^ 2 < 1) :
    ∫ z, densG e z ^ 2 ∂(gaussianRows T d) =
      ∏ i, (1 / Real.sqrt (1 - 2 * ‖e i‖ ^ 2)) := by
  unfold densG gaussianRows
  have h1 : Measure.pi (fun _ : Fin T => (stdGaussian (Vector d)).prod (gaussianReal 0 1)) =
      Measure.pi (fun _ : Fin T => rowMeasure d) := rfl
  rw [h1]
  simp_rw [← Finset.prod_pow]
  rw [integral_fintype_prod_eq_prod (fun i (r : Row d) => rowD (e i) r ^ 2)]
  exact Finset.prod_congr rfl fun i _ => rowD_sq_integral (e i) (h i)

lemma densG_sq_lintegral {T d : ℕ} (e : Fin T → Vector d) (h : ∀ i, 2 * ‖e i‖ ^ 2 < 1) :
    ∫⁻ z, ENNReal.ofReal (densG e z) ^ 2 ∂(gaussianRows T d) =
      ENNReal.ofReal (∏ i, (1 / Real.sqrt (1 - 2 * ‖e i‖ ^ 2))) := by
  have hint : Integrable (fun z : GaussianRows T d => densG e z ^ 2) (gaussianRows T d) := by
    unfold densG gaussianRows
    have h1 : Measure.pi (fun _ : Fin T => (stdGaussian (Vector d)).prod (gaussianReal 0 1)) =
        Measure.pi (fun _ : Fin T => rowMeasure d) := rfl
    rw [h1]
    simp_rw [← Finset.prod_pow]
    exact Integrable.fintype_prod (f := fun i (r : Row d) => rowD (e i) r ^ 2)
      fun i => rowD_sq_integrable (e i) (h i)
  rw [← densG_sq_integral e h]
  rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun z => by positivity)]
  refine lintegral_congr fun z => ?_
  exact (ENNReal.ofReal_pow (densG_nonneg e z) 2).symm

end TRS.Dev.CodebookShear

end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary

noncomputable section

namespace TRS.Dev.CodebookShear

lemma obs_shear {T d : ℕ} (θ θ' : Fin T → Vector d) (z : GaussianRows T d) :
    observations θ' z = observations θ (shearG (fun i => θ' i - θ i) z) := by
  funext i
  simp only [observations, shearG, rowShear, inner_sub_right]
  congr 1
  ring

lemma measurable_observations {T d : ℕ} (θ : Fin T → Vector d) :
    Measurable (observations (T := T) (d := d) θ) := by
  refine measurable_pi_lambda _ fun i => ?_
  unfold observations
  have h1 : Measurable fun z : GaussianRows T d => (z i).1 :=
    measurable_fst.comp (measurable_pi_apply i)
  have h2 : Measurable fun z : GaussianRows T d => (z i).2 :=
    measurable_snd.comp (measurable_pi_apply i)
  exact h1.prodMk ((h1.inner measurable_const).add h2)

/-- Event: the transcript generated by path `θ` lies in `S`. -/
def EvS {s : RandomSeed} {T d : ℕ} (S : Set (s.space × Data T d)) (θ : Fin T → Vector d) :
    Set (s.space × GaussianRows T d) :=
  {ω | (ω.1, observations θ ω.2) ∈ S}

lemma measurableSet_EvS {s : RandomSeed} {T d : ℕ} (S : Set (s.space × Data T d))
    (hS : MeasurableSet S) (θ : Fin T → Vector d) : MeasurableSet (EvS S θ) :=
  (measurable_fst.prodMk ((measurable_observations θ).comp measurable_snd)) hS

instance gaussianRows_prob (T d : ℕ) : IsProbabilityMeasure (gaussianRows T d) := by
  unfold gaussianRows; infer_instance

/-- probability of an event of transcripts under path `θ` -/
def prob {s : RandomSeed} {T d : ℕ} (S : Set (s.space × Data T d)) (θ : Fin T → Vector d) : ℝ :=
  ((s.law.prod (gaussianRows T d)) (EvS S θ)).toReal

lemma prob_nonneg {s : RandomSeed} {T d : ℕ} (S : Set (s.space × Data T d))
    (θ : Fin T → Vector d) : 0 ≤ prob S θ := ENNReal.toReal_nonneg

lemma prob_le_one' {s : RandomSeed} {T d : ℕ} (S : Set (s.space × Data T d))
    (θ : Fin T → Vector d) : prob S θ ≤ 1 := by
  unfold prob
  have : IsProbabilityMeasure (s.law.prod (gaussianRows T d)) := inferInstance
  have := MeasureTheory.prob_le_one (μ := s.law.prod (gaussianRows T d)) (s := EvS S θ)
  exact ENNReal.toReal_mono ENNReal.one_ne_top this |>.trans (by simp)

/-- Cauchy–Schwarz change of measure for a shear. -/
lemma cs_shift {s : RandomSeed} {T d : ℕ} (S : Set (s.space × Data T d)) (hS : MeasurableSet S)
    (θ θ' : Fin T → Vector d) (h : ∀ i, 2 * ‖θ' i - θ i‖ ^ 2 < 1) :
    prob S θ' ^ 2 ≤ (∏ i, (1 / Real.sqrt (1 - 2 * ‖θ' i - θ i‖ ^ 2))) * prob S θ := by
  set e : Fin T → Vector d := fun i => θ' i - θ i with he
  set μ := s.law.prod (gaussianRows T d) with hμ
  have hEm := measurableSet_EvS S hS θ
  set χ0 : ℝ := ∏ i, (1 / Real.sqrt (1 - 2 * ‖e i‖ ^ 2)) with hχ0
  have hχ0pos : 0 ≤ χ0 :=
    Finset.prod_nonneg fun i _ => by positivity
  have hDm : Measurable fun ω : s.space × GaussianRows T d => ENNReal.ofReal (densG e ω.2) :=
    ((measurable_densG e).comp measurable_snd).ennreal_ofReal
  have hind : Measurable ((EvS S θ).indicator (1 : s.space × GaussianRows T d → ℝ≥0∞)) :=
    measurable_one.indicator hEm
  have hpre : ∀ σ z, (EvS S θ').indicator (1 : s.space × GaussianRows T d → ℝ≥0∞) (σ, z) =
      (EvS S θ).indicator (1 : s.space × GaussianRows T d → ℝ≥0∞) (σ, shearG e z) := by
    intro σ z
    have : ((σ, z) ∈ EvS S θ') ↔ ((σ, shearG e z) ∈ EvS S θ) := by
      simp only [EvS, Set.mem_setOf_eq, obs_shear θ θ' z]
      exact Iff.rfl
    by_cases hh : (σ, z) ∈ EvS S θ'
    · rw [Set.indicator_of_mem hh, Set.indicator_of_mem (this.1 hh)]; rfl
    · rw [Set.indicator_of_notMem hh, Set.indicator_of_notMem (fun h' => hh (this.2 h'))]
  have hshift : μ (EvS S θ') =
      ∫⁻ ω, ENNReal.ofReal (densG e ω.2) * (EvS S θ).indicator 1 ω ∂μ := by
    have hprod : Measurable fun ω : s.space × GaussianRows T d =>
        ENNReal.ofReal (densG e ω.2) * (EvS S θ).indicator 1 ω := hDm.mul hind
    rw [← lintegral_indicator_one (measurableSet_EvS S hS θ'), hμ,
      lintegral_prod _ (measurable_one.indicator (measurableSet_EvS S hS θ')).aemeasurable,
      lintegral_prod _ hprod.aemeasurable]
    refine lintegral_congr fun σ => ?_
    have hF : Measurable fun z : GaussianRows T d => (EvS S θ).indicator
        (1 : s.space × GaussianRows T d → ℝ≥0∞) (σ, z) := hind.comp measurable_prodMk_left
    simp_rw [hpre]
    rw [shearG_lintegral e _ hF]
  have hCS := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    hDm.aemeasurable hind.aemeasurable
  have e1 : ∫⁻ ω, ENNReal.ofReal (densG e ω.2) ^ (2 : ℝ) ∂μ = ENNReal.ofReal χ0 := by
    simp_rw [ENNReal.rpow_two]
    rw [hμ, lintegral_prod _ (hDm.pow_const 2).aemeasurable]
    simp only [lintegral_const, measure_univ, mul_one]
    exact densG_sq_lintegral e h
  have e2 : ∫⁻ ω, ((EvS S θ).indicator (1 : s.space × GaussianRows T d → ℝ≥0∞) ω) ^ (2 : ℝ) ∂μ
      = μ (EvS S θ) := by
    rw [← lintegral_indicator_one hEm]
    refine lintegral_congr fun a => ?_
    by_cases hh : a ∈ EvS S θ <;> simp [Set.indicator, hh]
  rw [e1, e2] at hCS
  have hCS' : μ (EvS S θ') ≤ _ := hshift ▸ hCS
  clear hCS
  have hp : μ (EvS S θ) ≠ ⊤ := measure_ne_top _ _
  have hsq : (μ (EvS S θ')) ^ 2 ≤ ENNReal.ofReal χ0 * μ (EvS S θ) := by
    have h3 : μ (EvS S θ') ≤ (ENNReal.ofReal χ0 * μ (EvS S θ)) ^ (1 / (2 : ℝ)) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]; exact hCS'
    calc (μ (EvS S θ')) ^ 2 ≤ ((ENNReal.ofReal χ0 * μ (EvS S θ)) ^ (1 / (2 : ℝ))) ^ 2 := by gcongr
      _ = _ := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
  have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hp) hsq
  rw [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_ofReal hχ0pos] at this
  exact this

lemma inv_sqrt_le_exp (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1 / 4) :
    1 / Real.sqrt (1 - 2 * x) ≤ Real.exp (2 * x) := by
  have hpos : 0 < 1 - 2 * x := by linarith
  have ht := Real.quadratic_le_exp_of_nonneg (x := 4 * x) (by linarith)
  have hexp : Real.exp (-(4 * x)) ≤ 1 - 2 * x := by
    rw [Real.exp_neg]
    have hp : 0 < Real.exp (4 * x) := Real.exp_pos _
    rw [inv_le_iff_one_le_mul₀ hp]
    nlinarith [mul_nonneg h0 h0, mul_nonneg (mul_nonneg h0 h0) h0, mul_nonneg h0 (sub_nonneg.2 h1)]
  have hs : Real.exp (-(2 * x)) ≤ Real.sqrt (1 - 2 * x) := by
    apply Real.le_sqrt_of_sq_le
    rw [← Real.exp_nat_mul]
    push_cast
    convert hexp using 2; ring
  rw [div_le_iff₀ (Real.sqrt_pos.2 hpos)]
  calc (1 : ℝ) = Real.exp (2 * x) * Real.exp (-(2 * x)) := by rw [← Real.exp_add]; simp
    _ ≤ _ := by gcongr

lemma prod_inv_sqrt_le {T : ℕ} (x : Fin T → ℝ) (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1 / 4)
    (s : ℝ) (hs : ∑ i, x i ≤ s) :
    ∏ i, (1 / Real.sqrt (1 - 2 * x i)) ≤ Real.exp (2 * s) := by
  calc _ ≤ ∏ i, Real.exp (2 * x i) :=
        Finset.prod_le_prod (fun i _ => by
          have : 0 < 1 - 2 * x i := by linarith [h1 i]
          positivity) (fun i _ => inv_sqrt_le_exp _ (h0 i) (h1 i))
    _ = Real.exp (2 * ∑ i, x i) := by rw [← Real.exp_sum, Finset.mul_sum]
    _ ≤ _ := Real.exp_le_exp.2 (by linarith)

/-- Exponential form of the change of measure. -/
lemma cs_exp {s : RandomSeed} {T d : ℕ} (S : Set (s.space × Data T d)) (hS : MeasurableSet S)
    (θ θ' : Fin T → Vector d) (h1 : ∀ i, ‖θ' i - θ i‖ ^ 2 ≤ 1 / 4) (c : ℝ)
    (hc : ∑ i, ‖θ' i - θ i‖ ^ 2 ≤ c) :
    prob S θ' ^ 2 ≤ Real.exp (2 * c) * prob S θ := by
  have h2 : ∀ i, 2 * ‖θ' i - θ i‖ ^ 2 < 1 := fun i => by linarith [h1 i]
  refine (cs_shift S hS θ θ' h2).trans ?_
  have := prod_inv_sqrt_le (fun i => ‖θ' i - θ i‖ ^ 2) (fun i => by positivity) h1 c hc
  exact mul_le_mul_of_nonneg_right this (prob_nonneg S θ)

end TRS.Dev.CodebookShear

end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary TightReleaseSchedules.Stationary.Supplement

noncomputable section

namespace TRS.Dev.CodebookEvents
open TRS.Dev.CodebookDep TRS.Dev.CodebookShear TRS.Dev.CodebookPath

lemma info_le {s : RandomSeed} {T d : ℕ} (n : ℕ) :
    information s T d n ≤ (inferInstance : MeasurableSpace (Transcript s T d)) := by
  have hF : Measurable (fun ω : Transcript s T d =>
      (ω.1, fun i : Fin T => if i.val < n then ω.2 i else (0, 0))) := by
    refine measurable_fst.prodMk (measurable_pi_lambda _ fun i => ?_)
    by_cases h : i.val < n
    · simp only [h, if_true]
      exact (measurable_pi_apply i).comp measurable_snd
    · simp [h]
  exact hF.comap_le

lemma measurable_deployed {s : RandomSeed} {T d B : ℕ} (θ₀ : Vector d) (π : ReleasePolicy s T d B)
    (hπ : IsCausal π) (i : Fin T) :
    Measurable (fun ω : Transcript s T d => deployed θ₀ π ω i) := by
  have hdate : ∀ j, MeasurableSet {ω : Transcript s T d | π.date j ω ≤ i.val} :=
    fun j => info_le i.val _ (hπ.2.2.1 j i.val)
  have hhead : ∀ j, Measurable (fun ω : Transcript s T d =>
      if π.date j ω ≤ i.val then π.head j ω else 0) :=
    fun j => (hπ.2.2.2 j i.val).mono (info_le i.val) le_rfl
  have key : ∀ (l : List (Fin B)) (w0 : Transcript s T d → Vector d), Measurable w0 →
      Measurable fun ω => l.foldl (fun w j => if π.date j ω ≤ i.val then π.head j ω else w) (w0 ω) := by
    intro l
    induction l with
    | nil => intro w0 hw0; simpa using hw0
    | cons j l ih =>
      intro w0 hw0
      simp only [List.foldl_cons]
      apply ih
      have : Measurable fun ω : Transcript s T d =>
          if π.date j ω ≤ i.val then (if π.date j ω ≤ i.val then π.head j ω else 0) else w0 ω :=
        Measurable.ite (hdate j) (hhead j) hw0
      convert this using 2 with ω
      by_cases h : π.date j ω ≤ i.val <;> simp [h]
  unfold deployed
  exact key _ (fun _ => θ₀) measurable_const

lemma measurable_date {s : RandomSeed} {T d B : ℕ} (π : ReleasePolicy s T d B) (hπ : IsCausal π)
    (j : Fin B) : Measurable (fun ω : Transcript s T d => π.date j ω) := by
  have hle : ∀ n, MeasurableSet {ω : Transcript s T d | π.date j ω ≤ n} :=
    fun n => info_le n _ (hπ.2.2.1 j n)
  refine measurable_to_countable' fun n => ?_
  cases n with
  | zero => simpa [Set.preimage, Nat.le_zero] using hle 0
  | succ n =>
    have : (fun ω : Transcript s T d => π.date j ω) ⁻¹' {n + 1} =
        {ω | π.date j ω ≤ n + 1} \ {ω | π.date j ω ≤ n} := by
      ext ω; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_diff, Set.mem_setOf_eq]
      omega
    rw [this]
    exact (hle _).diff (hle _)

lemma measurable_head {s : RandomSeed} {T d B : ℕ} (π : ReleasePolicy s T d B) (hπ : IsCausal π)
    (j : Fin B) : Measurable (fun ω : Transcript s T d => π.head j ω) := by
  have := (hπ.2.2.2 j T).mono (info_le T) le_rfl
  have h2 : (fun ω : Transcript s T d => π.head j ω) =
      fun ω => if π.date j ω ≤ T then π.head j ω else 0 := by
    funext ω
    rw [if_pos (hπ.1 j ω)]
  rw [h2]
  exact this

/-- block start row -/
def aRow (N h : ℕ) (p j : ℕ) : ℕ := 1 + (p * N + j) * h

/-- pre-block coverage event -/
def Epre {s : RandomSeed} {T d B K M : ℕ} (π : ReleasePolicy s T d B) (δ : ℝ)
    (u : Fin M → Vector d) (N h : ℕ) (p : Fin K) (j : Fin N) (v : Fin M) :
    Set (Transcript s T d) :=
  {ω | ∃ i : Fin T, i.val = aRow N h p.val j.val ∧ ‖deployed 0 π ω i - u v‖ < δ / 4}

/-- in-block release event for slot `b` -/
def Fset {s : RandomSeed} {T d B K M : ℕ} (π : ReleasePolicy s T d B) (δ : ℝ)
    (u : Fin M → Vector d) (N h : ℕ) (b : Fin B) (p : Fin K) (j : Fin N) (v : Fin M) :
    Set (Transcript s T d) :=
  {ω | aRow N h p.val j.val < π.date b ω ∧ π.date b ω < aRow N h p.val j.val + h ∧
    ‖π.head b ω - u v‖ < δ / 4}

def Ein {s : RandomSeed} {T d B K M : ℕ} (π : ReleasePolicy s T d B) (δ : ℝ)
    (u : Fin M → Vector d) (N h : ℕ) (p : Fin K) (j : Fin N) (v : Fin M) :
    Set (Transcript s T d) :=
  ⋃ b : Fin B, Fset π δ u N h b p j v

/-- phase window event for slot `b` -/
def Gset {s : RandomSeed} {T d B K : ℕ} (π : ReleasePolicy s T d B) (N h : ℕ) (b : Fin B)
    (p : Fin K) : Set (Transcript s T d) :=
  {ω | 1 + p.val * N * h < π.date b ω ∧ π.date b ω < 1 + (p.val + 1) * N * h}

lemma measurableSet_Epre {s : RandomSeed} {T d B K M : ℕ} (π : ReleasePolicy s T d B)
    (hπ : IsCausal π) (δ : ℝ) (u : Fin M → Vector d) (N h : ℕ) (p : Fin K) (j : Fin N)
    (v : Fin M) : MeasurableSet (Epre π δ u N h p j v) := by
  unfold Epre
  rw [Set.setOf_exists]
  refine MeasurableSet.iUnion fun i => ?_
  rw [Set.setOf_and]
  exact (MeasurableSet.const _).inter (measurableSet_lt
    (((measurable_deployed 0 π hπ i).sub_const _).norm) measurable_const)

lemma measurableSet_Fset {s : RandomSeed} {T d B K M : ℕ} (π : ReleasePolicy s T d B)
    (hπ : IsCausal π) (δ : ℝ) (u : Fin M → Vector d) (N h : ℕ) (b : Fin B) (p : Fin K)
    (j : Fin N) (v : Fin M) : MeasurableSet (Fset π δ u N h b p j v) := by
  unfold Fset
  rw [Set.setOf_and, Set.setOf_and]
  refine (measurableSet_lt measurable_const (measurable_date π hπ b)).inter
    ((measurableSet_lt (measurable_date π hπ b) measurable_const).inter
      (measurableSet_lt (((measurable_head π hπ b).sub_const _).norm) measurable_const))

lemma measurableSet_Ein {s : RandomSeed} {T d B K M : ℕ} (π : ReleasePolicy s T d B)
    (hπ : IsCausal π) (δ : ℝ) (u : Fin M → Vector d) (N h : ℕ) (p : Fin K) (j : Fin N)
    (v : Fin M) : MeasurableSet (Ein π δ u N h p j v) :=
  MeasurableSet.iUnion fun b => measurableSet_Fset π hπ δ u N h b p j v

lemma measurableSet_Gset {s : RandomSeed} {T d B K : ℕ} (π : ReleasePolicy s T d B)
    (hπ : IsCausal π) (N h : ℕ) (b : Fin B) (p : Fin K) :
    MeasurableSet (Gset π N h b p) := by
  unfold Gset
  rw [Set.setOf_and]
  exact (measurableSet_lt measurable_const (measurable_date π hπ b)).inter
    (measurableSet_lt (measurable_date π hπ b) measurable_const)

/-! ### disjointness -/

lemma near_unique {d M : ℕ} (u : Fin M → Vector d) (δ : ℝ)
    (hsep : ∀ v v', v ≠ v' → δ / 2 < ‖u v - u v'‖) (x : Vector d) (v v' : Fin M)
    (h1 : ‖x - u v‖ < δ / 4) (h2 : ‖x - u v'‖ < δ / 4) : v = v' := by
  by_contra hne
  have := hsep v v' hne
  have h3 : ‖u v - u v'‖ ≤ ‖x - u v‖ + ‖x - u v'‖ := by
    calc ‖u v - u v'‖ = ‖(x - u v') - (x - u v)‖ := by congr 1; abel
      _ ≤ ‖x - u v'‖ + ‖x - u v‖ := norm_sub_le _ _
      _ = _ := add_comm _ _
  linarith

lemma Epre_disjoint {s : RandomSeed} {T d B K M : ℕ} (π : ReleasePolicy s T d B) (δ : ℝ)
    (u : Fin M → Vector d) (hsep : ∀ v v', v ≠ v' → δ / 2 < ‖u v - u v'‖) (N h : ℕ)
    (p : Fin K) (j : Fin N) :
    Set.PairwiseDisjoint (Set.univ : Set (Fin M)) (Epre π δ u N h p j) := by
  intro v _ v' _ hne
  rw [Function.onFun, Set.disjoint_left]
  rintro ω ⟨i, hi, h1⟩ ⟨i', hi', h2⟩
  have : i = i' := Fin.ext (by omega)
  subst this
  exact hne (near_unique u δ hsep _ v v' h1 h2)

lemma Fset_disjoint {s : RandomSeed} {T d B K M : ℕ} (π : ReleasePolicy s T d B) (δ : ℝ)
    (u : Fin M → Vector d) (hsep : ∀ v v', v ≠ v' → δ / 2 < ‖u v - u v'‖) (N h : ℕ)
    (hh : 1 ≤ h) (b : Fin B) (p : Fin K) :
    Set.PairwiseDisjoint (Set.univ : Set (Fin N × Fin M))
      (fun x : Fin N × Fin M => Fset π δ u N h b p x.1 x.2) := by
  intro x _ y _ hne
  rw [Function.onFun, Set.disjoint_left]
  rintro ω ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩
  have hj : x.1 = y.1 := by
    by_contra hjne
    have hlt : x.1.val < y.1.val ∨ y.1.val < x.1.val := by
      rcases Nat.lt_or_ge x.1.val y.1.val with h' | h'
      · exact Or.inl h'
      · exact Or.inr (lt_of_le_of_ne h' (fun e => hjne (Fin.ext e.symm)))
    unfold aRow at a1 a2 b1 b2
    rcases hlt with h' | h'
    · have : (p.val * N + x.1.val + 1) * h ≤ (p.val * N + y.1.val) * h :=
        Nat.mul_le_mul_right _ (by omega)
      nlinarith
    · have : (p.val * N + y.1.val + 1) * h ≤ (p.val * N + x.1.val) * h :=
        Nat.mul_le_mul_right _ (by omega)
      nlinarith
  have hv : x.2 = y.2 := near_unique u δ hsep _ _ _ a3 b3
  exact hne (Prod.ext hj hv)

lemma Gset_disjoint {s : RandomSeed} {T d B K : ℕ} (π : ReleasePolicy s T d B) (N h : ℕ)
    (b : Fin B) :
    Set.PairwiseDisjoint (Set.univ : Set (Fin K)) (fun p : Fin K => Gset π N h b p) := by
  have key : ∀ p q : Fin K, p.val < q.val → Disjoint (Gset π N h b p) (Gset π N h b q) := by
    intro p q hpq
    rw [Set.disjoint_left]
    rintro ω ⟨a1, a2⟩ ⟨b1, b2⟩
    have : (p.val + 1) * N * h ≤ q.val * N * h :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hpq)
    omega
  intro p _ q _ hne
  rw [Function.onFun]
  rcases lt_trichotomy p.val q.val with h' | h' | h'
  · exact key p q h'
  · exact (hne (Fin.ext h')).elim
  · exact (key q p h').symm

lemma Fset_subset_Gset {s : RandomSeed} {T d B K M : ℕ} (π : ReleasePolicy s T d B) (δ : ℝ)
    (u : Fin M → Vector d) (N h : ℕ) (b : Fin B) (p : Fin K) (j : Fin N) (v : Fin M) :
    Fset π δ u N h b p j v ⊆ Gset π N h b p := by
  rintro ω ⟨a1, a2, _⟩
  unfold aRow at a1 a2
  have hj := j.2
  have h1 : p.val * N * h ≤ (p.val * N + j.val) * h := Nat.mul_le_mul_right _ (by omega)
  have h2 : (p.val * N + j.val + 1) * h ≤ (p.val + 1) * N * h :=
    Nat.mul_le_mul_right _ (by nlinarith)
  have h3 : (p.val * N + j.val + 1) * h = (p.val * N + j.val) * h + h := by ring
  refine ⟨by omega, by omega⟩

/-! ### cover: on the complement, the deployed value is far from `u v` on the block -/

lemma far_on_block {s : RandomSeed} {T d B K M : ℕ} (π : ReleasePolicy s T d B) (δ : ℝ)
    (u : Fin M → Vector d) (N h : ℕ) (p : Fin K) (j : Fin N) (v : Fin M)
    (ω : Transcript s T d) (hω : ω ∉ Epre π δ u N h p j v ∪ Ein π δ u N h p j v)
    (ia i : Fin T) (hia : ia.val = aRow N h p.val j.val) (hi : aRow N h p.val j.val ≤ i.val)
    (hih : i.val < aRow N h p.val j.val + h) : δ / 4 ≤ ‖deployed 0 π ω i - u v‖ := by
  by_contra hcon
  push Not at hcon
  have hpre : ¬ ‖deployed 0 π ω ia - u v‖ < δ / 4 := fun hh => hω (Or.inl ⟨ia, hia, hh⟩)
  have hin : ∀ b : Fin B, aRow N h p.val j.val < π.date b ω →
      π.date b ω < aRow N h p.val j.val + h → ¬ ‖π.head b ω - u v‖ < δ / 4 :=
    fun b h1 h2 hh => hω (Or.inr (Set.mem_iUnion.2 ⟨b, h1, h2, hh⟩))
  exact cover 0 π (fun x => ‖x - u v‖ < δ / 4) ω _ h ia i hia hi hih hpre hin hcon

end TRS.Dev.CodebookEvents

end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary TightReleaseSchedules.Stationary.Supplement

noncomputable section

namespace TRS.Dev.CodebookFam
open TRS.Dev.CodebookDep TRS.Dev.CodebookShear TRS.Dev.CodebookPath TRS.Dev.CodebookEvents

abbrev Cfg (K N M : ℕ) := Fin K → Bool × Fin N × Fin M

/-- the path of a configuration -/
def path {T d K N M : ℕ} (h : ℕ) (u : Fin M → Vector d) (θ : Cfg K N M) : Fin T → Vector d :=
  pulsePath h u (fun p => (θ p).1) (fun p => (θ p).2.1) (fun p => (θ p).2.2)

/-- term of phase `q` -/
def tm {d N M : ℕ} (h : ℕ) (u : Fin M → Vector d) (q : ℕ) (c : Bool × Fin N × Fin M) (i : ℕ) :
    Vector d :=
  if c.1 = true ∧ 1 + (q * N + c.2.1.val) * h ≤ i ∧ i < 1 + (q * N + c.2.1.val + 1) * h
  then u c.2.2 else 0

lemma path_apply {T d K N M : ℕ} (h : ℕ) (u : Fin M → Vector d) (θ : Cfg K N M) (i : Fin T) :
    path h u θ i = ∑ q : Fin K, tm h u q.val (θ q) i.val := rfl

lemma path_update {T d K N M : ℕ} (h : ℕ) (u : Fin M → Vector d) (θ : Cfg K N M) (p : Fin K)
    (c : Bool × Fin N × Fin M) (i : Fin T) :
    path h u (Function.update θ p c) i =
      tm h u p.val c i.val + ∑ q ∈ Finset.univ.erase p, tm h u q.val (θ q) i.val := by
  rw [path_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ p)]
  rw [Function.update_self]
  congr 1
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hq)]

lemma tm_false {d N M : ℕ} (h : ℕ) (u : Fin M → Vector d) (q : ℕ) (c : Fin N × Fin M) (i : ℕ) :
    tm h u q (false, c) i = 0 := by
  unfold tm; simp

/-- the block shift -/
def bs {T d : ℕ} (N h : ℕ) (p j : ℕ) (c : Vector d) (i : Fin T) : Vector d :=
  if aRow N h p j ≤ i.val ∧ i.val < aRow N h p j + h then c else 0

lemma tm_true {d N M : ℕ} (h : ℕ) (u : Fin M → Vector d) (q : ℕ) (j : Fin N) (v : Fin M)
    (i : ℕ) : tm h u q (true, j, v) i =
      if aRow N h q j.val ≤ i ∧ i < aRow N h q j.val + h then u v else 0 := by
  unfold tm aRow
  have : 1 + (q * N + j.val + 1) * h = 1 + (q * N + j.val) * h + h := by ring
  simp only [true_and, this]

lemma path_update_true {T d K N M : ℕ} (h : ℕ) (u : Fin M → Vector d) (θ : Cfg K N M)
    (p : Fin K) (j : Fin N) (v : Fin M) (c : Fin N × Fin M) :
    path (T := T) h u (Function.update θ p (true, j, v)) = fun i =>
      path (T := T) h u (Function.update θ p (false, c)) i + bs N h p.val j.val (u v) i := by
  funext i
  rw [path_update, path_update, tm_false, tm_true]
  unfold bs
  simp [add_comm]

/-- zeroing the phase `p` of a configuration -/
def iota {K N M : ℕ} (θ : Cfg K N M) (p : Fin K) : Cfg K N M :=
  Function.update θ p (false, (θ p).2)

/-- null path -/
def th0 {T d K N M : ℕ} (h : ℕ) (u : Fin M → Vector d) (θ : Cfg K N M) (p : Fin K) :
    Fin T → Vector d := path h u (iota θ p)

/-- full path -/
def thFull {T d K N M : ℕ} (h : ℕ) (u : Fin M → Vector d) (θ : Cfg K N M) (p : Fin K)
    (j : Fin N) (v : Fin M) : Fin T → Vector d :=
  path h u (Function.update θ p (true, j, v))

/-- half-amplitude path -/
def thMid {T d K N M : ℕ} (h : ℕ) (u : Fin M → Vector d) (θ : Cfg K N M) (p : Fin K)
    (j : Fin N) (v : Fin M) : Fin T → Vector d :=
  fun i => th0 h u θ p i + bs N h p.val j.val ((1 / 2 : ℝ) • u v) i

lemma thFull_eq {T d K N M : ℕ} (h : ℕ) (u : Fin M → Vector d) (θ : Cfg K N M) (p : Fin K)
    (j : Fin N) (v : Fin M) :
    thFull (T := T) h u θ p j v = fun i => th0 h u θ p i + bs N h p.val j.val (u v) i := by
  unfold thFull th0 iota
  exact path_update_true h u θ p j v (θ p).2

lemma bs_apply {T d : ℕ} (N h : ℕ) (p j : ℕ) (c : Vector d) (i : Fin T) :
    bs N h p j c i = if aRow N h p j ≤ i.val ∧ i.val < aRow N h p j + h then c else 0 := rfl

lemma norm_bs_le {T d : ℕ} (N h p j : ℕ) (c : Vector d) (r : ℝ) (hr : 0 ≤ r) (hc : ‖c‖ ≤ r)
    (i : Fin T) : ‖bs N h p j c i‖ ≤ r := by
  unfold bs; split_ifs
  · exact hc
  · simpa using hr

lemma card_block {T : ℕ} (N h p j : ℕ) (hT : aRow N h p j + h ≤ T) :
    (Finset.univ.filter (fun i : Fin T => aRow N h p j ≤ i.val ∧ i.val < aRow N h p j + h)).card
      = h := by
  have : (Finset.univ.filter (fun i : Fin T => aRow N h p j ≤ i.val ∧ i.val < aRow N h p j + h)).map
      Fin.valEmbedding = Finset.Ico (aRow N h p j) (aRow N h p j + h) := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_Ico]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact hi
    · intro hx; exact ⟨⟨x, by omega⟩, hx, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, this]
  simp

lemma sum_bs_sq {T d : ℕ} (N h p j : ℕ) (hT : aRow N h p j + h ≤ T) (c : Vector d) :
    ∑ i : Fin T, ‖bs N h p j c i‖ ^ 2 = h * ‖c‖ ^ 2 := by
  have : ∀ i : Fin T, ‖bs N h p j c i‖ ^ 2 =
      if aRow N h p j ≤ i.val ∧ i.val < aRow N h p j + h then ‖c‖ ^ 2 else 0 := by
    intro i; unfold bs; split_ifs <;> simp
  simp_rw [this]
  rw [← Finset.sum_filter, Finset.sum_const, card_block N h p j hT]
  simp

lemma aRow_add_le {K N : ℕ} (h T : ℕ) (hT : 1 + K * N * h ≤ T) (p : Fin K) (j : Fin N) :
    aRow N h p.val j.val + h ≤ T := by
  unfold aRow
  have h1 : p.val * N + j.val + 1 ≤ K * N := by
    have := j.2
    have h2 : (p.val + 1) * N ≤ K * N := Nat.mul_le_mul_right _ p.2
    nlinarith
  have : (p.val * N + j.val + 1) * h ≤ K * N * h := Nat.mul_le_mul_right _ h1
  have h3 : (p.val * N + j.val + 1) * h = (p.val * N + j.val) * h + h := by ring
  omega

end TRS.Dev.CodebookFam

end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary TightReleaseSchedules.Stationary.Supplement

noncomputable section

namespace TRS.Dev.CodebookRisk
open TRS.Dev.CodebookDep TRS.Dev.CodebookShear TRS.Dev.CodebookPath TRS.Dev.CodebookEvents
  TRS.Dev.CodebookFam

section probs
variable {s : RandomSeed} {T d : ℕ}

lemma prob_def (S : Set (Transcript s T d)) (θ : Fin T → Vector d) :
    prob S θ = (s.law.prod (gaussianRows T d)).real (EvS S θ) := rfl

lemma EvS_iUnion {ι : Type} (S : ι → Set (Transcript s T d)) (θ : Fin T → Vector d) :
    EvS (⋃ i, S i) θ = ⋃ i, EvS (S i) θ := by
  ext ω; simp [EvS]

lemma EvS_compl (S : Set (Transcript s T d)) (θ : Fin T → Vector d) :
    EvS Sᶜ θ = (EvS S θ)ᶜ := by
  ext ω; simp [EvS]

lemma EvS_union (S S' : Set (Transcript s T d)) (θ : Fin T → Vector d) :
    EvS (S ∪ S') θ = EvS S θ ∪ EvS S' θ := by
  ext ω; simp [EvS]

lemma prob_iUnion_le {ι : Type} [Fintype ι] (S : ι → Set (Transcript s T d))
    (θ : Fin T → Vector d) : prob (⋃ i, S i) θ ≤ ∑ i, prob (S i) θ := by
  rw [prob_def, EvS_iUnion]
  exact measureReal_iUnion_fintype_le _

lemma prob_iUnion_eq {ι : Type} [Fintype ι] (S : ι → Set (Transcript s T d))
    (hm : ∀ i, MeasurableSet (S i)) (hd : Pairwise (Function.onFun Disjoint S))
    (θ : Fin T → Vector d) : prob (⋃ i, S i) θ = ∑ i, prob (S i) θ := by
  rw [prob_def, EvS_iUnion]
  refine measureReal_iUnion_fintype (fun i j hij => ?_) (fun i => measurableSet_EvS _ (hm i) θ)
  exact (hd hij).preimage _

lemma prob_mono (S S' : Set (Transcript s T d)) (h : S ⊆ S') (θ : Fin T → Vector d) :
    prob S θ ≤ prob S' θ := by
  rw [prob_def, prob_def]
  exact measureReal_mono (fun ω hω => h hω)

lemma prob_union_le (S S' : Set (Transcript s T d)) (θ : Fin T → Vector d) :
    prob (S ∪ S') θ ≤ prob S θ + prob S' θ := by
  rw [prob_def, prob_def, prob_def, EvS_union]
  exact measureReal_union_le _ _

lemma prob_compl (S : Set (Transcript s T d)) (hS : MeasurableSet S) (θ : Fin T → Vector d) :
    prob Sᶜ θ = 1 - prob S θ := by
  rw [prob_def, prob_def, EvS_compl]
  have := measureReal_add_measureReal_compl (μ := s.law.prod (gaussianRows T d))
    (measurableSet_EvS S hS θ)
  have h1 : (s.law.prod (gaussianRows T d)).real Set.univ = 1 := by simp
  linarith

end probs

/-! ### pointwise cost bound -/

open scoped Classical in
lemma cost_ge {s : RandomSeed} {T d B K N M : ℕ} (π : ReleasePolicy s T d B) (δ : ℝ) (hδ : 0 ≤ δ)
    (u : Fin M → Vector d) (h : ℕ) (hh : 1 ≤ h) (hT : 1 + K * N * h ≤ T)
    (Z : Fin K → Bool) (J : Fin K → Fin N) (V : Fin K → Fin M) (ω : Transcript s T d) :
    ∑ p : Fin K, (if Z p = true ∧ ω ∈ (Epre π δ u N h p (J p) (V p) ∪ Ein π δ u N h p (J p) (V p))ᶜ
        then (h : ℝ) * δ ^ 2 / 32 else 0) ≤
      (1 / 2 : ℝ) * ∑ i : Fin T, ‖deployed 0 π ω i - pulsePath h u Z J V i‖ ^ 2 := by
  classical
  set D : Fin T → ℝ := fun i => ‖deployed 0 π ω i - pulsePath h u Z J V i‖ ^ 2 with hD
  have hD0 : ∀ i, 0 ≤ D i := fun i => by positivity
  set blk : Fin K → Finset (Fin T) := fun p =>
    Finset.univ.filter (fun i : Fin T => aRow N h p.val (J p).val ≤ i.val ∧
      i.val < aRow N h p.val (J p).val + h) with hblk
  have claim1 : ∀ p : Fin K, Z p = true →
      ω ∈ (Epre π δ u N h p (J p) (V p) ∪ Ein π δ u N h p (J p) (V p))ᶜ →
      (h : ℝ) * (δ / 4) ^ 2 ≤ ∑ i ∈ blk p, D i := by
    intro p hZ hU
    have hlt := aRow_add_le h T hT p (J p)
    have hia : (⟨aRow N h p.val (J p).val, by omega⟩ : Fin T).val = aRow N h p.val (J p).val := rfl
    calc (h : ℝ) * (δ / 4) ^ 2 = ∑ i ∈ blk p, (δ / 4) ^ 2 := by
          rw [Finset.sum_const, hblk, card_block N h p.val (J p).val hlt]
          simp
      _ ≤ ∑ i ∈ blk p, D i := by
          refine Finset.sum_le_sum fun i hi => ?_
          simp only [hblk, Finset.mem_filter, Finset.mem_univ, true_and] at hi
          have hact : Act N h Z J p i.val := ⟨hZ, by unfold aRow at hi; exact hi.1, by
            have := hi.2; unfold aRow at this
            have e : 1 + (p.val * N + (J p).val + 1) * h = 1 + (p.val * N + (J p).val) * h + h := by
              ring
            omega⟩
          have hθ := pulsePath_of_act h u Z J V i p hact
          have hfar := far_on_block π δ u N h p (J p) (V p) ω hU ⟨_, by omega⟩ i hia hi.1 hi.2
          have h0 : 0 ≤ δ / 4 := by linarith
          simp only [hD, hθ]
          exact pow_le_pow_left₀ h0 hfar 2
  have claim2 : ∑ p : Fin K, (if Z p = true then ∑ i ∈ blk p, D i else 0) ≤ ∑ i, D i := by
    have e1 : ∀ p : Fin K, (if Z p = true then ∑ i ∈ blk p, D i else 0) =
        ∑ i : Fin T, (if Z p = true ∧ i ∈ blk p then D i else 0) := by
      intro p
      by_cases hZ : Z p = true
      · simp only [hZ, true_and, if_true]
        rw [← Finset.sum_filter]
        congr 1
        ext i; simp [hblk]
      · simp [hZ]
    simp_rw [e1]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun i _ => ?_
    have hcount : ∑ p : Fin K, (if Z p = true ∧ i ∈ blk p then D i else 0) ≤ D i := by
      by_cases hex : ∃ p, Z p = true ∧ i ∈ blk p
      · obtain ⟨p, hp⟩ := hex
        rw [Finset.sum_eq_single p]
        · rw [if_pos hp]
        · intro q _ hqp
          rw [if_neg]
          rintro ⟨hZq, hq⟩
          simp only [hblk, Finset.mem_filter, Finset.mem_univ, true_and] at hq hp
          have act : ∀ r : Fin K, Z r = true → aRow N h r.val (J r).val ≤ i.val →
              i.val < aRow N h r.val (J r).val + h → Act N h Z J r i.val := by
            intro r hZr a1 a2
            refine ⟨hZr, by unfold aRow at a1; exact a1, ?_⟩
            unfold aRow at a2
            have e : 1 + (r.val * N + (J r).val + 1) * h = 1 + (r.val * N + (J r).val) * h + h := by
              ring
            omega
          exact hqp (act_unique N h Z J q p i.val (act q hZq hq.1 hq.2)
            (act p hp.1 hp.2.1 hp.2.2))
        · intro h'; exact absurd (Finset.mem_univ p) h'
      · push Not at hex
        rw [Finset.sum_eq_zero fun p _ => if_neg (fun hp => (hex p hp.1) hp.2)]
        exact hD0 i
    exact hcount
  calc _ ≤ ∑ p : Fin K, (1 / 2 : ℝ) * (if Z p = true then ∑ i ∈ blk p, D i else 0) := by
        refine Finset.sum_le_sum fun p _ => ?_
        by_cases hc : Z p = true ∧ ω ∈ (Epre π δ u N h p (J p) (V p) ∪
            Ein π δ u N h p (J p) (V p))ᶜ
        · rw [if_pos hc, if_pos hc.1]
          have := claim1 p hc.1 hc.2
          nlinarith
        · rw [if_neg hc]
          split_ifs
          · exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => hD0 i)
          · simp
    _ = (1 / 2 : ℝ) * ∑ p : Fin K, (if Z p = true then ∑ i ∈ blk p, D i else 0) := by
        rw [Finset.mul_sum]
    _ ≤ _ := by gcongr


open scoped Classical in
lemma risk_ge {s : RandomSeed} {T d B K N M : ℕ} (π : ReleasePolicy s T d B) (hπ : IsCausal π)
    (δ : ℝ) (hδ : 0 ≤ δ) (u : Fin M → Vector d) (h : ℕ) (hh : 1 ≤ h) (hT : 1 + K * N * h ≤ T)
    (Z : Fin K → Bool) (J : Fin K → Fin N) (V : Fin K → Fin M) :
    ENNReal.ofReal (∑ p : Fin K, if Z p = true then ((h : ℝ) * δ ^ 2 / 32) *
        prob (Epre π δ u N h p (J p) (V p) ∪ Ein π δ u N h p (J p) (V p))ᶜ
          (pulsePath h u Z J V) else 0) ≤
      policyRisk 0 π (pulsePath h u Z J V) := by
  set c : ℝ := (h : ℝ) * δ ^ 2 / 32 with hcdef
  set μ := s.law.prod (gaussianRows T d) with hμ
  set θ := pulsePath (T := T) h u Z J V with hθ
  set U : Fin K → Set (Transcript s T d) := fun p =>
    (Epre π δ u N h p (J p) (V p) ∪ Ein π δ u N h p (J p) (V p))ᶜ with hU
  have hUm : ∀ p, MeasurableSet (U p) := fun p =>
    ((measurableSet_Epre π hπ δ u N h p (J p) (V p)).union
      (measurableSet_Ein π hπ δ u N h p (J p) (V p))).compl
  have hc : 0 ≤ c := by positivity
  have step1 : ENNReal.ofReal (∑ p : Fin K, if Z p = true then c * prob (U p) θ else 0) =
      ∑ p : Fin K, (if Z p = true then ENNReal.ofReal c * μ (EvS (U p) θ) else 0) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun p _ => by
      split_ifs
      · exact mul_nonneg hc (prob_nonneg _ _)
      · exact le_rfl)]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hZ : Z p = true
    · simp only [hZ, if_true]
      rw [ENNReal.ofReal_mul hc]
      congr 1
      exact ENNReal.ofReal_toReal (measure_ne_top _ _)
    · simp [hZ]
  rw [show (∑ p : Fin K, if Z p = true then ((h : ℝ) * δ ^ 2 / 32) *
        prob (Epre π δ u N h p (J p) (V p) ∪ Ein π δ u N h p (J p) (V p))ᶜ
          (pulsePath h u Z J V) else 0) =
      ∑ p : Fin K, if Z p = true then c * prob (U p) θ else 0 from rfl, step1]
  have hmeas : ∀ p : Fin K, Measurable (fun ω : s.space × GaussianRows T d =>
      if Z p = true then (EvS (U p) θ).indicator (fun _ => ENNReal.ofReal c) ω else 0) := by
    intro p
    by_cases hZ : Z p = true
    · simp only [hZ, if_true]
      exact measurable_const.indicator (measurableSet_EvS _ (hUm p) θ)
    · simp [hZ]
  have step2 : (∑ p : Fin K, (if Z p = true then ENNReal.ofReal c * μ (EvS (U p) θ) else 0)) =
      ∫⁻ ω, ∑ p : Fin K, (if Z p = true then
        (EvS (U p) θ).indicator (fun _ => ENNReal.ofReal c) ω else 0) ∂μ := by
    rw [lintegral_finset_sum _ (fun p _ => hmeas p)]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hZ : Z p = true
    · simp only [hZ, if_true]
      rw [lintegral_indicator_const (measurableSet_EvS _ (hUm p) θ)]
    · simp [hZ]
  rw [step2]
  unfold policyRisk
  refine lintegral_mono fun ω => ?_
  have hp : ∀ p : Fin K, (if Z p = true then
        (EvS (U p) θ).indicator (fun _ => ENNReal.ofReal c) ω else 0) =
      ENNReal.ofReal (if Z p = true ∧ (ω.1, observations θ ω.2) ∈ U p then c else 0) := by
    intro p
    by_cases hZ : Z p = true
    · by_cases hm : ω ∈ EvS (U p) θ
      · have hm' : (ω.1, observations θ ω.2) ∈ U p := hm
        simp [hZ, hm, hm']
      · have hm' : ¬ (ω.1, observations θ ω.2) ∈ U p := hm
        simp [hZ, hm, hm']
    · simp [hZ]
  simp_rw [hp]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun p _ => by split_ifs <;> positivity)]
  apply ENNReal.ofReal_le_ofReal
  exact cost_ge π δ hδ u h hh hT Z J V (ω.1, observations θ ω.2)

end TRS.Dev.CodebookRisk

end
end

section
set_option autoImplicit false
open scoped BigOperators

noncomputable section

namespace TRS.Dev.CodebookSum

lemma resample {K : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (p : Fin K) (y : Y)
    (f : (Fin K → Y) → ℝ) :
    ∑ θ : Fin K → Y, f (Function.update θ p y) =
      Fintype.card Y * ∑ θ : Fin K → Y, (if θ p = y then f θ else 0) := by
  have key : ∀ y' : Y, ∑ θ : Fin K → Y, (if θ p = y' then f (Function.update θ p y) else 0) =
      ∑ θ : Fin K → Y, (if θ p = y then f θ else 0) := by
    intro y'
    let e : (Fin K → Y) ≃ (Fin K → Y) :=
      { toFun := fun θ => Function.update θ p (Equiv.swap y y' (θ p))
        invFun := fun θ => Function.update θ p (Equiv.swap y y' (θ p))
        left_inv := fun θ => by
          funext q
          by_cases hq : q = p
          · subst hq; simp
          · simp [Function.update_of_ne hq]
        right_inv := fun θ => by
          funext q
          by_cases hq : q = p
          · subst hq; simp
          · simp [Function.update_of_ne hq] }
    rw [← Equiv.sum_comp e (fun θ => if θ p = y then f θ else 0)]
    refine Finset.sum_congr rfl fun θ _ => ?_
    simp only [e, Equiv.coe_fn_mk, Function.update_self]
    by_cases hθ : θ p = y'
    · simp [hθ]
    · have : Equiv.swap y y' (θ p) ≠ y := by
        intro hc
        apply hθ
        have := congrArg (Equiv.swap y y') hc
        simpa using this
      simp [hθ, this]
  calc ∑ θ : Fin K → Y, f (Function.update θ p y)
      = ∑ θ : Fin K → Y, ∑ y' : Y, (if θ p = y' then f (Function.update θ p y) else 0) := by
        refine Finset.sum_congr rfl fun θ _ => ?_
        simp
    _ = ∑ y' : Y, ∑ θ : Fin K → Y, (if θ p = y' then f (Function.update θ p y) else 0) :=
        Finset.sum_comm
    _ = ∑ y' : Y, ∑ θ : Fin K → Y, (if θ p = y then f θ else 0) :=
        Finset.sum_congr rfl fun y' _ => key y'
    _ = _ := by simp

lemma alg4 {ι : Type} (I : Finset ι) (X Y W : ι → ℝ) (F : ℝ) (hF : 0 ≤ F)
    (hY : ∀ i, 0 ≤ Y i) (hW : ∀ i, 0 ≤ W i)
    (h1 : ∀ i ∈ I, X i ^ 2 ≤ F * Y i) (h2 : ∀ i ∈ I, Y i ^ 2 ≤ F * W i) :
    (∑ i ∈ I, X i) ^ 4 ≤ F ^ 3 * (I.card : ℝ) ^ 3 * ∑ i ∈ I, W i := by
  have c := (I.card : ℝ)
  have hc0 : (0 : ℝ) ≤ I.card := Nat.cast_nonneg _
  have e1 : (∑ i ∈ I, X i) ^ 2 ≤ I.card * (F * ∑ i ∈ I, Y i) := by
    calc (∑ i ∈ I, X i) ^ 2 ≤ I.card * ∑ i ∈ I, X i ^ 2 := sq_sum_le_card_mul_sum_sq
      _ ≤ I.card * ∑ i ∈ I, F * Y i := by
          gcongr with i hi
          exact h1 i hi
      _ = _ := by rw [← Finset.mul_sum]
  have e2 : (∑ i ∈ I, Y i) ^ 2 ≤ I.card * (F * ∑ i ∈ I, W i) := by
    calc (∑ i ∈ I, Y i) ^ 2 ≤ I.card * ∑ i ∈ I, Y i ^ 2 := sq_sum_le_card_mul_sum_sq
      _ ≤ I.card * ∑ i ∈ I, F * W i := by
          gcongr with i hi
          exact h2 i hi
      _ = _ := by rw [← Finset.mul_sum]
  have hSY : 0 ≤ ∑ i ∈ I, Y i := Finset.sum_nonneg fun i _ => hY i
  have hSW : 0 ≤ ∑ i ∈ I, W i := Finset.sum_nonneg fun i _ => hW i
  calc (∑ i ∈ I, X i) ^ 4 = ((∑ i ∈ I, X i) ^ 2) ^ 2 := by ring
    _ ≤ (I.card * (F * ∑ i ∈ I, Y i)) ^ 2 := by
        gcongr
    _ = (I.card : ℝ) ^ 2 * F ^ 2 * (∑ i ∈ I, Y i) ^ 2 := by ring
    _ ≤ (I.card : ℝ) ^ 2 * F ^ 2 * (I.card * (F * ∑ i ∈ I, W i)) := by gcongr
    _ = _ := by ring

end TRS.Dev.CodebookSum

end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary TightReleaseSchedules.Stationary.Supplement

noncomputable section

namespace TRS.Dev.CodebookCount
open TRS.Dev.CodebookDep TRS.Dev.CodebookShear TRS.Dev.CodebookPath TRS.Dev.CodebookEvents
  TRS.Dev.CodebookFam TRS.Dev.CodebookRisk

variable {s : RandomSeed} {T d B K N M : ℕ}

lemma thFull_agree (h : ℕ) (u : Fin M → Vector d) (θ : Cfg K N M) (p : Fin K) (j : Fin N)
    (v : Fin M) (k : Fin T) (hk : k.val < aRow N h p.val j.val) :
    thFull h u θ p j v k = th0 h u θ p k := by
  rw [thFull_eq]
  simp only [bs_apply]
  rw [if_neg (by omega), add_zero]

lemma pre_eq (π : ReleasePolicy s T d B) (hπ : IsCausal π) (δ : ℝ) (u : Fin M → Vector d)
    (h : ℕ) (θ : Cfg K N M) (p : Fin K) (j : Fin N) (v : Fin M) :
    prob (Epre π δ u N h p j v) (thFull h u θ p j v) = prob (Epre π δ u N h p j v) (th0 h u θ p) := by
  unfold prob
  congr 2
  ext ω
  simp only [EvS, Epre, Set.mem_setOf_eq]
  have hdep : ∀ i : Fin T, i.val = aRow N h p.val j.val →
      deployed 0 π (ω.1, observations (thFull h u θ p j v) ω.2) i =
        deployed 0 π (ω.1, observations (th0 h u θ p) ω.2) i := by
    intro i hi
    refine deployed_congr 0 π hπ i _ _ ?_
    unfold trunc
    refine Prod.ext rfl ?_
    funext k
    simp only
    by_cases hk : k.val < i.val
    · rw [if_pos hk, if_pos hk]
      unfold observations
      rw [thFull_agree h u θ p j v k (by omega)]
    · rw [if_neg hk, if_neg hk]
  constructor
  · rintro ⟨i, hi, hn⟩
    exact ⟨i, hi, by rw [← hdep i hi]; exact hn⟩
  · rintro ⟨i, hi, hn⟩
    exact ⟨i, hi, by rw [hdep i hi]; exact hn⟩

lemma sum_pre_le (π : ReleasePolicy s T d B) (hπ : IsCausal π) (δ : ℝ) (u : Fin M → Vector d)
    (hsep : ∀ v v', v ≠ v' → δ / 2 < ‖u v - u v'‖) (h : ℕ) (p : Fin K) (j : Fin N)
    (ϑ : Fin T → Vector d) :
    ∑ v : Fin M, prob (Epre π δ u N h p j v) ϑ ≤ 1 := by
  rw [← prob_iUnion_eq _ (fun v => measurableSet_Epre π hπ δ u N h p j v)
    (Set.pairwise_univ.1 (Epre_disjoint π δ u hsep N h p j))]
  exact prob_le_one' _ _

lemma cnt_le (π : ReleasePolicy s T d B) (hπ : IsCausal π) (δ : ℝ) (u : Fin M → Vector d)
    (hsep : ∀ v v', v ≠ v' → δ / 2 < ‖u v - u v'‖) (h : ℕ) (hh : 1 ≤ h) (p : Fin K)
    (ϑ : Fin T → Vector d) :
    ∑ x : Fin N × Fin M, prob (Ein π δ u N h p x.1 x.2) ϑ ≤
      ∑ b : Fin B, prob (Gset π N h b p) ϑ := by
  calc ∑ x : Fin N × Fin M, prob (Ein π δ u N h p x.1 x.2) ϑ
      ≤ ∑ x : Fin N × Fin M, ∑ b : Fin B, prob (Fset π δ u N h b p x.1 x.2) ϑ :=
        Finset.sum_le_sum fun x _ => prob_iUnion_le _ _
    _ = ∑ b : Fin B, ∑ x : Fin N × Fin M, prob (Fset π δ u N h b p x.1 x.2) ϑ :=
        Finset.sum_comm
    _ ≤ ∑ b : Fin B, prob (Gset π N h b p) ϑ := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [← prob_iUnion_eq (fun x : Fin N × Fin M => Fset π δ u N h b p x.1 x.2)
          (fun x => measurableSet_Fset π hπ δ u N h b p x.1 x.2)
          (Set.pairwise_univ.1 (Fset_disjoint π δ u hsep N h hh b p))]
        refine prob_mono _ _ ?_ _
        exact Set.iUnion_subset fun x => Fset_subset_Gset π δ u N h b p x.1 x.2

lemma Gsum_le (π : ReleasePolicy s T d B) (hπ : IsCausal π) (h : ℕ) (ϑ : Fin T → Vector d) :
    ∑ p : Fin K, ∑ b : Fin B, prob (Gset π N h b p) ϑ ≤ B := by
  rw [Finset.sum_comm]
  calc ∑ b : Fin B, ∑ p : Fin K, prob (Gset π N h b p) ϑ ≤ ∑ b : Fin B, (1 : ℝ) := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [← prob_iUnion_eq (fun p : Fin K => Gset π N h b p)
          (fun p => measurableSet_Gset π hπ N h b p)
          (Set.pairwise_univ.1 (Gset_disjoint π N h b))]
        exact prob_le_one' _ _
    _ = B := by simp

/-- the change of measure along one block -/
lemma cs_block (S : Set (Transcript s T d)) (hS : MeasurableSet S) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) (h p j : ℕ) (hT : aRow N h p j + h ≤ T) (ϑ ϑ' : Fin T → Vector d)
    (c : Vector d) (hc : ‖c‖ ≤ δ / 2) (hdiff : ∀ i, ϑ' i - ϑ i = bs N h p j c i) :
    prob S ϑ' ^ 2 ≤ Real.exp ((h : ℝ) * δ ^ 2 / 2) * prob S ϑ := by
  have hc0 : 0 ≤ δ / 2 := by linarith
  have h1 : ∀ i, ‖ϑ' i - ϑ i‖ ^ 2 ≤ 1 / 4 := by
    intro i
    rw [hdiff]
    have := norm_bs_le N h p j c (δ / 2) hc0 hc i
    nlinarith [norm_nonneg (bs N h p j c i)]
  have h2 : ∑ i, ‖ϑ' i - ϑ i‖ ^ 2 ≤ (h : ℝ) * δ ^ 2 / 4 := by
    simp_rw [hdiff]
    rw [sum_bs_sq N h p j hT c]
    have : ‖c‖ ^ 2 ≤ (δ / 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hc 2
    nlinarith [Nat.cast_nonneg (α := ℝ) h]
  have := cs_exp S hS ϑ ϑ' h1 _ h2
  have e : 2 * ((h : ℝ) * δ ^ 2 / 4) = (h : ℝ) * δ ^ 2 / 2 := by ring
  rwa [e] at this

lemma diff_full_mid {T d K N M : ℕ} (h : ℕ) (u : Fin M → Vector d) (θ : Cfg K N M) (p : Fin K)
    (j : Fin N) (v : Fin M) (i : Fin T) :
    thFull h u θ p j v i - thMid h u θ p j v i = bs N h p.val j.val ((1 / 2 : ℝ) • u v) i := by
  rw [thFull_eq]
  simp only [thMid, bs_apply]
  split_ifs
  · rw [add_sub_add_left_eq_sub]
    module
  · simp

lemma diff_mid_zero {T d K N M : ℕ} (h : ℕ) (u : Fin M → Vector d) (θ : Cfg K N M) (p : Fin K)
    (j : Fin N) (v : Fin M) (i : Fin T) :
    thMid h u θ p j v i - th0 h u θ p i = bs N h p.val j.val ((1 / 2 : ℝ) • u v) i := by
  simp only [thMid]
  abel

lemma norm_half {d : ℕ} (δ : ℝ) (hδ0 : 0 ≤ δ) (c : Vector d) (hc : ‖c‖ ≤ δ) :
    ‖(1 / 2 : ℝ) • c‖ ≤ δ / 2 := by
  rw [norm_smul]
  simp only [Real.norm_eq_abs]
  rw [abs_of_pos (by norm_num)]
  linarith

end TRS.Dev.CodebookCount

end
end

section
set_option autoImplicit false
open scoped BigOperators

noncomputable section

namespace TRS.Dev.CodebookNum

lemma exp_four : (53 : ℝ) ≤ Real.exp 4 := by
  have h1 : (2.7 : ℝ) < Real.exp 1 := by
    have := Real.exp_one_gt_d9
    linarith
  have : Real.exp 4 = Real.exp 1 ^ 4 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  have : (2.7 : ℝ) ^ 4 ≤ Real.exp 1 ^ 4 := by gcongr
  norm_num at this ⊢
  linarith

lemma numeric (B K N M h : ℕ) (δ : ℝ) (hB : 1 ≤ B) (hK : 1 ≤ K) (hN : 1 ≤ N) (hM : 2 ≤ M)
    (hMKN : 1024 * B ≤ M * K * N)
    (hinfo : (h : ℝ) * δ ^ 2 ≤ (1 / 8) * Real.log ((M * K * N : ℝ) / (4 * B))) :
    Real.exp ((h : ℝ) * δ ^ 2 / 2) ^ 3 * (2 * B / (K * N * M : ℝ)) ≤ (3 / 8) ^ 4 := by
  have hB' : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hMKN' : (1024 : ℝ) * B ≤ M * K * N := by exact_mod_cast hMKN
  set q : ℝ := (M * K * N : ℝ) / (4 * B) with hq
  have hq256 : 256 ≤ q := by
    rw [hq, le_div_iff₀ (by positivity)]; linarith
  have hqpos : 0 < q := by linarith
  set L : ℝ := Real.log q with hL
  have hL5 : 5 ≤ L := by
    have h2 : Real.log 256 ≤ L := Real.log_le_log (by norm_num) hq256
    have h3 : Real.log 256 = 8 * Real.log 2 := by
      rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_gt_d9
    linarith
  have hexpL : Real.exp L = q := Real.exp_log hqpos
  have hF3 : Real.exp ((h : ℝ) * δ ^ 2 / 2) ^ 3 ≤ Real.exp (3 * L / 16) := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    push_cast
    linarith
  have hKNM : (2 * B / (K * N * M : ℝ)) = 1 / (2 * q) := by
    rw [hq]
    have : (0 : ℝ) < M := by positivity
    have : (0 : ℝ) < K := by exact_mod_cast hK
    have : (0 : ℝ) < N := by exact_mod_cast hN
    field_simp
    norm_num
  rw [hKNM]
  have hexp4 := exp_four
  have h4 : Real.exp (3 * L / 16) * (1 / (2 * q)) ≤ Real.exp (-4) / 2 := by
    have : Real.exp (3 * L / 16) * (1 / (2 * q)) = Real.exp (3 * L / 16 - L) / 2 := by
      rw [Real.exp_sub, hexpL]; field_simp
    rw [this]
    have : Real.exp (3 * L / 16 - L) ≤ Real.exp (-4) := Real.exp_le_exp.2 (by linarith)
    linarith
  have h5 : Real.exp (-4) ≤ 1 / 53 := by
    rw [Real.exp_neg]
    exact inv_le_of_inv_le₀ (by norm_num) (by simpa using hexp4)
  calc Real.exp ((h : ℝ) * δ ^ 2 / 2) ^ 3 * (1 / (2 * q))
      ≤ Real.exp (3 * L / 16) * (1 / (2 * q)) := by gcongr
    _ ≤ Real.exp (-4) / 2 := h4
    _ ≤ (3 / 8) ^ 4 := by norm_num; linarith

end TRS.Dev.CodebookNum

end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary TightReleaseSchedules.Stationary.Supplement

noncomputable section

namespace TRS.Dev.CodebookMain
open TRS.Dev.CodebookDep TRS.Dev.CodebookShear TRS.Dev.CodebookPath TRS.Dev.CodebookEvents
  TRS.Dev.CodebookFam TRS.Dev.CodebookRisk TRS.Dev.CodebookCount TRS.Dev.CodebookSum
  TRS.Dev.CodebookNum

variable {s : RandomSeed} {T d B K N M : ℕ}

/-- flip the activity bit of phase `p` -/
def flipC {K N M : ℕ} (p : Fin K) (θ : Cfg K N M) : Cfg K N M :=
  Function.update θ p (!(θ p).1, (θ p).2)

lemma flipC_flipC {K N M : ℕ} (p : Fin K) (θ : Cfg K N M) : flipC p (flipC p θ) = θ := by
  funext q
  by_cases hq : q = p
  · subst hq; simp [flipC]
  · simp [flipC, Function.update_of_ne hq]

def flipE {K N M : ℕ} (p : Fin K) : Cfg K N M ≃ Cfg K N M where
  toFun := flipC p
  invFun := flipC p
  left_inv := flipC_flipC p
  right_inv := flipC_flipC p

lemma iota_cases {K N M : ℕ} (p : Fin K) (θ : Cfg K N M) :
    iota θ p = θ ∨ iota θ p = flipC p θ := by
  by_cases hb : (θ p).1 = true
  · right
    simp [iota, flipC, hb]
  · left
    have hb' : (θ p).1 = false := by simpa using hb
    funext q
    by_cases hq : q = p
    · subst hq
      have : ((false : Bool), (θ q).2) = θ q := Prod.ext hb'.symm rfl
      simp [iota, this]
    · simp [iota, Function.update_of_ne hq]

abbrev Idx (K N M : ℕ) := Cfg K N M × Fin K × Fin N × Fin M

def Uset (π : ReleasePolicy s T d B) (δ : ℝ) (u : Fin M → Vector d) (N h : ℕ) (p : Fin K)
    (j : Fin N) (v : Fin M) : Set (Transcript s T d) :=
  (Epre π δ u N h p j v ∪ Ein π δ u N h p j v)ᶜ

/-! ### the null counting bound -/

lemma sumW_le (π : ReleasePolicy s T d B) (hπ : IsCausal π) (δ : ℝ) (u : Fin M → Vector d)
    (hsep : ∀ v v', v ≠ v' → δ / 2 < ‖u v - u v'‖) (h : ℕ) (hh : 1 ≤ h) :
    ∑ θ : Cfg K N M, ∑ p : Fin K, ∑ x : Fin N × Fin M,
        prob (Ein π δ u N h p x.1 x.2) (th0 (T := T) h u θ p) ≤
      2 * Fintype.card (Cfg K N M) * B := by
  set g : Fin K → (Fin T → Vector d) → ℝ := fun p ϑ => ∑ b : Fin B, prob (Gset π N h b p) ϑ
    with hg
  have hg0 : ∀ p ϑ, 0 ≤ g p ϑ := fun p ϑ => Finset.sum_nonneg fun b _ => prob_nonneg _ _
  have step1 : ∀ (θ : Cfg K N M) (p : Fin K),
      ∑ x : Fin N × Fin M, prob (Ein π δ u N h p x.1 x.2) (th0 (T := T) h u θ p) ≤
        g p (path h u θ) + g p (path h u (flipC p θ)) := by
    intro θ p
    refine (cnt_le π hπ δ u hsep h hh p _).trans ?_
    rcases iota_cases p θ with hc | hc
    · have : th0 (T := T) h u θ p = path h u θ := by unfold th0; rw [hc]
      rw [this]
      have := hg0 p (path h u (flipC p θ))
      simp only [hg] at this ⊢
      linarith
    · have : th0 (T := T) h u θ p = path h u (flipC p θ) := by unfold th0; rw [hc]
      rw [this]
      have := hg0 p (path h u θ)
      simp only [hg] at this ⊢
      linarith
  calc _ ≤ ∑ θ : Cfg K N M, ∑ p : Fin K, (g p (path h u θ) + g p (path h u (flipC p θ))) :=
        Finset.sum_le_sum fun θ _ => Finset.sum_le_sum fun p _ => step1 θ p
    _ = ∑ θ : Cfg K N M, ∑ p : Fin K, g p (path (T := T) h u θ) +
        ∑ θ : Cfg K N M, ∑ p : Fin K, g p (path (T := T) h u (flipC p θ)) := by
        simp_rw [Finset.sum_add_distrib]
    _ = 2 * ∑ θ : Cfg K N M, ∑ p : Fin K, g p (path (T := T) h u θ) := by
        have : ∑ θ : Cfg K N M, ∑ p : Fin K, g p (path (T := T) h u (flipC p θ)) =
            ∑ θ : Cfg K N M, ∑ p : Fin K, g p (path (T := T) h u θ) := by
          rw [Finset.sum_comm, Finset.sum_comm (f := fun θ p => g p (path (T := T) h u θ))]
          refine Finset.sum_congr rfl fun p _ => ?_
          exact Equiv.sum_comp (flipE p) (fun θ => g p (path (T := T) h u θ))
        rw [this]; ring
    _ ≤ 2 * ∑ θ : Cfg K N M, (B : ℝ) := by
        gcongr with θ _
        exact Gsum_le π hπ h _
    _ = _ := by simp; ring


lemma sumR_le (π : ReleasePolicy s T d B) (hπ : IsCausal π) (δ : ℝ) (u : Fin M → Vector d)
    (hsep : ∀ v v', v ≠ v' → δ / 2 < ‖u v - u v'‖) (h : ℕ) :
    ∑ θ : Cfg K N M, ∑ p : Fin K, ∑ j : Fin N, ∑ v : Fin M,
        prob (Epre π δ u N h p j v) (thFull (T := T) h u θ p j v) ≤
      Fintype.card (Cfg K N M) * K * N := by
  calc _ ≤ ∑ θ : Cfg K N M, ∑ p : Fin K, ∑ j : Fin N, (1 : ℝ) := by
        refine Finset.sum_le_sum fun θ _ => Finset.sum_le_sum fun p _ =>
          Finset.sum_le_sum fun j _ => ?_
        simp_rw [pre_eq π hπ δ u h θ p j]
        exact sum_pre_le π hπ δ u hsep h p j _
    _ = _ := by simp; ring

lemma sumX_le (π : ReleasePolicy s T d B) (hπ : IsCausal π) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (u : Fin M → Vector d) (hu : ∀ v, ‖u v‖ ≤ δ)
    (hsep : ∀ v v', v ≠ v' → δ / 2 < ‖u v - u v'‖) (h : ℕ) (hh : 1 ≤ h)
    (hT : 1 + K * N * h ≤ T) (hB : 1 ≤ B) (hK : 1 ≤ K) (hN : 1 ≤ N) (hM : 2 ≤ M)
    (hMKN : 1024 * B ≤ M * K * N)
    (hinfo : (h : ℝ) * δ ^ 2 ≤ (1 / 8) * Real.log ((M * K * N : ℝ) / (4 * B))) :
    ∑ θ : Cfg K N M, ∑ p : Fin K, ∑ j : Fin N, ∑ v : Fin M,
        prob (Ein π δ u N h p j v) (thFull (T := T) h u θ p j v) ≤
      (3 / 8) * (Fintype.card (Cfg K N M) * K * N * M) := by
  set F : ℝ := Real.exp ((h : ℝ) * δ ^ 2 / 2) with hF
  have hF0 : 0 ≤ F := (Real.exp_pos _).le
  let Xf : Idx K N M → ℝ := fun i => prob (Ein π δ u N h i.2.1 i.2.2.1 i.2.2.2)
    (thFull (T := T) h u i.1 i.2.1 i.2.2.1 i.2.2.2)
  let Yf : Idx K N M → ℝ := fun i => prob (Ein π δ u N h i.2.1 i.2.2.1 i.2.2.2)
    (thMid (T := T) h u i.1 i.2.1 i.2.2.1 i.2.2.2)
  let Wf : Idx K N M → ℝ := fun i => prob (Ein π δ u N h i.2.1 i.2.2.1 i.2.2.2)
    (th0 (T := T) h u i.1 i.2.1)
  have h1 : ∀ i ∈ (Finset.univ : Finset (Idx K N M)), Xf i ^ 2 ≤ F * Yf i := by
    intro i _
    exact cs_block _ (measurableSet_Ein π hπ δ u N h _ _ _) δ hδ0 hδ1 h _ _
      (aRow_add_le h T hT i.2.1 i.2.2.1) _ _ _ (norm_half δ hδ0 _ (hu _))
      (fun k => diff_full_mid h u i.1 i.2.1 i.2.2.1 i.2.2.2 k)
  have h2 : ∀ i ∈ (Finset.univ : Finset (Idx K N M)), Yf i ^ 2 ≤ F * Wf i := by
    intro i _
    exact cs_block _ (measurableSet_Ein π hπ δ u N h _ _ _) δ hδ0 hδ1 h _ _
      (aRow_add_le h T hT i.2.1 i.2.2.1) _ _ _ (norm_half δ hδ0 _ (hu _))
      (fun k => diff_mid_zero h u i.1 i.2.1 i.2.2.1 i.2.2.2 k)
  have key := alg4 (Finset.univ : Finset (Idx K N M)) Xf Yf Wf F hF0 (fun i => prob_nonneg _ _)
    (fun i => prob_nonneg _ _) h1 h2
  have hW : ∑ i : Idx K N M, Wf i ≤ 2 * Fintype.card (Cfg K N M) * B := by
    have := sumW_le (T := T) (N := N) (K := K) π hπ δ u hsep h hh
    simp only [Wf, Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type] at this
    exact this
  have hX : ∑ i : Idx K N M, Xf i = ∑ θ : Cfg K N M, ∑ p : Fin K, ∑ j : Fin N, ∑ v : Fin M,
        prob (Ein π δ u N h p j v) (thFull (T := T) h u θ p j v) := by
    simp only [Xf, Fintype.sum_prod_type]
  rw [← hX]
  set A : ℝ := Fintype.card (Cfg K N M) * K * N * M with hA
  have hcardIdx : ((Finset.univ : Finset (Idx K N M)).card : ℝ) = A := by
    simp [hA, Fintype.card_prod]
    ring
  rw [hcardIdx] at key
  have hcard0 : (0 : ℝ) < Fintype.card (Cfg K N M) := by
    have : Nonempty (Cfg K N M) := ⟨fun _ => (true, ⟨0, by omega⟩, ⟨0, by omega⟩)⟩
    exact_mod_cast Fintype.card_pos
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hA0 : 0 < A := by positivity
  have hnum := numeric B K N M h δ hB hK hN hM hMKN hinfo
  have hSW : 0 ≤ ∑ i : Idx K N M, Wf i := Finset.sum_nonneg fun i _ => prob_nonneg _ _
  have hfin : (∑ i : Idx K N M, Xf i) ^ 4 ≤ ((3 / 8) * A) ^ 4 := by
    calc (∑ i : Idx K N M, Xf i) ^ 4 ≤ F ^ 3 * A ^ 3 * (2 * Fintype.card (Cfg K N M) * B) := by
          refine key.trans ?_
          gcongr
      _ = A ^ 4 * (F ^ 3 * (2 * B / (K * N * M : ℝ))) := by
          rw [hA]; field_simp
      _ ≤ A ^ 4 * (3 / 8) ^ 4 := by gcongr
      _ = _ := by ring
  exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) hfin


lemma rr_sum (π : ReleasePolicy s T d B) (δ : ℝ) (u : Fin M → Vector d) (h : ℕ) (c : ℝ)
    (hN : 1 ≤ N) (hM : 1 ≤ M) :
    ∑ θ : Cfg K N M, (∑ p : Fin K, if (θ p).1 = true then
        c * prob (Uset π δ u N h p (θ p).2.1 (θ p).2.2) (path (T := T) h u θ) else 0) =
      c / (2 * N * M) * ∑ θ : Cfg K N M, ∑ p : Fin K, ∑ j : Fin N, ∑ v : Fin M,
        prob (Uset π δ u N h p j v) (thFull (T := T) h u θ p j v) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hY : (Fintype.card (Bool × Fin N × Fin M) : ℝ) = 2 * N * M := by
    simp [Fintype.card_prod]; ring
  have per_p : ∀ p : Fin K, ∑ θ : Cfg K N M, (if (θ p).1 = true then
        c * prob (Uset π δ u N h p (θ p).2.1 (θ p).2.2) (path (T := T) h u θ) else 0) =
      c / (2 * N * M) * ∑ θ : Cfg K N M, ∑ j : Fin N, ∑ v : Fin M,
        prob (Uset π δ u N h p j v) (thFull (T := T) h u θ p j v) := by
    intro p
    have pt : ∀ θ : Cfg K N M, (if (θ p).1 = true then
        c * prob (Uset π δ u N h p (θ p).2.1 (θ p).2.2) (path (T := T) h u θ) else 0) =
        ∑ x : Fin N × Fin M, (if θ p = (true, x) then
          c * prob (Uset π δ u N h p x.1 x.2) (path (T := T) h u θ) else 0) := by
      intro θ
      by_cases hb : (θ p).1 = true
      · rw [if_pos hb, Finset.sum_eq_single (θ p).2]
        · have e : θ p = ((true : Bool), (θ p).2) := Prod.ext hb rfl
          rw [if_pos e]
        · intro x _ hx
          rw [if_neg]
          intro hc
          apply hx
          have := congrArg Prod.snd hc
          simpa using this.symm
        · intro h'; exact absurd (Finset.mem_univ _) h'
      · rw [if_neg hb]
        symm
        refine Finset.sum_eq_zero fun x _ => ?_
        rw [if_neg]
        intro hc
        apply hb
        rw [hc]
    calc _ = ∑ θ : Cfg K N M, ∑ x : Fin N × Fin M, (if θ p = (true, x) then
          c * prob (Uset π δ u N h p x.1 x.2) (path (T := T) h u θ) else 0) :=
          Finset.sum_congr rfl fun θ _ => pt θ
      _ = ∑ x : Fin N × Fin M, ∑ θ : Cfg K N M, (if θ p = (true, x) then
          c * prob (Uset π δ u N h p x.1 x.2) (path (T := T) h u θ) else 0) := Finset.sum_comm
      _ = ∑ x : Fin N × Fin M, (1 / (2 * N * M)) * ∑ θ : Cfg K N M,
          c * prob (Uset π δ u N h p x.1 x.2) (thFull (T := T) h u θ p x.1 x.2) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          have := resample p ((true, x) : Bool × Fin N × Fin M)
            (fun θ => c * prob (Uset π δ u N h p x.1 x.2) (path (T := T) h u θ))
          rw [hY] at this
          have hne : (2 * (N : ℝ) * M) ≠ 0 := by positivity
          have e : ∑ θ : Cfg K N M, c * prob (Uset π δ u N h p x.1 x.2)
              (thFull (T := T) h u θ p x.1 x.2) = ∑ θ : Cfg K N M, c *
              prob (Uset π δ u N h p x.1 x.2) (path (T := T) h u (Function.update θ p (true, x))) :=
            rfl
          rw [e, this]
          field_simp
      _ = _ := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          simp_rw [← Finset.mul_sum]
          simp only [Fintype.sum_prod_type]
          ring
  calc _ = ∑ p : Fin K, ∑ θ : Cfg K N M, (if (θ p).1 = true then
        c * prob (Uset π δ u N h p (θ p).2.1 (θ p).2.2) (path (T := T) h u θ) else 0) := by
        rw [Finset.sum_comm]
    _ = ∑ p : Fin K, c / (2 * N * M) * ∑ θ : Cfg K N M, ∑ j : Fin N, ∑ v : Fin M,
        prob (Uset π δ u N h p j v) (thFull (T := T) h u θ p j v) :=
        Finset.sum_congr rfl fun p _ => per_p p
    _ = _ := by
        rw [← Finset.mul_sum, Finset.sum_comm]


lemma Q_ge (π : ReleasePolicy s T d B) (hπ : IsCausal π) (δ : ℝ) (u : Fin M → Vector d) (h : ℕ)
    (p : Fin K) (j : Fin N) (v : Fin M) (ϑ : Fin T → Vector d) :
    1 - prob (Epre π δ u N h p j v) ϑ - prob (Ein π δ u N h p j v) ϑ ≤
      prob (Uset π δ u N h p j v) ϑ := by
  unfold Uset
  rw [prob_compl _ ((measurableSet_Epre π hπ δ u N h p j v).union
    (measurableSet_Ein π hπ δ u N h p j v))]
  have := prob_union_le (Epre π δ u N h p j v) (Ein π δ u N h p j v) ϑ
  linarith

theorem exists_good (π : ReleasePolicy s T d B) (hπ : IsCausal π) (δ : ℝ) (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) (u : Fin M → Vector d) (hu : ∀ v, ‖u v‖ ≤ δ)
    (hsep : ∀ v v', v ≠ v' → δ / 2 < ‖u v - u v'‖) (h : ℕ) (hh : 1 ≤ h)
    (hT : 1 + K * N * h ≤ T) (hB : 1 ≤ B) (hK : 1 ≤ K) (hN : 1 ≤ N) (hM : 2 ≤ M)
    (hMKN : 1024 * B ≤ M * K * N)
    (hinfo : (h : ℝ) * δ ^ 2 ≤ (1 / 8) * Real.log ((M * K * N : ℝ) / (4 * B))) :
    ∃ θ : Cfg K N M, (K : ℝ) * h * δ ^ 2 / 512 ≤
      ∑ p : Fin K, if (θ p).1 = true then ((h : ℝ) * δ ^ 2 / 32) *
        prob (Uset π δ u N h p (θ p).2.1 (θ p).2.2) (path (T := T) h u θ) else 0 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  haveI : Nonempty (Cfg K N M) := ⟨fun _ => (true, ⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  have hcard0 : (0 : ℝ) < Fintype.card (Cfg K N M) := by exact_mod_cast Fintype.card_pos
  set c : ℝ := (h : ℝ) * δ ^ 2 / 32 with hc
  have hc0 : 0 < c := by
    have : (0 : ℝ) < h := by exact_mod_cast hh
    positivity
  set A : ℝ := Fintype.card (Cfg K N M) * K * N * M with hA
  have hA0 : 0 < A := by positivity
  have hSX := sumX_le π hπ δ hδ0.le hδ1 u hu hsep h hh hT hB hK hN hM hMKN hinfo
  have hSR := sumR_le (T := T) (K := K) (N := N) π hπ δ u hsep h
  have hQ : A / 8 ≤ ∑ θ : Cfg K N M, ∑ p : Fin K, ∑ j : Fin N, ∑ v : Fin M,
      prob (Uset π δ u N h p j v) (thFull (T := T) h u θ p j v) := by
    have hlow : ∑ θ : Cfg K N M, ∑ p : Fin K, ∑ j : Fin N, ∑ v : Fin M,
        (1 - prob (Epre π δ u N h p j v) (thFull (T := T) h u θ p j v) -
          prob (Ein π δ u N h p j v) (thFull (T := T) h u θ p j v)) ≤
        ∑ θ : Cfg K N M, ∑ p : Fin K, ∑ j : Fin N, ∑ v : Fin M,
          prob (Uset π δ u N h p j v) (thFull (T := T) h u θ p j v) :=
      Finset.sum_le_sum fun θ _ => Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun j _ =>
        Finset.sum_le_sum fun v _ => Q_ge π hπ δ u h p j v _
    have e : ∑ θ : Cfg K N M, ∑ p : Fin K, ∑ j : Fin N, ∑ v : Fin M,
        (1 - prob (Epre π δ u N h p j v) (thFull (T := T) h u θ p j v) -
          prob (Ein π δ u N h p j v) (thFull (T := T) h u θ p j v)) =
        A - ∑ θ : Cfg K N M, ∑ p : Fin K, ∑ j : Fin N, ∑ v : Fin M,
          prob (Epre π δ u N h p j v) (thFull (T := T) h u θ p j v) -
        ∑ θ : Cfg K N M, ∑ p : Fin K, ∑ j : Fin N, ∑ v : Fin M,
          prob (Ein π δ u N h p j v) (thFull (T := T) h u θ p j v) := by
      simp only [Finset.sum_sub_distrib, hA]
      simp
      ring
    have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
    have : (Fintype.card (Cfg K N M) : ℝ) * K * N * 2 ≤ A := by
      rw [hA]
      have : 0 < (Fintype.card (Cfg K N M) : ℝ) * K * N := by positivity
      nlinarith
    linarith
  have hsum := rr_sum (T := T) (K := K) π δ u h c hN (by omega)
  have hbound : (Fintype.card (Cfg K N M) : ℝ) * ((K : ℝ) * h * δ ^ 2 / 512) ≤
      ∑ θ : Cfg K N M, ∑ p : Fin K, if (θ p).1 = true then c *
        prob (Uset π δ u N h p (θ p).2.1 (θ p).2.2) (path (T := T) h u θ) else 0 := by
    rw [hsum]
    have h1 : c / (2 * N * M) * (A / 8) ≤ c / (2 * N * M) * ∑ θ : Cfg K N M, ∑ p : Fin K,
        ∑ j : Fin N, ∑ v : Fin M,
          prob (Uset π δ u N h p j v) (thFull (T := T) h u θ p j v) := by
      gcongr
    refine le_trans (le_of_eq ?_) h1
    rw [hA, hc]
    field_simp
    ring
  by_contra hcon
  push Not at hcon
  have : ∑ θ : Cfg K N M, ∑ p : Fin K, (if (θ p).1 = true then c *
        prob (Uset π δ u N h p (θ p).2.1 (θ p).2.2) (path (T := T) h u θ) else 0) <
      ∑ θ : Cfg K N M, ((K : ℝ) * h * δ ^ 2 / 512) :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun θ _ => hcon θ
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
  linarith

end TRS.Dev.CodebookMain

end
end

section
/-!
# PLAN for Theorem 6.1 (codebook pulses), part 2   (q382)

Notation.  `Θ = Fin K → Bool × Fin N × Fin M` (uniform), `path θ = pulsePath h u Z J V`.
`a(p,j) = 1 + (pN+j)h` (start row of block `j` of phase `p`), block `I(p,j) = [a, a+h)`; the
blocks are pairwise disjoint (`CodebookPath.act_unique`), `I(p,j) ⊆ W_p = (1+pNh, 1+(p+1)Nh]`.
`near v x :⇔ ‖x - u v‖ < δ/4`; by `hsep` at most one `v` has `near v x`.
`μ = law ⊗ gaussianRows`, `prob S ϑ = μ{(σ,z) | (σ, obs ϑ z) ∈ S}` (real), `F = exp(hδ²/2)`.

Step 1 (risk of one path).  For a causal `π`, transcripts `ω`, block `(p,j)`, code `v`:
 `Epre(p,j,v) = {near v (deployed 0 π ω a)}`,
 `Ein(p,j,v)  = {∃ slot s, a < date s ω < a+h ∧ near v (head s ω)}`,  `U = (Epre ∪ Ein)ᶜ`.
 Since dates are monotone, `deployed` at row `i∈I(p,j)` is the head of the last slot dated `≤ i`
 (or `0`); that slot is the last one dated `≤ a` (so `deployed … a` is near `u v`) or is dated in
 `(a, a+h)`.  So on `U`, `‖deployed i - u v‖ ≥ δ/4` for every `i ∈ I(p,j)`.
 If `θ = (Z,J,V)` has `Z p`, `J p = j`, `V p = v` then `θ_i = u v` on `I(p,j)`, hence
 `½ Σ_{i∈I} ‖dep_i - θ_i‖² ≥ h δ²/32 · 1_U`.  Blocks of distinct phases are disjoint, so
 `risk(θ) ≥ ofReal( Σ_p [Z p] (hδ²/32) · prob U(p,J p,V p) (path θ) ) =: ofReal(rr θ)`.
 It suffices to find `θ` with `rr θ ≥ Khδ²/512`, i.e. `Σ_θ rr θ ≥ |Θ| K hδ²/512`.
Step 2 (resampling).  `Σ_θ rr θ = (hδ²/(64 N M)) Σ_{i∈I} prob U_i(ϑfull_i)`,  `I = Θ×K×N×M`,
 `A := |I| = |Θ|KNM`, `ϑfull(θ,p,j,v) = path(update θ p (true,j,v))`
 (`Σ_{θ:θ p = y} f θ = |Y|⁻¹ Σ_θ f(update θ p y)`).  `prob U ≥ 1 - pre - X`, `pre = prob Epre ϑfull`,
 `X = prob Ein ϑfull`.
Step 3 (pre part).  `deployed … a` depends only on seed and rows `< a`
 (`information a`-measurability), and `ϑfull`, `ϑ⁰ = path(update θ p (false,·))` agree there, so
 `pre = prob Epre ϑ⁰`; pointwise `Σ_v 1_{Epre(p,j,v)} ≤ 1` ⇒ `Σ_I pre ≤ |Θ|KN = A/M ≤ A/2`.
Step 4 (in part, change of measure).  `ϑmid = ϑ⁰ + (u v/2) 1_I`.  Shear lemma (copied): for
 paths differing by `e_i` with `‖e_i‖² ≤ 1/4`, `prob S ϑ'² ≤ exp(2Σ‖e_i‖²) · prob S ϑ`; here
 `Σ‖e_i‖² ≤ hδ²/4`, factor `F = exp(hδ²/2)`.  With `X=prob Ein ϑfull, Y = … ϑmid, W = … ϑ⁰`:
 `X² ≤ F Y`, `Y² ≤ F W`; Cauchy–Schwarz over `I`: `(ΣX)⁴ ≤ F³ A³ ΣW`.
 Counting: `Σ_{j,v} 1_{Ein(p,j,v)} ≤ #{s : date s ∈ W_p}` (one block, one code per slot), and `Σ_p ≤ B`;
 using `Σ_θ g(ι_p θ) ≤ 2 Σ_θ g θ` (`ι_p θ = update θ p (false,·)`, pointwise
 `g(ι θ) ≤ g θ + g(flip θ)`): `ΣW ≤ 2 |Θ| B`.  Hence `(ΣX/A)⁴ ≤ F³ · 2B/(KNM) = exp(3hδ²/2)/(2q)`,
 `q = MKN/(4B) ≥ 256`, `hδ² ≤ (log q)/8` ⇒ `≤ exp(-13 log q/16)/2 ≤ 0.006 < (3/8)⁴`; so `ΣX ≤ 3A/8`.
Step 5 (numerics).  `Σ_I prob U ≥ A(1 - 1/2 - 3/8) = A/8`, so
 `Σ_θ rr θ ≥ hδ²/(64NM) · A/8 = |Θ| K hδ²/512`.  (`hM : 2 ≤ M` used for `1/M ≤ 1/2`.)
-/

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary TightReleaseSchedules.Stationary.Supplement

namespace TRS

theorem chk_codebook_pulses (T d B K N h M : ℕ) (hd : 1 ≤ d) (hB : 1 ≤ B) (hK : 1 ≤ K)
    (hN : 1 ≤ N) (hh : 1 ≤ h) (δ : ℝ) (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (u : Fin M → Vector d) (hM : 2 ≤ M) (hu : ∀ v, ‖u v‖ ≤ δ)
    (hsep : ∀ v v', v ≠ v' → δ / 2 < ‖u v - u v'‖)
    (hTKNh : 1 + K * N * h ≤ T) (hMKN : 1024 * B ≤ M * K * N)
    (hinfo : (h : ℝ) * δ ^ 2 ≤ (1 / 8) * Real.log ((M * K * N : ℝ) / (4 * B))) :
    (∀ θ ∈ pulseFamily T d K N M h u,
        (∀ i : Fin T, i.val = 0 → θ i = 0) ∧
        (∀ i, ‖θ i‖ ≤ δ) ∧
        totalVariation θ ≤ 2 * K * δ ∧
        changeCount θ ≤ 2 * K ∧
        (2 * K ≤ B → ∃ π' : ReleasePolicy unitSeed T d B,
          IsCausal π' ∧ HasDeterministicDates π' ∧ ∀ ω i, deployed 0 π' ω i = θ i)) ∧
    (∀ (s : RandomSeed) (π : ReleasePolicy s T d B), IsCausal π →
      ∃ θ ∈ pulseFamily T d K N M h u,
        ENNReal.ofReal ((K : ℝ) * h * δ ^ 2 / 512) ≤ policyRisk 0 π θ) := by
  refine ⟨?_, ?_⟩
  · rintro θ ⟨Z, J, V, rfl⟩
    exact ⟨fun i hi => TRS.Dev.CodebookPath.pulsePath_zero h u Z J V i hi,
      fun i => TRS.Dev.CodebookPath.norm_pulsePath_le h u Z J V δ hδ.le hu i,
      TRS.Dev.CodebookPath.totalVariation_le h u Z J V δ hδ.le hu,
      TRS.Dev.CodebookPath.changeCount_le h u Z J V,
      fun hKB => ⟨TRS.Dev.CodebookPolicy.pol T B N h u Z J V,
        TRS.Dev.CodebookPolicy.isCausal_pol T B N h u Z J V hTKNh,
        TRS.Dev.CodebookPolicy.hasDet_pol T B N h u Z J V,
        fun ω i => TRS.Dev.CodebookPolicy.deployed_pol T B N h u Z J V hTKNh hKB ω i⟩⟩
  · intro s π hπ
    obtain ⟨θ, hθ⟩ := TRS.Dev.CodebookMain.exists_good π hπ δ hδ hδ₁ u hu hsep h hh hTKNh hB hK hN
      hM hMKN hinfo
    refine ⟨TRS.Dev.CodebookFam.path h u θ, ⟨fun p => (θ p).1, fun p => (θ p).2.1,
      fun p => (θ p).2.2, rfl⟩, ?_⟩
    refine le_trans (ENNReal.ofReal_le_ofReal hθ) ?_
    exact TRS.Dev.CodebookRisk.risk_ge π hπ δ hδ.le u h hh hTKNh (fun p => (θ p).1)
      (fun p => (θ p).2.1) (fun p => (θ p).2.2)

end TRS
end

theorem solution : type_of% @TRS.chk_codebook_pulses := @TRS.chk_codebook_pulses
