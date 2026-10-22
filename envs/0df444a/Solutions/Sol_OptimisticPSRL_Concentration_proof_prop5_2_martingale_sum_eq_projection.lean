-- Prove2me | solution 1 for OptimisticPSRL.Concentration.proof_prop5_2_martingale_sum_eq_projection
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:44:46.648776+00:00
-- url     : https://prove2.me/submissions/8e2d72d4-166a-4ebd-9bb0-f3e5e3f2fae0

import Mathlib
import Definitions.Def_OptimisticPSRL_Concentration_Setting

set_option autoImplicit false

open OptimisticPSRL.Concentration

theorem core_abel (S : ℕ) (Hh P Q : ℕ → ℝ)
    (hP : ∀ n, 0 ≤ P n) (hP1 : ∑ n ∈ Finset.range S, P n = 1)
    (hQ1 : ∑ n ∈ Finset.range S, Q n = 1) :
    ∑ n ∈ Finset.range S,
      (Hh n - (∑ m ∈ Finset.Ico (n + 1) S, Hh m * P m) / (∑ m ∈ Finset.Ico (n + 1) S, P m)) *
        (Q n - P n / (∑ m ∈ Finset.Ico n S, P m) * ∑ m ∈ Finset.Ico n S, Q m)
      = ∑ n ∈ Finset.range S, (Q n - P n) * Hh n := by
  set TP : ℕ → ℝ := fun m => ∑ x ∈ Finset.Ico m S, P x with hTP
  set TQ : ℕ → ℝ := fun m => ∑ x ∈ Finset.Ico m S, Q x with hTQ
  set V : ℕ → ℝ := fun m => ∑ x ∈ Finset.Ico m S, Hh x * P x with hV
  have hTPs : ∀ n, n < S → TP n = P n + TP (n + 1) := by
    intro n hn; simp only [hTP]; exact Finset.sum_eq_sum_Ico_succ_bot hn _
  have hTQs : ∀ n, n < S → TQ n = Q n + TQ (n + 1) := by
    intro n hn; simp only [hTQ]; exact Finset.sum_eq_sum_Ico_succ_bot hn _
  have hVs : ∀ n, n < S → V n = Hh n * P n + V (n + 1) := by
    intro n hn; simp only [hV]; exact Finset.sum_eq_sum_Ico_succ_bot hn _
  have hTPnn : ∀ n, 0 ≤ TP n := fun n => Finset.sum_nonneg (fun m _ => hP m)
  set g : ℕ → ℝ := fun n => TQ n / TP n with hg
  have stepa : ∀ n, n < S →
      (V (n + 1) / TP (n + 1)) * (Q n - P n / TP n * TQ n) = V (n + 1) * (g n - g (n + 1)) := by
    intro n hn
    by_cases h0 : TP (n + 1) = 0
    · have hz : ∀ m ∈ Finset.Ico (n + 1) S, P m = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun m _ => hP m)).mp h0
      have hV0 : V (n + 1) = 0 := by
        simp only [hV]
        exact Finset.sum_eq_zero (fun m hm => by rw [hz m hm]; ring)
      rw [hV0]; simp
    · have hpos : 0 < TP (n + 1) := lt_of_le_of_ne (hTPnn _) (Ne.symm h0)
      have hpos0 : 0 < TP n := by rw [hTPs n hn]; linarith [hP n]
      have e1 := hTPs n hn
      have e2 := hTQs n hn
      simp only [hg]
      rw [e2, e1]
      rw [e1] at hpos0
      field_simp
      ring
  have abel : ∀ k, k ≤ S →
      ∑ n ∈ Finset.range k, V (n + 1) * (g n - g (n + 1))
        = V 0 * g 0 - V k * g k - ∑ n ∈ Finset.range k, Hh n * P n * g n := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      rw [Finset.sum_range_succ, ih (by omega), Finset.sum_range_succ]
      have hVk := hVs k (by omega)
      rw [hVk]; ring
  have hVS : V S = 0 := by simp [hV]
  have hV0 : V 0 = ∑ n ∈ Finset.range S, Hh n * P n := by
    simp only [hV]; rw [Finset.range_eq_Ico]
  have hg0 : g 0 = 1 := by
    simp only [hg, hTP, hTQ]
    rw [← Finset.range_eq_Ico, hP1, hQ1]; norm_num
  have habel := abel S le_rfl
  rw [hVS, hg0, hV0] at habel
  have e1 : ∀ n ∈ Finset.range S,
      (Hh n - (V (n + 1)) / (TP (n + 1))) * (Q n - P n / TP n * TQ n)
        = Hh n * (Q n - P n * g n) - V (n + 1) * (g n - g (n + 1)) := by
    intro n hn
    have := stepa n (Finset.mem_range.mp hn)
    have hφ : Q n - P n / TP n * TQ n = Q n - P n * g n := by
      simp only [hg]; ring
    rw [sub_mul, this, hφ]
  show ∑ n ∈ Finset.range S, (Hh n - (V (n + 1)) / (TP (n + 1))) * (Q n - P n / TP n * TQ n) = _
  rw [Finset.sum_congr rfl e1, Finset.sum_sub_distrib, habel]
  have h2 : ∀ n ∈ Finset.range S, Hh n * (Q n - P n * g n)
      = (Q n - P n) * Hh n + (Hh n * P n - Hh n * P n * g n) := by
    intro n _; ring
  rw [Finset.sum_congr rfl h2, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [mul_one, zero_mul, sub_zero]
  ring

def extF {S : ℕ} (f : Fin S → ℝ) (n : ℕ) : ℝ := if h : n < S then f ⟨n, h⟩ else 0

theorem extF_val {S : ℕ} (f : Fin S → ℝ) (i : Fin S) : extF f i.val = f i := by
  simp [extF]

theorem extF_nonneg {S : ℕ} (f : Fin S → ℝ) (hf : ∀ i, 0 ≤ f i) (n : ℕ) : 0 ≤ extF f n := by
  unfold extF; split_ifs
  · exact hf _
  · exact le_rfl

theorem extF_mul {S : ℕ} (f g : Fin S → ℝ) (n : ℕ) :
    extF (fun j => f j * g j) n = extF f n * extF g n := by
  unfold extF; split_ifs <;> simp

theorem sum_ge_aux {S : ℕ} (f : Fin S → ℝ) (m : ℕ) :
    ∑ j ∈ Finset.univ.filter (fun j : Fin S => m ≤ j.val), f j
      = ∑ n ∈ Finset.Ico m S, extF f n := by
  rw [Finset.sum_filter]
  have : ∀ j : Fin S, (if m ≤ j.val then f j else 0)
      = (fun n => if m ≤ n then extF f n else 0) j.val := by
    intro j; simp [extF_val]
  rw [Finset.sum_congr rfl (fun j _ => this j),
    Fin.sum_univ_eq_sum_range (fun n => if m ≤ n then extF f n else 0) S]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext n; simp [Finset.mem_Ico]; omega

theorem tail_eq {S : ℕ} (p : Fin S → ℝ) (i : Fin S) :
    tail p i = ∑ n ∈ Finset.Ico i.val S, extF p n := by
  unfold tail; exact sum_ge_aux p i.val

theorem tailAfter_eq {S : ℕ} (p : Fin S → ℝ) (i : Fin S) :
    tailAfter p i = ∑ n ∈ Finset.Ico (i.val + 1) S, extF p n := by
  unfold tailAfter; exact sum_ge_aux p (i.val + 1)

theorem term_eq {S : ℕ} (p h q : Fin S → ℝ) (i : Fin S) :
    cCoef p h i * (q i - p i / tail p i * tail q i)
      = (extF h i.val - (∑ m ∈ Finset.Ico (i.val + 1) S, extF h m * extF p m)
            / (∑ m ∈ Finset.Ico (i.val + 1) S, extF p m)) *
        (extF q i.val - extF p i.val / (∑ m ∈ Finset.Ico i.val S, extF p m)
            * ∑ m ∈ Finset.Ico i.val S, extF q m) := by
  have e1 : (∑ j ∈ Finset.univ.filter (fun j : Fin S => i < j), h j * p j)
      = ∑ m ∈ Finset.Ico (i.val + 1) S, extF h m * extF p m := by
    have := sum_ge_aux (fun j => h j * p j) (i.val + 1)
    simp only [extF_mul] at this
    exact this
  unfold cCoef Hnext
  rw [e1, tailAfter_eq, tail_eq p, tail_eq q, extF_val, extF_val, extF_val]

theorem core_fin {S : ℕ} (p h q : Fin S → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (hq1 : ∑ i, q i = 1) :
    ∑ i, cCoef p h i * (q i - p i / tail p i * tail q i) = ∑ i, (q i - p i) * h i := by
  have hs : ∀ f : Fin S → ℝ, ∑ i, f i = ∑ n ∈ Finset.range S, extF f n := by
    intro f
    rw [← Fin.sum_univ_eq_sum_range (extF f) S]
    exact Finset.sum_congr rfl (fun i _ => (extF_val f i).symm)
  have := core_abel S (extF h) (extF p) (extF q) (extF_nonneg p hp)
    (by rw [← hs]; exact hp1) (by rw [← hs]; exact hq1)
  rw [Finset.sum_congr rfl (fun i _ => term_eq p h q i)]
  rw [Fin.sum_univ_eq_sum_range (fun n => (extF h n - (∑ m ∈ Finset.Ico (n + 1) S, extF h m * extF p m)
            / (∑ m ∈ Finset.Ico (n + 1) S, extF p m)) *
        (extF q n - extF p n / (∑ m ∈ Finset.Ico n S, extF p m)
            * ∑ m ∈ Finset.Ico n S, extF q m)) S]
  rw [this]
  rw [← Fin.sum_univ_eq_sum_range (fun n => (extF q n - extF p n) * extF h n) S]
  exact Finset.sum_congr rfl (fun i _ => by simp only [extF_val])

theorem solution {S n : ℕ} (p h : Fin S → ℝ)
    (hp : IsProbVec p) (hn : 0 < n) (ω : Fin n → Fin S) (hω : ∀ t, 0 < p (ω t)) :
    ((∑ t, ∑ i, Zcoord p h i (ω t)) / n =
        ∑ i, cCoef p h i * phat ω i - ∑ i, cCoef p h i * p i / tail p i * tail (phat ω) i) ∧
      (∑ i, cCoef p h i * phat ω i - ∑ i, cCoef p h i * p i / tail p i * tail (phat ω) i =
        ∑ i ∈ belowLast S, (yRatio (phat ω) i - yRatio p i) * tail (phat ω) i * cCoef p h i) ∧
      (∑ i ∈ belowLast S, (yRatio (phat ω) i - yRatio p i) * tail (phat ω) i * cCoef p h i =
        ∑ i, (phat ω i - p i) * h i) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hph_nn : ∀ i, 0 ≤ phat ω i := by intro i; unfold phat; positivity
  have h1 : ∀ i, ∑ t, (if ω t = i then (1 : ℝ) else 0) = n * phat ω i := by
    intro i
    rw [Finset.sum_boole]; unfold phat; field_simp
  have hph_sum : ∑ i, phat ω i = 1 := by
    have hh : ∑ i, (n : ℝ) * phat ω i = n := by
      calc ∑ i, (n : ℝ) * phat ω i = ∑ i, ∑ t, (if ω t = i then (1 : ℝ) else 0) :=
            Finset.sum_congr rfl (fun i _ => (h1 i).symm)
        _ = ∑ t, ∑ i, (if ω t = i then (1 : ℝ) else 0) := Finset.sum_comm
        _ = n := by simp
    rw [← Finset.mul_sum] at hh
    have : (n : ℝ) * (∑ i, phat ω i) = n * 1 := by rw [hh, mul_one]
    exact mul_left_cancel₀ hn' this
  have h2 : ∀ i, ∑ t, (if i ≤ ω t then (1 : ℝ) else 0) = n * tail (phat ω) i := by
    intro i
    unfold tail
    rw [Finset.mul_sum]
    calc ∑ t, (if i ≤ ω t then (1 : ℝ) else 0)
        = ∑ t, ∑ j ∈ Finset.univ.filter (fun j => i ≤ j), (if ω t = j then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl (fun t _ => ?_)
          rw [Finset.sum_ite_eq]
          simp
      _ = ∑ j ∈ Finset.univ.filter (fun j => i ≤ j), ∑ t, (if ω t = j then (1 : ℝ) else 0) :=
          Finset.sum_comm
      _ = _ := Finset.sum_congr rfl (fun j _ => h1 j)
  -- Fact A
  have hA : ∀ i, phat ω i = yRatio (phat ω) i * tail (phat ω) i := by
    intro i
    have hle : phat ω i ≤ tail (phat ω) i := by
      unfold tail
      exact Finset.single_le_sum (f := fun j => phat ω j) (fun j _ => hph_nn j) (by simp)
    unfold yRatio
    by_cases h0 : tail (phat ω) i = 0
    · have : phat ω i = 0 := le_antisymm (h0 ▸ hle) (hph_nn i)
      rw [this, h0]; simp
    · rw [div_mul_cancel₀ _ h0]
  have hB : ∀ i, (yRatio (phat ω) i - yRatio p i) * tail (phat ω) i * cCoef p h i
      = cCoef p h i * (phat ω i - p i / tail p i * tail (phat ω) i) := by
    intro i
    calc (yRatio (phat ω) i - yRatio p i) * tail (phat ω) i * cCoef p h i
        = (yRatio (phat ω) i * tail (phat ω) i - p i / tail p i * tail (phat ω) i)
            * cCoef p h i := by unfold yRatio; ring
      _ = _ := by rw [← hA i]; ring
  have hC : ∀ i, i ∉ belowLast S →
      cCoef p h i * (phat ω i - p i / tail p i * tail (phat ω) i) = 0 := by
    intro i hi
    have hlast : i.val + 1 = S := by
      have := i.isLt
      simp only [belowLast, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      omega
    have htail : ∀ q : Fin S → ℝ, tail q i = q i := by
      intro q
      rw [tail_eq, show Finset.Ico i.val S = {i.val} by
        ext x; simp [Finset.mem_Ico]; omega]
      simp [extF_val]
    rw [htail, htail]
    by_cases h0 : phat ω i = 0
    · simp [h0]
    · have hc : (Finset.univ.filter (fun t => ω t = i)).card ≠ 0 := by
        intro hc; apply h0; unfold phat; rw [hc]; simp
      obtain ⟨t, ht⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hc)
      have hti : ω t = i := (Finset.mem_filter.mp ht).2
      have hpi : p i ≠ 0 := by rw [← hti]; exact (hω t).ne'
      have hh : p i / p i * phat ω i = phat ω i := by field_simp
      rw [hh]; simp
  have hterm : ∑ i, cCoef p h i * phat ω i - ∑ i, cCoef p h i * p i / tail p i * tail (phat ω) i
      = ∑ i, cCoef p h i * (phat ω i - p i / tail p i * tail (phat ω) i) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hbl : ∑ i ∈ belowLast S, (yRatio (phat ω) i - yRatio p i) * tail (phat ω) i * cCoef p h i
      = ∑ i, cCoef p h i * (phat ω i - p i / tail p i * tail (phat ω) i) := by
    rw [Finset.sum_congr rfl (fun i _ => hB i)]
    exact Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => hC i hi)
  refine ⟨?_, ?_, ?_⟩
  · -- Part 1
    have hZ : ∀ i, ∑ t, Zcoord p h i (ω t)
        = n * (cCoef p h i * phat ω i - cCoef p h i * p i / tail p i * tail (phat ω) i) := by
      intro i
      have : ∑ t, Zcoord p h i (ω t) = cCoef p h i *
          (∑ t, (if ω t = i then (1 : ℝ) else 0) - yRatio p i * ∑ t, (if i ≤ ω t then (1 : ℝ) else 0)) := by
        simp only [Zcoord, ← Finset.mul_sum, Finset.sum_sub_distrib]
      rw [this, h1, h2]
      unfold yRatio; ring
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun i _ => hZ i), ← Finset.mul_sum, Finset.sum_sub_distrib]
    field_simp
  · rw [hterm, hbl]
  · rw [hbl]
    have hphat1 : ∑ i, phat ω i = 1 := hph_sum
    exact core_fin p h (phat ω) hp.1 hp.2 hphat1
