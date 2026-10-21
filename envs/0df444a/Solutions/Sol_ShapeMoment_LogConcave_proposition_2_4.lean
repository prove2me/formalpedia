-- Prove2me | solution 1 for ShapeMoment.LogConcave.proposition_2_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:01:38.205982+00:00
-- url     : https://prove2.me/submissions/c91b1351-efa6-453d-9451-4a3cafaedda7

import Mathlib
import Definitions.Def_ShapeMoment_LogConcave_Model

set_option autoImplicit false
open ShapeMoment.LogConcave

lemma sm_ext_val {n : ℕ} (x : Fin n → ℝ) (j : Fin n) : ext x (j.val + 1) = x j := by
  unfold ext
  rw [dif_pos ⟨by omega, by omega⟩]
  simp

lemma sm_ext_out {n : ℕ} (x : Fin n → ℝ) (i : ℕ) (h : ¬ (1 ≤ i ∧ i ≤ n)) : ext x i = 0 := by
  unfold ext
  rw [dif_neg h]

lemma sm_ext_zero_of_out {n : ℕ} (x : Fin n → ℝ) (k ℓ : ℕ) (hk : 1 ≤ k) (hle : ℓ ≤ n)
    (hzero : ∀ j : Fin n, ¬ (k ≤ j.val + 1 ∧ j.val + 1 ≤ ℓ) → x j = 0) (i : ℕ)
    (hi : ¬ (k ≤ i ∧ i ≤ ℓ)) : ext x i = 0 := by
  by_cases h : 1 ≤ i ∧ i ≤ n
  · have := hzero ⟨i - 1, by omega⟩ (by simp only; omega)
    unfold ext
    rw [dif_pos h]; exact this
  · exact sm_ext_out x i h

/-- ratio monotonicity for a log-concave positive sequence on `[k,ℓ]` -/
lemma sm_ratio_anti (a : ℕ → ℝ) (k ℓ : ℕ) (hpos : ∀ j, k ≤ j → j ≤ ℓ → 0 < a j)
    (hlc : ∀ j, k < j → j < ℓ → a (j - 1) * a (j + 1) ≤ a j ^ 2) :
    ∀ d i, k ≤ i → i + d + 1 ≤ ℓ → a (i + d + 1) / a (i + d) ≤ a (i + 1) / a i := by
  intro d
  induction d with
  | zero => intro i _ _; simp
  | succ d ih =>
    intro i hi hil
    have h1 := ih i hi (by omega)
    have hj := hlc (i + d + 1) (by omega) (by omega)
    have e : i + d + 1 - 1 = i + d := by omega
    rw [e] at hj
    have p1 := hpos (i + d) (by omega) (by omega)
    have p2 := hpos (i + d + 1) (by omega) (by omega)
    have p3 := hpos (i + d + 1 + 1) (by omega) (by omega)
    refine le_trans ?_ h1
    rw [show i + (d + 1) + 1 = i + d + 1 + 1 by omega, show i + (d + 1) = i + d + 1 by omega]
    rw [div_le_div_iff₀ p2 p1]
    nlinarith

lemma sm_lc_to_prime (a : ℕ → ℝ) (k ℓ : ℕ) (hpos : ∀ j, k ≤ j → j ≤ ℓ → 0 < a j)
    (hlc : ∀ j, k < j → j < ℓ → a (j - 1) * a (j + 1) ≤ a j ^ 2)
    (j u v : ℕ) (hu : 1 ≤ u) (hv : 1 ≤ v) (h1 : k ≤ j - u) (hu' : u ≤ j - 1) (h2 : j + v ≤ ℓ) :
    a (j - u) ^ v * a (j + v) ^ u ≤ a j ^ (u + v) := by
  have hanti := sm_ratio_anti a k ℓ hpos hlc
  have hrho : ∀ s i, k ≤ s → s ≤ i → i + 1 ≤ ℓ → a (i + 1) / a i ≤ a (s + 1) / a s := by
    intro s i hs hsi hi
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hsi
    exact hanti d s hs (by omega)
  obtain ⟨i0, hi0⟩ : ∃ i0, j = i0 + 1 := ⟨j - 1, by omega⟩
  have hk0 : k ≤ i0 := by omega
  set r := a (i0 + 1) / a i0 with hr
  have pj := hpos j (by omega) (by omega)
  have pi0 := hpos i0 hk0 (by omega)
  have hrpos : 0 < r := div_pos (hi0 ▸ pj) pi0
  have step : ∀ s, k ≤ s → s ≤ i0 → a s * r ≤ a (s + 1) := by
    intro s hs hsi
    have h := hrho s i0 hs hsi (by omega)
    have ps := hpos s hs (by omega)
    rw [← hr] at h
    have := (le_div_iff₀ ps).1 h
    linarith
  have low : ∀ t s, k ≤ s → s + t = j → a s * r ^ t ≤ a j := by
    intro t
    induction t with
    | zero => intro s _ hs; simp at hs; subst hs; simp
    | succ t ih =>
      intro s hs hst
      have h1 := ih (s + 1) (by omega) (by omega)
      have h2 := step s hs (by omega)
      have ps := hpos s hs (by omega)
      calc a s * r ^ (t + 1) = (a s * r) * r ^ t := by ring
        _ ≤ a (s + 1) * r ^ t := mul_le_mul_of_nonneg_right h2 (by positivity)
        _ ≤ a j := h1
  have up : ∀ t, j + t ≤ ℓ → a (j + t) ≤ r ^ t * a j := by
    intro t
    induction t with
    | zero => intro _; simp
    | succ t ih =>
      intro ht
      have h1 := ih (by omega)
      have h := hrho i0 (j + t) hk0 (by omega) (by omega)
      rw [← hr] at h
      have pjt := hpos (j + t) (by omega) (by omega)
      have := (div_le_iff₀ pjt).1 h
      have e : j + (t + 1) = j + t + 1 := by omega
      rw [e]
      have e2 : j + t = j + t := rfl
      calc a (j + t + 1) ≤ a (j + t) * r := by
            have h3 : a (j + t + 1) / a (j + t) ≤ r := h
            rw [div_le_iff₀ pjt] at h3; linarith
        _ ≤ (r ^ t * a j) * r := mul_le_mul_of_nonneg_right h1 hrpos.le
        _ = r ^ (t + 1) * a j := by ring
  have hA := low u (j - u) h1 (by omega)
  have hB := up v h2
  have pA := hpos (j - u) h1 (by omega)
  have pB := hpos (j + v) (by omega) (by omega)
  have e1 : (a (j - u) * r ^ u) ^ v ≤ a j ^ v := pow_le_pow_left₀ (by positivity) hA v
  have e2 : a (j + v) ^ u ≤ (r ^ v * a j) ^ u := pow_le_pow_left₀ pB.le hB u
  have hrr : 0 < r ^ (u * v) := by positivity
  apply le_of_mul_le_mul_left _ hrr
  calc r ^ (u * v) * (a (j - u) ^ v * a (j + v) ^ u)
      = (a (j - u) * r ^ u) ^ v * a (j + v) ^ u := by rw [mul_pow, ← pow_mul]; ring
    _ ≤ a j ^ v * (r ^ v * a j) ^ u :=
        mul_le_mul e1 e2 (by positivity) (by positivity)
    _ = r ^ (u * v) * a j ^ (u + v) := by rw [mul_pow, ← pow_mul, pow_add]; ring

theorem solution (n m : ℕ) (q : ℕ → ℝ) (hq0 : q 0 = 1) :
    feasLC n m q = feasLCPrime n m q := by
  ext x
  constructor
  · rintro ⟨k, ℓ, hk, hkl, hln, hmom, hlc, hpos, hzero⟩
    refine ⟨hmom, ?_, ?_⟩
    · intro j u v hj1 hjn hu hu' hv hv'
      have hz := sm_ext_zero_of_out x k ℓ hk hln hzero
      by_cases hin : k ≤ j - u ∧ j + v ≤ ℓ
      · exact sm_lc_to_prime (ext x) k ℓ hpos hlc j u v hu hv hin.1 hu' hin.2
      · have hnn : 0 ≤ ext x j ^ (u + v) := by
          by_cases hj : k ≤ j ∧ j ≤ ℓ
          · exact (pow_pos (hpos j hj.1 hj.2) _).le
          · rw [hz j hj]; simp
        rcases not_and_or.1 hin with h | h
        · rw [hz (j - u) (by omega), zero_pow (by omega), zero_mul]; exact hnn
        · rw [hz (j + v) (by omega), zero_pow (by omega), mul_zero]; exact hnn
    · intro j
      rw [← sm_ext_val x j]
      by_cases hj : k ≤ j.val + 1 ∧ j.val + 1 ≤ ℓ
      · exact (hpos _ hj.1 hj.2).le
      · rw [sm_ext_zero_of_out x k ℓ hk hln hzero _ hj]
  · rintro ⟨hmom, hcon, hnn⟩
    have hsum : ∑ j, x j = 1 := by
      have := hmom 0 (Nat.zero_le _)
      simp only [moment, pow_zero, one_mul, hq0] at this
      exact this
    have hex : ∃ j, 0 < x j := by
      by_contra hno
      push_neg at hno
      have : ∑ j, x j ≤ 0 := Finset.sum_nonpos (fun j _ => hno j)
      linarith
    classical
    set S : Finset ℕ := (Finset.univ.filter (fun j : Fin n => 0 < x j)).image (fun j => j.val + 1) with hS
    have hmemS : ∀ i, i ∈ S ↔ ∃ j : Fin n, 0 < x j ∧ j.val + 1 = i := by
      intro i; simp [hS]
    have hSne : S.Nonempty := by
      obtain ⟨j, hj⟩ := hex
      exact ⟨j.val + 1, (hmemS _).2 ⟨j, hj, rfl⟩⟩
    set k := S.min' hSne with hk
    set ℓ := S.max' hSne with hℓ
    have hkS : k ∈ S := Finset.min'_mem S hSne
    have hℓS : ℓ ∈ S := Finset.max'_mem S hSne
    have hkl : k ≤ ℓ := Finset.min'_le S _ hℓS
    obtain ⟨jk, hjk, hjk'⟩ := (hmemS k).1 hkS
    obtain ⟨jl, hjl, hjl'⟩ := (hmemS ℓ).1 hℓS
    have hk1 : 1 ≤ k := by omega
    have hln : ℓ ≤ n := by have := jl.2; omega
    have extk : 0 < ext x k := by rw [← hjk', sm_ext_val]; exact hjk
    have extl : 0 < ext x ℓ := by rw [← hjl', sm_ext_val]; exact hjl
    have extnn : ∀ i, 0 ≤ ext x i := by
      intro i
      unfold ext
      split_ifs
      · exact hnn _
      · exact le_rfl
    have hposs : ∀ i, k ≤ i → i ≤ ℓ → 0 < ext x i := by
      intro i hi1 hi2
      rcases hi1.eq_or_lt with h | h
      · rw [← h]; exact extk
      rcases hi2.eq_or_lt with h' | h'
      · rw [h']; exact extl
      by_contra hneg
      have hz : ext x i = 0 := le_antisymm (not_lt.1 hneg) (extnn i)
      have := hcon i (i - k) (ℓ - i) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      rw [hz, zero_pow (by omega)] at this
      have e1 : i - (i - k) = k := by omega
      have e2 : i + (ℓ - i) = ℓ := by omega
      rw [e1, e2] at this
      have : 0 < ext x k ^ (ℓ - i) * ext x ℓ ^ (i - k) := by positivity
      linarith
    refine ⟨k, ℓ, hk1, hkl, hln, hmom, ?_, hposs, ?_⟩
    · intro j hj1 hj2
      have := hcon j 1 1 (by omega) (by omega) le_rfl (by omega) le_rfl (by omega)
      simpa using this
    · intro j hj
      by_contra hne
      have hpj : 0 < x j := lt_of_le_of_ne (hnn j) (Ne.symm hne)
      have hm : j.val + 1 ∈ S := (hmemS _).2 ⟨j, hpj, rfl⟩
      exact hj ⟨Finset.min'_le S _ hm, Finset.le_max' S _ hm⟩
