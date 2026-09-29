-- Prove2me | solution 1 for SparseApprox.Greedy.iterations_le_of_rho
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:24:25.213838+00:00
-- url     : https://prove2.me/submissions/319b57da-0cd7-4580-9c97-fa536e0b1e6d

import Mathlib
import Definitions.Def_SparseApprox_Greedy_Basic
import Definitions.Def_SparseApprox_Greedy_Algorithm

open scoped InnerProductSpace

namespace SparseApprox.Greedy

lemma aux_itr_normalize {m : ℕ} (v : EuclideanSpace ℝ (Fin m)) :
    normalizeVec v = 0 ∨ ‖normalizeVec v‖ = 1 := by
  by_cases hv : v = 0
  · left; simp [normalizeVec, hv]
  · right
    unfold normalizeVec
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

def aux_itr_Inv {m n : ℕ} (s : State m n) : Prop :=
  (∀ j, s.col j = 0 ∨ ‖s.col j‖ = 1) ∧
  (∀ i ∈ s.chosen, ⟪s.col i, s.res⟫_ℝ = 0) ∧
  (∀ i ∈ s.chosen, ∀ j ∉ s.chosen, ⟪s.col i, s.col j⟫_ℝ = 0)

lemma aux_itr_Inv_init {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) : aux_itr_Inv (initState A b) := by
  refine ⟨fun j => aux_itr_normalize _, ?_, ?_⟩ <;> simp [initState]

lemma aux_itr_unit {m n : ℕ} (s : State m n) (hs : aux_itr_Inv s) (k : Fin n)
    (hk : ⟪s.col k, s.res⟫_ℝ ≠ 0) : ⟪s.col k, s.col k⟫_ℝ = 1 := by
  rcases hs.1 k with h | h
  · exact absurd (by simp [h]) hk
  · rw [real_inner_self_eq_norm_sq, h]; norm_num

lemma aux_itr_step {m n : ℕ} (s : State m n) (hs : aux_itr_Inv s) (k : Fin n)
    (hkc : k ∉ s.chosen) (hk : ⟪s.col k, s.res⟫_ℝ ≠ 0) :
    aux_itr_Inv (greedyStep s k) ∧
      ‖(greedyStep s k).res‖ ^ 2 = ‖s.res‖ ^ 2 - ⟪s.col k, s.res⟫_ℝ ^ 2 := by
  have hu := aux_itr_unit s hs k hk
  obtain ⟨h1, h2, h3⟩ := hs
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro j
    simp only [greedyStep]
    split_ifs
    · exact h1 j
    · exact aux_itr_normalize _
  · intro i hi
    simp only [greedyStep] at hi ⊢
    rw [if_pos hi]
    rw [inner_sub_right, real_inner_smul_right]
    rcases Finset.mem_insert.mp hi with rfl | hi'
    · rw [hu]; ring
    · rw [h2 i hi', h3 i hi' k hkc]; ring
  · intro i hi j hj
    simp only [greedyStep] at hi hj ⊢
    rw [if_pos hi, if_neg hj]
    unfold normalizeVec
    rw [real_inner_smul_right, inner_sub_right, real_inner_smul_right]
    have hj' : j ∉ s.chosen := fun h => hj (Finset.mem_insert_of_mem h)
    rcases Finset.mem_insert.mp hi with rfl | hi'
    · rw [hu]; ring
    · rw [h3 i hi' j hj', h3 i hi' k hkc]; ring
  · simp only [greedyStep]
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right, hu]
    rw [real_inner_comm s.res (s.col k)]
    ring

lemma aux_itr_key {m n : ℕ} (s : State m n) (hs : aux_itr_Inv s) (kr : Fin n) (ε : ℝ)
    (hε : 0 < ε) (hres : ε < ‖s.res‖)
    (hmax : ∀ j ∉ s.chosen, |⟪s.col j, s.res⟫_ℝ| ≤ |⟪s.col kr, s.res⟫_ℝ|)
    (u : EuclideanSpace ℝ (Fin n)) (hu : ‖(∑ i, u i • s.col i) - s.res‖ ≤ ε / 2)
    (ρ : ℝ) (hρ : 4 * (nnz u : ℝ) * ‖u‖ ^ 2 ≤ ρ * ‖s.res‖ ^ 2) :
    ‖s.res‖ ^ 2 ≤ ρ * ⟪s.col kr, s.res⟫_ℝ ^ 2 := by
  set M := |⟪s.col kr, s.res⟫_ℝ| with hM
  set y := ∑ i, u i • s.col i with hy
  have hbpos : 0 < ‖s.res‖ := hε.trans hres
  have hlow : ‖s.res‖ ^ 2 / 2 ≤ ⟪y, s.res⟫_ℝ := by
    have h1 : ⟪y, s.res⟫_ℝ = ‖s.res‖ ^ 2 + ⟪y - s.res, s.res⟫_ℝ := by
      rw [inner_sub_left, real_inner_self_eq_norm_sq]; ring
    have h2 : |⟪y - s.res, s.res⟫_ℝ| ≤ ‖y - s.res‖ * ‖s.res‖ := abs_real_inner_le_norm _ _
    have h3 : ‖y - s.res‖ * ‖s.res‖ ≤ ε / 2 * ‖s.res‖ :=
      mul_le_mul_of_nonneg_right hu hbpos.le
    have h4 := neg_abs_le ⟪y - s.res, s.res⟫_ℝ
    nlinarith
  have hup : ⟪y, s.res⟫_ℝ ≤ M * ∑ i, |u i| := by
    rw [hy, sum_inner, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [real_inner_smul_left]
    have : |⟪s.col i, s.res⟫_ℝ| ≤ M := by
      by_cases hi : i ∈ s.chosen
      · rw [hs.2.1 i hi, abs_zero]; exact abs_nonneg _
      · exact hmax i hi
    calc u i * ⟪s.col i, s.res⟫_ℝ ≤ |u i * ⟪s.col i, s.res⟫_ℝ| := le_abs_self _
      _ = |u i| * |⟪s.col i, s.res⟫_ℝ| := abs_mul _ _
      _ ≤ |u i| * M := mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = M * |u i| := mul_comm _ _
  have hcs : (∑ i, |u i|) ^ 2 ≤ (nnz u : ℝ) * ‖u‖ ^ 2 := by
    have e1 : ∑ i, |u i| = ∑ i ∈ nzSet u, |u i| := by
      unfold nzSet
      rw [Finset.sum_filter_of_ne]
      intro x _ hx h
      exact hx (by simp [h])
    have e2 : ‖u‖ ^ 2 = ∑ i ∈ nzSet u, |u i| ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      unfold nzSet
      rw [Finset.sum_filter_of_ne]
      · simp
      · intro x _ hx h
        exact hx (by simp [h])
    rw [e1, e2, nnz]
    exact sq_sum_le_card_mul_sum_sq
  have hMsq : M ^ 2 = ⟪s.col kr, s.res⟫_ℝ ^ 2 := sq_abs _
  have key : (‖s.res‖ ^ 2 / 2) ^ 2 ≤ M ^ 2 * ((nnz u : ℝ) * ‖u‖ ^ 2) := by
    have h0 : 0 ≤ ‖s.res‖ ^ 2 / 2 := by positivity
    calc (‖s.res‖ ^ 2 / 2) ^ 2 ≤ (M * ∑ i, |u i|) ^ 2 :=
          pow_le_pow_left₀ h0 (hlow.trans hup) 2
      _ = M ^ 2 * (∑ i, |u i|) ^ 2 := by ring
      _ ≤ M ^ 2 * ((nnz u : ℝ) * ‖u‖ ^ 2) := mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
  have h5 : M ^ 2 * (4 * (nnz u : ℝ) * ‖u‖ ^ 2) ≤ M ^ 2 * (ρ * ‖s.res‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hρ (sq_nonneg _)
  have hb2 : 0 < ‖s.res‖ ^ 2 := by positivity
  rw [← hMsq]
  have h6 : ‖s.res‖ ^ 2 * ‖s.res‖ ^ 2 ≤ (ρ * M ^ 2) * ‖s.res‖ ^ 2 := by nlinarith
  exact le_of_mul_le_mul_right h6 hb2

end SparseApprox.Greedy

open SparseApprox.Greedy

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (ε : ℝ) (hε : 0 < ε) (k : ℕ → Fin n) (t : ℕ)
    (hrun : IsGreedyRun A b ε k t) (u : ℕ → EuclideanSpace ℝ (Fin n))
    (hu : ∀ r < t,
      IsMinSparseSol (greedyState A b k r).col (greedyState A b k r).res (ε / 2) (u r))
    (ρ : ℝ)
    (hρ : ∀ r < t, 4 * (nnz (u r) : ℝ) * ‖u r‖ ^ 2 ≤ ρ * ‖(greedyState A b k r).res‖ ^ 2) :
    t ≤ ⌈2 * ρ * Real.log (‖b‖ / ε)⌉₊ := by
  have hinv : ∀ r ≤ t, aux_itr_Inv (greedyState A b k r) := by
    intro r
    induction r with
    | zero => intro _; exact aux_itr_Inv_init A b
    | succ r ih =>
      intro hr
      have hrt : r < t := hr
      obtain ⟨_, hkc, hk, _⟩ := hrun r hrt
      exact (aux_itr_step _ (ih hrt.le) (k r) hkc hk).1
  have hstep : ∀ r < t, ‖(greedyState A b k (r + 1)).res‖ ^ 2 =
      ‖(greedyState A b k r).res‖ ^ 2 -
        ⟪(greedyState A b k r).col (k r), (greedyState A b k r).res⟫_ℝ ^ 2 := by
    intro r hr
    obtain ⟨_, hkc, hk, _⟩ := hrun r hr
    exact (aux_itr_step _ (hinv r hr.le) (k r) hkc hk).2
  have hkey : ∀ r < t, ‖(greedyState A b k r).res‖ ^ 2 ≤
      ρ * ⟪(greedyState A b k r).col (k r), (greedyState A b k r).res⟫_ℝ ^ 2 := by
    intro r hr
    obtain ⟨hres, _, _, hmax⟩ := hrun r hr
    exact aux_itr_key _ (hinv r hr.le) (k r) ε hε hres hmax (u r) (hu r hr).1 ρ (hρ r hr)
  cases t with
  | zero => exact Nat.zero_le _
  | succ s =>
    have hb : (greedyState A b k 0).res = b := rfl
    have hbε : ε < ‖b‖ := by rw [← hb]; exact (hrun 0 (Nat.succ_pos _)).1
    have hbpos : 0 < ‖b‖ := hε.trans hbε
    have hρpos : 0 < ρ := by
      have h := hkey 0 (Nat.succ_pos _)
      rw [hb] at h
      have hb2 : 0 < ‖b‖ ^ 2 := by positivity
      by_contra hneg'
      have hneg := not_lt.mp hneg'
      have : ρ * ⟪(greedyState A b k 0).col (k 0), b⟫_ℝ ^ 2 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hneg (sq_nonneg _)
      linarith
    have hdecay : ∀ r ≤ s, ‖(greedyState A b k r).res‖ ^ 2 ≤
        Real.exp (-(r : ℝ) / ρ) * ‖b‖ ^ 2 := by
      intro r
      induction r with
      | zero => intro _; simp [hb]
      | succ r ih =>
        intro hr
        have hrt : r < s + 1 := by omega
        have h1 := hstep r hrt
        have h2 := hkey r hrt
        have h3 := ih (by omega)
        set B := ‖(greedyState A b k r).res‖ ^ 2 with hB
        set α := ⟪(greedyState A b k r).col (k r), (greedyState A b k r).res⟫_ℝ with hα
        have hB0 : 0 ≤ B := sq_nonneg _
        have h4 : ‖(greedyState A b k (r + 1)).res‖ ^ 2 ≤ (1 - 1 / ρ) * B := by
          rw [h1]
          have : B / ρ ≤ α ^ 2 := by rw [div_le_iff₀ hρpos]; linarith
          have e : (1 - 1 / ρ) * B = B - B / ρ := by field_simp
          rw [e]; linarith
        have h5 : 1 - 1 / ρ ≤ Real.exp (-1 / ρ) := by
          have := Real.add_one_le_exp (-1 / ρ)
          have e : -1 / ρ + 1 = 1 - 1 / ρ := by ring
          linarith
        have hexp : Real.exp (-((r + 1 : ℕ) : ℝ) / ρ) =
            Real.exp (-1 / ρ) * Real.exp (-(r : ℝ) / ρ) := by
          rw [← Real.exp_add]; congr 1; push_cast; ring
        calc ‖(greedyState A b k (r + 1)).res‖ ^ 2 ≤ (1 - 1 / ρ) * B := h4
          _ ≤ Real.exp (-1 / ρ) * B := mul_le_mul_of_nonneg_right h5 hB0
          _ ≤ Real.exp (-1 / ρ) * (Real.exp (-(r : ℝ) / ρ) * ‖b‖ ^ 2) :=
              mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
          _ = Real.exp (-((r + 1 : ℕ) : ℝ) / ρ) * ‖b‖ ^ 2 := by rw [hexp]; ring
    have hlast := hdecay s le_rfl
    have hεs := (hrun s (Nat.lt_succ_self s)).1
    have hε2 : ε ^ 2 < Real.exp (-(s : ℝ) / ρ) * ‖b‖ ^ 2 := by
      have : ε ^ 2 < ‖(greedyState A b k s).res‖ ^ 2 :=
        pow_lt_pow_left₀ hεs hε.le (by norm_num)
      linarith
    have hx : (s : ℝ) / ρ < 2 * Real.log (‖b‖ / ε) := by
      have e : Real.log ((‖b‖ / ε) ^ 2) = 2 * Real.log (‖b‖ / ε) := by
        rw [Real.log_pow]; norm_num
      rw [← e, Real.lt_log_iff_exp_lt (by positivity), div_pow,
        lt_div_iff₀ (by positivity)]
      have e2 : Real.exp ((s : ℝ) / ρ) * Real.exp (-(s : ℝ) / ρ) = 1 := by
        rw [← Real.exp_add]; rw [show (s : ℝ) / ρ + -(s : ℝ) / ρ = 0 by ring]; simp
      calc Real.exp ((s : ℝ) / ρ) * ε ^ 2
          < Real.exp ((s : ℝ) / ρ) * (Real.exp (-(s : ℝ) / ρ) * ‖b‖ ^ 2) :=
            mul_lt_mul_of_pos_left hε2 (Real.exp_pos _)
        _ = ‖b‖ ^ 2 := by rw [← mul_assoc, e2, one_mul]
    have hs : (s : ℝ) < 2 * ρ * Real.log (‖b‖ / ε) := by
      rw [div_lt_iff₀ hρpos] at hx; linarith
    exact Nat.lt_ceil.mpr hs
