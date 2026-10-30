-- Prove2me | solution 1 for StaggeredRollout.TOpt.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T17:08:29.727378+00:00
-- url     : https://prove2.me/submissions/d85bde7a-aabd-45f2-aff0-027688dc8bf2

import Mathlib
import Definitions.Def_StaggeredRollout_TOpt_Setting
import Definitions.Def_StaggeredRollout_TOpt_Quadratic
import Theorems.Thm_StaggeredRollout_TOpt_lemma_EC_1_2
import Theorems.Thm_StaggeredRollout_TOpt_omega_star_minimizes_f1
import Theorems.Thm_StaggeredRollout_TOpt_covariate_terms

open Matrix StaggeredRollout.TOpt

/-- Cohort balance + centring makes `Vᵀ z_t` constant in `t`. -/
private lemma balanced_const {N T d : ℕ} (V : Matrix (Fin N) (Fin d) ℝ)
    (hc : ∀ k, ∑ i, V i k = 0) (A : Fin N → WithTop (Fin T))
    (hbal : ∀ t : Fin T, 1 ≤ t.val → ∀ k : Fin d,
      ∑ i ∈ Finset.univ.filter (fun i => A i = (t : WithTop (Fin T))), V i k = 0) :
    ∃ μ : Fin d → ℝ, ∀ t, Vᵀ *ᵥ (fun i => z A i t) = μ := by
  -- S t k = ∑_{A i ≤ t} V i k
  set S : Fin T → Fin d → ℝ := fun t k =>
    ∑ i, (if A i ≤ (t : WithTop (Fin T)) then V i k else 0) with hS
  have hz : ∀ t, Vᵀ *ᵥ (fun i => z A i t) = fun k => 2 * S t k := by
    intro t; funext k
    simp only [mulVec, dotProduct, transpose_apply, hS, Finset.mul_sum]
    have : ∀ i, V i k * z A i t
        = 2 * (if A i ≤ (t : WithTop (Fin T)) then V i k else 0) - V i k := by
      intro i; unfold z; split_ifs <;> ring
    simp only [this, Finset.sum_sub_distrib, hc k, sub_zero]
  have hstep : ∀ (n : ℕ) (hn : n + 1 < T), S ⟨n + 1, hn⟩ = S ⟨n, by omega⟩ := by
    intro n hn; funext k
    have h0 := hbal ⟨n + 1, hn⟩ (by simp) k
    rw [Finset.sum_filter] at h0
    simp only [hS]
    have : ∀ i, (if A i ≤ ((⟨n + 1, hn⟩ : Fin T) : WithTop (Fin T)) then V i k else 0)
        = (if A i ≤ ((⟨n, by omega⟩ : Fin T) : WithTop (Fin T)) then V i k else 0)
          + (if A i = ((⟨n + 1, hn⟩ : Fin T) : WithTop (Fin T)) then V i k else 0) := by
      intro i
      cases h : A i with
      | top => simp
      | coe s =>
        simp only [WithTop.coe_le_coe, WithTop.coe_eq_coe, Fin.le_def, Fin.ext_iff]
        by_cases h1 : s.val ≤ n
        · have : s.val ≠ n + 1 := by omega
          simp [h1, this, show s.val ≤ n + 1 by omega]
        · by_cases h2 : s.val = n + 1
          · simp [h1, h2]
          · simp [h1, h2, show ¬ s.val ≤ n + 1 by omega]
    simp only [this, Finset.sum_add_distrib, h0, add_zero]
  have hall : ∀ (n : ℕ) (hn : n < T), S ⟨n, hn⟩ = S ⟨0, by omega⟩ := by
    intro n
    induction n with
    | zero => intro hn; rfl
    | succ m ih => intro hn; rw [hstep m hn, ih]
  by_cases hT : 0 < T
  · refine ⟨fun k => 2 * S ⟨0, hT⟩ k, fun t => ?_⟩
    rw [hz t]
    have := hall t.val t.isLt
    simp only [Fin.eta] at this
    rw [this]
  · exact ⟨0, fun t => absurd t.isLt (by omega)⟩

theorem solution (N T ℓ dx du : ℕ) (sig2 : ℝ) (hsig : 0 < sig2)
    (X : Matrix (Fin N) (Fin dx) ℝ) (U : Matrix (Fin N) (Fin du) ℝ)
    (Sv : Matrix (Fin du) (Fin du) ℝ)
    (hXc : ∀ k, ∑ i, X i k = 0) (hUc : ∀ k, ∑ i, U i k = 0) (hXU : Xᵀ * U = 0)
    (hSv : Sv = sig2 • (1 : Matrix (Fin du) (Fin du) ℝ))
    (hT : 0 < ℓ → ((ℓ : ℝ) ^ 3 + 13 * (ℓ : ℝ) ^ 2 + 7 * (ℓ : ℝ) + 3) / (8 * (ℓ : ℝ)) < (T : ℝ))
    (A : Fin N → WithTop (Fin T)) (hA : A ∈ Aell ℓ ∩ AX X ∩ AU U) :
    ∀ A' : Fin N → WithTop (Fin T), traceT ℓ sig2 X U Sv A' ≤ traceT ℓ sig2 X U Sv A := by
  intro A'
  rcases hA with ⟨⟨hAl, hAX⟩, hAU⟩
  rw [lemma_EC_1_2 N T ℓ dx du sig2 hsig X U Sv hXc hUc hXU hSv A',
    lemma_EC_1_2 N T ℓ dx du sig2 hsig X U Sv hXc hUc hXU hSv A]
  obtain ⟨-, -, hmin⟩ := omega_star_minimizes_f1 ℓ T hT
  obtain ⟨hX0', hU0', -, -⟩ := covariate_terms N T ℓ dx du X U (z A')
  obtain ⟨-, -, hXz, hUz⟩ := covariate_terms N T ℓ dx du X U (z A)
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hNne : (N : ℝ) ≠ 0 := hNr.ne'
  -- the treated fractions of `A` are `ω*`
  have hom : omegaBar (z A) = omegaStar ℓ T := by
    funext t
    have h1 := hAl t
    have : ∀ i, z A i t = 2 * (if A i ≤ (t : WithTop (Fin T)) then (1 : ℝ) else 0) - 1 := by
      intro i; unfold z; split_ifs <;> norm_num
    simp only [omegaBar, this, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h1 ⊢
    field_simp at h1 ⊢
    linarith
  -- the fractions of any design are nondecreasing and in `[-1, 1]`
  have hzle : ∀ i (t : Fin T), -1 ≤ z A' i t ∧ z A' i t ≤ 1 := by
    intro i t; unfold z; split_ifs <;> norm_num
  have hmono : Monotone (omegaBar (z A')) := by
    intro t t' htt
    unfold omegaBar
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hNr.le)
    apply Finset.sum_le_sum
    intro i _
    unfold z
    by_cases h : A' i ≤ (t : WithTop (Fin T))
    · have h' : A' i ≤ (t' : WithTop (Fin T)) := le_trans h (WithTop.coe_le_coe.mpr htt)
      simp [h, h']
    · split_ifs <;> norm_num
  have hbd : ∀ t, -1 ≤ omegaBar (z A') t ∧ omegaBar (z A') t ≤ 1 := by
    intro t
    unfold omegaBar
    have hlo : -(N : ℝ) ≤ ∑ i, z A' i t := by
      have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (hzle i t).1)
      simpa using this
    have hhi : ∑ i, z A' i t ≤ (N : ℝ) := by
      have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (hzle i t).2)
      simpa using this
    constructor
    · rw [le_inv_mul_iff₀ hNr]; linarith
    · rw [inv_mul_le_iff₀ hNr]; linarith
  -- covariate balance kills the covariate terms of `A`
  have hXA : ∀ j, fXj ℓ X (z A) j = 0 := by
    apply hXz
    apply balanced_const X hXc A
    intro t ht k
    have := hAX t ht k
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (inv_ne_zero hNne)
    · exact h
  have hUA : ∀ j, fUj ℓ U (z A) j = 0 := by
    apply hUz
    apply balanced_const U hUc A
    intro t ht k
    have := hAU t ht k
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (inv_ne_zero hNne)
    · exact h
  have hf : f1 ℓ T (omegaStar ℓ T) ≤ f1 ℓ T (omegaBar (z A')) := hmin _ hmono hbd
  unfold f1 at hf
  have hsum : ∑ j : Fin (ℓ + 1), (f1j ℓ T (omegaBar (z A)) j + fXj ℓ X (z A) j + fUj ℓ U (z A) j)
      ≤ ∑ j : Fin (ℓ + 1),
          (f1j ℓ T (omegaBar (z A')) j + fXj ℓ X (z A') j + fUj ℓ U (z A') j) := by
    simp only [hXA, hUA, add_zero, Finset.sum_add_distrib, hom]
    have := Finset.sum_nonneg (fun j (_ : j ∈ (Finset.univ : Finset (Fin (ℓ + 1)))) => hX0' j)
    have := Finset.sum_nonneg (fun j (_ : j ∈ (Finset.univ : Finset (Fin (ℓ + 1)))) => hU0' j)
    linarith
  have hc : -((N : ℝ) / sig2) ≤ 0 := by
    have := div_pos hNr hsig; linarith
  exact mul_le_mul_of_nonpos_left hsum hc
