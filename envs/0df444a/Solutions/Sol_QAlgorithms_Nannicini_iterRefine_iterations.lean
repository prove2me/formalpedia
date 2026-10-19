-- Prove2me | solution 1 for QAlgorithms.Nannicini.iterRefine_iterations
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T07:54:20.831062+00:00
-- url     : https://prove2.me/submissions/3d7580f3-9ca3-41d0-9343-6e86cf1a8d25

import Definitions.Def_QAlgorithms_Defs_BlockEncoding
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open QAlgorithms

private lemma residual_step {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ)
    (b x y : EuclideanSpace ℂ (Fin N)) (hr : 0 < ‖b - act A x‖) :
    ‖b - act A (x + (‖b - act A x‖ : ℂ) • y)‖ =
      ‖b - act A x‖ * ‖act A y - normalizedVec (b - act A x)‖ := by
  have ha : act A (x + (‖b - act A x‖ : ℂ) • y) =
      act A x + (‖b - act A x‖ : ℂ) • act A y := by
    ext i
    simp [act, Matrix.mulVec, dotProduct, Finset.sum_add_distrib, mul_add, mul_comm]
    simp only [← mul_assoc, Finset.sum_mul]
  have hn : (‖b - act A x‖ : ℂ) • normalizedVec (b - act A x) = b - act A x := by
    rw [normalizedVec, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hr.ne',
      Complex.ofReal_one, one_smul]
  have he : b - act A (x + (‖b - act A x‖ : ℂ) • y) =
      -(‖b - act A x‖ : ℂ) • (act A y - normalizedVec (b - act A x)) := by
    rw [ha, neg_smul, smul_sub, hn]
    abel
  rw [he, norm_smul]
  simp [Complex.norm_real]

private lemma geometric_budget (δ ε : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hε0 : 0 < ε) (hεδ : ε < δ) :
    ∃ M : ℕ, (M : ℝ) ≤ (2 / (-Real.log δ)) * Real.log (1 / ε) ∧ δ ^ M ≤ ε := by
  have hd : 0 < -Real.log δ := neg_pos.mpr (Real.log_neg hδ0 hδ1)
  have hl : Real.log (1 / ε) = -Real.log ε := by simp
  have hld : -Real.log δ < Real.log (1 / ε) := by
    rw [hl]
    exact neg_lt_neg ((Real.log_lt_log_iff hε0 hδ0).mpr hεδ)
  let q := Real.log (1 / ε) / (-Real.log δ)
  have hq : 1 < q := (lt_div_iff₀ hd).mpr (by simpa using hld)
  have heq : q * (-Real.log δ) = Real.log (1 / ε) := div_mul_cancel₀ _ hd.ne'
  let M := ⌈q⌉₊
  have hm : q ≤ (M : ℝ) := Nat.le_ceil q
  have hm' : (M : ℝ) < q + 1 := Nat.ceil_lt_add_one (by linarith : 0 ≤ q)
  refine ⟨M, ?_, ?_⟩
  · have h : (M : ℝ) ≤ 2 * q := by linarith
    calc
      (M : ℝ) ≤ 2 * q := h
      _ = (2 / (-Real.log δ)) * Real.log (1 / ε) := by dsimp [q]; ring
  · apply (Real.log_le_log_iff (pow_pos hδ0 M) hε0).mp
    rw [Real.log_pow]
    have := mul_le_mul_of_nonneg_right hm hd.le
    rw [heq, hl] at this
    nlinarith

theorem solution (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (b : EuclideanSpace ℂ (Fin N)), ‖b‖ = 1 →
        ∀ ε : ℝ, 0 < ε → ε < δ →
          ∀ xhat : ℕ → EuclideanSpace ℂ (Fin N),
            (∀ k : ℕ, (∀ j ≤ k, ε < ‖b - act A (iterRefineX A b xhat j)‖) →
              ‖act A (xhat (k + 1)) - normalizedVec (b - act A (iterRefineX A b xhat k))‖ ≤ δ) →
            ∃ K : ℕ, (K : ℝ) ≤ C * Real.log (1 / ε) ∧
              (∀ k < K, ε < ‖b - act A (iterRefineX A b xhat k)‖) ∧
              ‖act A (iterRefineX A b xhat K) - b‖ ≤ ε := by
  refine ⟨2 / (-Real.log δ), div_pos (by norm_num) (neg_pos.mpr (Real.log_neg hδ0 hδ1)), ?_⟩
  intro N A b hb ε hε0 hεδ xhat hsolver
  let r : ℕ → ℝ := fun k => ‖b - act A (iterRefineX A b xhat k)‖
  have decay (k : ℕ) : (∀ j < k, ε < r j) → r k ≤ δ ^ k := by
    induction k with
    | zero =>
      intro _
      simpa [r, iterRefineX, act] using hb.le
    | succ k ih =>
      intro h
      have hk : 0 < r k := hε0.trans (h k (Nat.lt_succ_self k))
      have hs := hsolver k (fun j hj => h j (Nat.lt_succ_of_le hj))
      have hi := ih (fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self k)))
      calc
        r (k + 1) = r k *
            ‖act A (xhat (k + 1)) - normalizedVec (b - act A (iterRefineX A b xhat k))‖ := by
          exact residual_step A b (iterRefineX A b xhat k) (xhat (k + 1)) hk
        _ ≤ r k * δ := mul_le_mul_of_nonneg_left hs hk.le
        _ ≤ δ ^ k * δ := mul_le_mul_of_nonneg_right hi hδ0.le
        _ = δ ^ (k + 1) := (pow_succ δ k).symm
  obtain ⟨M, hM, hpow⟩ := geometric_budget δ ε hδ0 hδ1 hε0 hεδ
  have hex : ∃ k, k ≤ M ∧ r k ≤ ε := by
    by_contra! h
    have hd := decay M (fun j hj => h j (Nat.le_of_lt hj))
    exact (not_lt_of_ge (hd.trans hpow)) (h M le_rfl)
  have hex' : ∃ k, r k ≤ ε := by obtain ⟨k, _, hk⟩ := hex; exact ⟨k, hk⟩
  let K := Nat.find hex'
  have hK : r K ≤ ε := Nat.find_spec hex'
  have hKM : K ≤ M := by
    obtain ⟨k, hkM, hk⟩ := hex
    exact (Nat.find_min' hex' hk).trans hkM
  refine ⟨K, (Nat.cast_le.mpr hKM).trans hM, ?_, ?_⟩
  · intro k hk
    exact lt_of_not_ge (Nat.find_min hex' hk)
  · simpa only [r, norm_sub_rev] using hK
