-- Prove2me | solution 1 for QuantumLinSys.Chebyshev.lemma_14
-- status  : ACCEPTED   (prove)
-- author  : @elem
-- created : 2026-10-09T22:08:02.606396+00:00
-- url     : https://prove2.me/submissions/a253ea69-70ad-4a45-9734-48112ad10976

import Mathlib
import Definitions.Def_QuantumLinSys_Chebyshev_Setting
import Theorems.Thm_QuantumLinSys_Chebyshev_lemma_17
import Theorems.Thm_QuantumLinSys_Chebyshev_lemma_19

open QuantumLinSys.Chebyshev

theorem solution (κ ε : ℝ) (hκ : 1 ≤ κ) (hε : 0 < ε) :
    ∀ x ∈ Dκ κ, |chebSum (bOf κ ε) (j0Of (bOf κ ε) ε + 1) x - 1 / x| ≤ 2 * ε := by
  intro x hx
  have hκpos : 0 < κ := by linarith
  have hx' : x ∈ Set.Icc (-1 : ℝ) 1 := by
    have hinv : 1 / κ ≤ 1 := by rw [div_le_one hκpos]; exact hκ
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨h1, ?_⟩
      have : -1 / κ ≤ 0 := by rw [neg_div]; linarith [one_div_pos.mpr hκpos]
      linarith
    · refine ⟨?_, h2⟩
      linarith [one_div_pos.mpr hκpos]
  have h19 := lemma_19 (bOf κ ε) ε hε x hx'
  have hb : (κ * ((1 : ℕ) : ℝ)) ^ 2 * Real.log (κ * ((1 : ℕ) : ℝ) / ε) ≤ (bOf κ ε : ℝ) := by
    simp only [Nat.cast_one, mul_one]
    exact Nat.le_ceil _
  have hx'' : x ∈ Dκ (κ * ((1 : ℕ) : ℝ)) := by simpa using hx
  have h17 := lemma_17 κ ε 1 (bOf κ ε) hκ le_rfl hε hb x hx''
  calc |chebSum (bOf κ ε) (j0Of (bOf κ ε) ε + 1) x - 1 / x|
      = |(chebSum (bOf κ ε) (j0Of (bOf κ ε) ε + 1) x - fTamed (bOf κ ε) x) +
          (fTamed (bOf κ ε) x - 1 / x)| := by ring_nf
    _ ≤ |chebSum (bOf κ ε) (j0Of (bOf κ ε) ε + 1) x - fTamed (bOf κ ε) x| +
          |fTamed (bOf κ ε) x - 1 / x| := abs_add_le _ _
    _ ≤ ε + ε := add_le_add h19 h17
    _ = 2 * ε := by ring
