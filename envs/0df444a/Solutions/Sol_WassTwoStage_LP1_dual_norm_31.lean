-- Prove2me | solution 1 for WassTwoStage.LP1.dual_norm_31
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:43:11.90784+00:00
-- url     : https://prove2.me/submissions/1a51cf92-83f1-4b05-a7e6-d63e3062aa87

import Mathlib
import Definitions.Def_WassTwoStage_LP1_Gauge

set_option autoImplicit false
open Matrix WassTwoStage.LP1

theorem gauge_single {K : ℕ} (wp wm : ℝ) (k : Fin K) (c : ℝ) :
    WassTwoStage.LP1.gauge wp wm (Pi.single k c : Fin K → ℝ) = max (wp * c) (-(wm * c)) := by
  unfold WassTwoStage.LP1.gauge
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    simp [Pi.single_apply, hj]
  · intro h; exact absurd (Finset.mem_univ k) h

theorem solution {K : ℕ} (hK : 0 < K) (wp wm : ℝ) (hwp : 0 < wp) (hwm : 0 < wm)
    (z : Fin K → ℝ) :
    dualGauge wp wm z =
      ((Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hK⟩⟩)
        (fun k => max (z k / wp) (-z k / wm)) : ℝ) : EReal) := by
  set hne := Finset.univ_nonempty_iff.mpr ⟨(⟨0, hK⟩ : Fin K)⟩ with hhne
  set M : ℝ := Finset.univ.sup' hne (fun k => max (z k / wp) (-z k / wm)) with hM
  have hkM : ∀ k, max (z k / wp) (-z k / wm) ≤ M := fun k =>
    Finset.le_sup' (fun k => max (z k / wp) (-z k / wm)) (Finset.mem_univ k)
  have hM0 : 0 ≤ M := by
    have h := hkM ⟨0, hK⟩
    have : 0 ≤ max (z ⟨0, hK⟩ / wp) (-z ⟨0, hK⟩ / wm) := by
      rcases le_total 0 (z ⟨0, hK⟩) with h0 | h0
      · exact le_max_of_le_left (div_nonneg h0 hwp.le)
      · exact le_max_of_le_right (div_nonneg (by linarith) hwm.le)
    linarith
  unfold dualGauge
  apply le_antisymm
  · refine iSup₂_le fun ξ hξ => ?_
    have hle : z ⬝ᵥ ξ ≤ M := by
      have hterm : ∀ k, z k * ξ k ≤ M * max (wp * ξ k) (-(wm * ξ k)) := by
        intro k
        have hmax0 : 0 ≤ max (wp * ξ k) (-(wm * ξ k)) := by
          rcases le_total 0 (ξ k) with h0 | h0
          · exact le_max_of_le_left (by positivity)
          · exact le_max_of_le_right (by nlinarith)
        have h1 := hkM k
        rcases le_total 0 (ξ k) with h0 | h0
        · have a1 : z k / wp ≤ M := (le_max_left _ _).trans h1
          have : z k * ξ k = (z k / wp) * (wp * ξ k) := by field_simp
          rw [this]
          calc z k / wp * (wp * ξ k) ≤ M * (wp * ξ k) :=
                mul_le_mul_of_nonneg_right a1 (by positivity)
            _ ≤ M * max (wp * ξ k) (-(wm * ξ k)) :=
                mul_le_mul_of_nonneg_left (le_max_left _ _) hM0
        · have a1 : -z k / wm ≤ M := (le_max_right _ _).trans h1
          have : z k * ξ k = (-z k / wm) * (-(wm * ξ k)) := by field_simp
          rw [this]
          calc -z k / wm * (-(wm * ξ k)) ≤ M * (-(wm * ξ k)) :=
                mul_le_mul_of_nonneg_right a1 (by nlinarith)
            _ ≤ M * max (wp * ξ k) (-(wm * ξ k)) :=
                mul_le_mul_of_nonneg_left (le_max_right _ _) hM0
      calc z ⬝ᵥ ξ = ∑ k, z k * ξ k := rfl
        _ ≤ ∑ k, M * max (wp * ξ k) (-(wm * ξ k)) := Finset.sum_le_sum fun k _ => hterm k
        _ = M * WassTwoStage.LP1.gauge wp wm ξ := by unfold WassTwoStage.LP1.gauge; rw [Finset.mul_sum]
        _ ≤ M * 1 := mul_le_mul_of_nonneg_left hξ hM0
        _ = M := mul_one M
    exact_mod_cast hle
  · obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_sup' hne (fun k => max (z k / wp) (-z k / wm))
    rw [← hM] at hk
    rcases le_total (-z k / wm) (z k / wp) with h | h
    · -- M = z k / wp
      have hMk : M = z k / wp := by rw [hk]; exact max_eq_left h
      refine le_iSup₂_of_le (Pi.single k (1 / wp) : Fin K → ℝ) ?_ ?_
      · rw [gauge_single]
        have : wp * (1 / wp) = 1 := by field_simp
        rw [this]
        have : -(wm * (1 / wp)) ≤ 1 := by
          have : 0 ≤ wm * (1 / wp) := by positivity
          linarith
        exact max_le le_rfl (this.trans le_rfl)
      · have : z ⬝ᵥ (Pi.single k (1 / wp) : Fin K → ℝ) = M := by
          rw [hMk]; simp [dotProduct_single]; ring
        rw [this]
    · have hMk : M = -z k / wm := by rw [hk]; exact max_eq_right h
      refine le_iSup₂_of_le (Pi.single k (-(1 / wm)) : Fin K → ℝ) ?_ ?_
      · rw [gauge_single]
        have : -(wm * -(1 / wm)) = 1 := by field_simp
        rw [this]
        have : wp * -(1 / wm) ≤ 1 := by
          have : 0 ≤ wp * (1 / wm) := by positivity
          nlinarith
        exact max_le this le_rfl
      · have : z ⬝ᵥ (Pi.single k (-(1 / wm)) : Fin K → ℝ) = M := by
          rw [hMk]; simp [dotProduct_single]; ring
        rw [this]
