-- Prove2me | solution 1 for TaoBR.restr_zero_of_forall_br
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T21:01:00.255774+00:00
-- url     : https://prove2.me/submissions/800e55c3-05c5-4ccd-9403-344dc6b985ef
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_TaoBR
import Theorems.Thm_TaoBR_restr_two_mul_of_br
import Theorems.Thm_TaoBR_restr_zero_of_restr

open scoped ENNReal

namespace TaoBR

theorem restr_zero_of_forall_br_dev (n : ℕ) (hn : 2 ≤ n) (p : ℝ≥0∞) (hp : 1 < p)
    (hp' : p ≤ ENNReal.ofReal (2 * n / (n + 1))) (h : ∀ ε : ℝ, 0 < ε → BR n p ε) :
    ∀ q : ℝ≥0∞, 1 ≤ q → q < p → Restr n q 0 := by
  intro q hq hqp
  have hpt : p ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hp'
  have hqt : q ≠ ⊤ := ne_top_of_lt hqp
  set pr := p.toReal with hpr
  set qr := q.toReal with hqr
  have hpe : ENNReal.ofReal pr = p := ENNReal.ofReal_toReal hpt
  have hqe : ENNReal.ofReal qr = q := ENNReal.ofReal_toReal hqt
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpr1 : 1 < pr := by
    have := (ENNReal.toReal_lt_toReal (by simp) hpt).2 hp
    simpa using this
  have hpr2 : pr < 2 := by
    have h1 : pr ≤ 2 * n / (n + 1) := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hp'
      rwa [ENNReal.toReal_ofReal (by positivity)] at this
    have h2 : 2 * (n : ℝ) / (n + 1) < 2 := by
      rw [div_lt_iff₀ (by positivity)]; linarith
    linarith
  have hqr1 : 1 ≤ qr := by
    have := (ENNReal.toReal_le_toReal (by simp) hqt).2 hq
    simpa using this
  have hqp' : qr < pr := (ENNReal.toReal_lt_toReal hqt hpt).2 hqp
  obtain ⟨C, α₀, hα₀, hmain⟩ := restr_zero_of_restr n hn pr hpr1 hpr2
  set d := 1 / qr - 1 / pr with hd
  have hdpos : 0 < d := by
    have : 1 / pr < 1 / qr := one_div_lt_one_div_of_lt (by linarith) hqp'
    linarith
  set L := |C| / d + 1 with hL
  have hLpos : 0 < L := by positivity
  set α := min (α₀ / 2) (Real.exp (-L)) with hα
  have hαpos : 0 < α := lt_min (by positivity) (Real.exp_pos _)
  have hαlt : α < α₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hαexp : α ≤ Real.exp (-L) := min_le_right _ _
  have hlog : L ≤ Real.log (1 / α) := by
    rw [one_div, Real.log_inv]
    have := Real.log_le_log hαpos hαexp
    rw [Real.log_exp] at this
    linarith
  have hlogpos : 0 < Real.log (1 / α) := lt_of_lt_of_le hLpos hlog
  have hCd : C / Real.log (1 / α) < d := by
    calc C / Real.log (1 / α) ≤ |C| / Real.log (1 / α) :=
          div_le_div_of_nonneg_right (le_abs_self C) hlogpos.le
      _ ≤ |C| / L := div_le_div_of_nonneg_left (abs_nonneg C) hLpos hlog
      _ < d := by
          rw [div_lt_iff₀ hLpos]
          have : |C| / d * d = |C| := div_mul_cancel₀ _ hdpos.ne'
          rw [hL]; nlinarith
  have hbr : Restr n (ENNReal.ofReal pr) α := by
    rw [hpe]
    have := restr_two_mul_of_br n hn p hp.le hp' (α / 2) (by positivity) (h (α / 2) (by positivity))
    simpa [mul_div_cancel₀ α (two_ne_zero)] using this
  have := hmain α hαpos hαlt hbr qr hqr1 (by rw [hd] at hCd; linarith)
  rwa [hqe] at this

end TaoBR

theorem solution : type_of% @TaoBR.restr_zero_of_forall_br_dev := @TaoBR.restr_zero_of_forall_br_dev
