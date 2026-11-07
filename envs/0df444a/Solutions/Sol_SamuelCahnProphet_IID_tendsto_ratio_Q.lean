-- Prove2me | solution 1 for SamuelCahnProphet.IID.tendsto_ratio_Q
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T14:09:07.10719+00:00
-- url     : https://prove2.me/submissions/3c8b7bc9-6927-4508-b33a-d125e0678463

import Mathlib
import Definitions.Def_SamuelCahnProphet_IID_Setting
import Theorems.Thm_SamuelCahnProphet_IID_tendsto_expected_max
import Theorems.Thm_SamuelCahnProphet_IID_supE_threePoint_eq_max
import Theorems.Thm_SamuelCahnProphet_IID_tendsto_W_a
import Theorems.Thm_SamuelCahnProphet_IID_tendsto_W_one
import Theorems.Thm_SamuelCahnProphet_IID_aStarIID_spec

open MeasureTheory Filter Topology
open SamuelCahnProphet.IID

theorem solution (b c : ℝ) (hb : 0 < b) (hc : 0 < c) :
    Tendsto (fun k : ℕ =>
        (Emax (threePoint ((k + 1 : ℕ) : ℝ) (aStarIID b c) b c) (k + 1)).toReal /
          (supE (threePoint ((k + 1 : ℕ) : ℝ) (aStarIID b c) b c) (k + 1)).toReal) atTop
      (𝓝 (Q b c)) := by
  obtain ⟨hW, ha0, ha1⟩ := aStarIID_spec b c hb hc
  set a := aStarIID b c with ha
  have hE := tendsto_expected_max a b c ha0 ha1 hb hc
  have hWa := tendsto_W_a a b c ha0 ha1 hb hc
  have hW1 := tendsto_W_one a b c ha0 ha1 hb hc
  rw [hW] at hWa
  have hpos : 0 < 1 - Real.exp (-b) := by
    rw [sub_pos]; exact Real.exp_lt_one_iff.2 (by linarith)
  have hmax := hWa.max hW1
  rw [max_self] at hmax
  have hdiv := hE.div hmax hpos.ne'
  -- the limit is `Q b c`
  have hQ : (1 - Real.exp (-b) + a * (Real.exp (-b) - Real.exp (-b - c))) /
      (1 - Real.exp (-b)) = Q b c := by
    have hx : Real.exp (-b - c) = Real.exp (-b) * Real.exp (-c) := by
      rw [sub_eq_add_neg, Real.exp_add]
    have hbc : 0 < 1 - Real.exp (-b - c) := by
      rw [sub_pos]; exact Real.exp_lt_one_iff.2 (by linarith)
    rw [hx] at hbc
    simp only [Q, ha, aStarIID, hx]
    have h1 : 1 - Real.exp (-b) ≠ 0 := hpos.ne'
    have h2 : 1 - Real.exp (-b) * Real.exp (-c) ≠ 0 := hbc.ne'
    have h3 : c ≠ 0 := hc.ne'
    field_simp
    ring
  rw [hQ] at hdiv
  refine hdiv.congr' ?_
  -- eventually the sup is the max of the two rules, both finite
  have hev1 : ∀ᶠ k : ℕ in atTop, b + c < ((k + 1 : ℕ) : ℝ) := by
    obtain ⟨N, hN⟩ := exists_nat_gt (b + c)
    filter_upwards [eventually_ge_atTop N] with k hk
    have : (N : ℝ) ≤ k := by exact_mod_cast hk
    push_cast; linarith
  have hev2 := hWa.eventually (lt_mem_nhds hpos)
  have hev3 := hW1.eventually (lt_mem_nhds hpos)
  filter_upwards [hev1, hev2, hev3] with k hk h2 h3

  rw [supE_threePoint_eq_max a b c ha0 ha1 hb hc (k + 1) hk]
  have hne2 : EstopT (threePoint ((k + 1 : ℕ) : ℝ) a b c) (k + 1) a ≠ ⊤ := fun h => by
    rw [h, ENNReal.toReal_top] at h2; exact lt_irrefl _ h2
  have hne3 : EstopT (threePoint ((k + 1 : ℕ) : ℝ) a b c) (k + 1) 1 ≠ ⊤ := fun h => by
    rw [h, ENNReal.toReal_top] at h3; exact lt_irrefl _ h3
  rw [ENNReal.toReal_max hne2 hne3]
  rfl
