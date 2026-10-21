-- Prove2me | solution 1 for PoSShares.Stability.eq_A2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T16:15:13.50776+00:00
-- url     : https://prove2.me/submissions/44912234-0c7d-4cad-8593-71fb933acc4e

import Mathlib
import Definitions.Def_PoSShares_Stability_Model

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology PoSShares.Stability

theorem stab_cs_succ (N₀ : ℝ) (R : ℕ → ℝ) (t : ℕ) :
    coinSupply N₀ R (t + 1) = coinSupply N₀ R t + R (t + 1) := by
  unfold coinSupply
  rw [Finset.sum_Icc_succ_top (by omega)]
  ring

theorem stab_cs_pos {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (t : ℕ) :
    0 < coinSupply M.N₀ M.R t := by
  induction t with
  | zero => simpa [coinSupply] using M.N₀_pos
  | succ t ih => rw [stab_cs_succ]; linarith [M.R_nonneg (t + 1)]

theorem solution {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (t : ℕ) (ω : Ω) :
    share M (t + 1) ω - share M t ω =
      M.R (t + 1) * (M.ξ (t + 1) ω - share M t ω) / coinSupply M.N₀ M.R (t + 1) := by
  have h1 := stab_cs_pos M t
  have h2 := stab_cs_pos M (t + 1)
  have h3 := stab_cs_succ M.N₀ M.R t
  unfold share
  rw [show coins M (t + 1) ω = coins M t ω + M.R (t + 1) * M.ξ (t + 1) ω from rfl]
  rw [div_sub_div _ _ h2.ne' h1.ne', div_eq_div_iff (by positivity) h2.ne']
  rw [h3]
  field_simp
  ring
