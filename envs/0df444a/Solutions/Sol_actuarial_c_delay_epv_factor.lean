-- Prove2me | solution 1 for actuarial_c_delay_epv_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-15T13:12:26.198983+00:00
-- url     : https://prove2.me/submissions/8473af0c-35e3-42db-8c2f-d77507cca975

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_path
import Definitions.Def_actuarial_c_epv
import Definitions.Def_actuarial_c_delayPath
import Definitions.Def_actuarial_c_delayEPV
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open ActuarialAssurances

private theorem delay_path_factor_local (h lag k : ℕ) (v : ℝ) (b : ℕ → ℝ) :
    delayPath h lag v b k = v^lag * path h v b k := by
  unfold delayPath path
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have he : j + 1 + lag = (j+1)+lag := rfl
  rw [he, pow_add]
  ring

theorem solution (h lag : ℕ) (v : ℝ) (b p : ℕ → ℝ) :
    delayEPV h lag v b p = v^lag * epv h v b p := by
  unfold delayEPV epv
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [delay_path_factor_local]
  ring
