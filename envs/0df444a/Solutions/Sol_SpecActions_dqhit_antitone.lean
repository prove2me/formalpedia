-- Prove2me | solution 1 for SpecActions.dqhit_antitone
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-12T04:18:58.467984+00:00
-- url     : https://prove2.me/submissions/ccc1d2d4-d395-4ab2-a631-e1abc2a5c472

import Mathlib
import Definitions.Def_SpecActions_model

open Finset SpecActions

theorem solution (pv : ℕ → ℝ) (hpv0 : ∀ j, 0 ≤ pv j) (hpv1 : ∀ j, pv j ≤ 1)
    (hsorted : ∀ i j, i ≤ j → pv j ≤ pv i) (m : ℕ) :
    dqhit pv (m + 1) ≤ dqhit pv m := by
  unfold dqhit
  rw [Finset.prod_range_succ]
  have hP : 0 ≤ ∏ j ∈ Finset.range m, (1 - pv j) :=
    Finset.prod_nonneg (fun j _ => by linarith [hpv1 j])
  have h2 : pv (m + 1) ≤ pv m := hsorted m (m + 1) (by omega)
  have h1 : (1 - pv m) * pv (m + 1) ≤ pv m := by
    nlinarith [hpv0 m, hpv0 (m + 1), hpv1 m]
  calc (∏ j ∈ Finset.range m, (1 - pv j)) * (1 - pv m) * pv (m + 1)
      = (∏ j ∈ Finset.range m, (1 - pv j)) * ((1 - pv m) * pv (m + 1)) := by ring
    _ ≤ (∏ j ∈ Finset.range m, (1 - pv j)) * pv m := mul_le_mul_of_nonneg_left h1 hP
