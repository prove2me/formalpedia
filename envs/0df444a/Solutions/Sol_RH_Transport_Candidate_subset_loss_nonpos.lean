-- Prove2me | solution 1 for RH.Transport.Candidate.subset_loss_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:12:10.074452+00:00
-- url     : https://prove2.me/submissions/1e8add5f-ff07-4b1a-a4e7-be4b19a88f6b

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_Candidate
set_option autoImplicit false
open RH RH.Transport RH.Transport.Candidate
open RH.Transport.Geometry
open RH.Transport.LocalBounds
noncomputable section

theorem solution {d : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ ell p) :
    subsetLoss p d ≤ 0 := by
  rw [subsetLoss]
  by_cases h : 0 ≤ 5 * ell p - 1 + d
  · rw [max_eq_right h]
    norm_num [ell, p] at *
    linarith
  · rw [max_eq_left (le_of_not_ge h)]
    linarith
