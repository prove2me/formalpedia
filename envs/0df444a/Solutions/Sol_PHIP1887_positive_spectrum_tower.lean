-- Prove2me | solution 1 for PHIP1887.positive_spectrum_tower
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:53:35.830774+00:00
-- url     : https://prove2.me/submissions/fff635ab-ad02-46ef-8f84-b36ffd3953b9

import Mathlib
import Definitions.Def_RHPF28_PHIP1887_6e42e337ddd5
import Theorems.Thm_PHIP1887_real_atom_nonneg
open MeasureTheory Set
open PHIP1887

theorem solution (r : ℕ → ℝ) (p q : ℕ)
    (h : ∀ j, 0 ≤ r j ∧ r j ≤ 1)
    (_hs : Summable (fun j => (atom (r j : ℂ) p q).re)) :
    0 ≤ tower (fun j => (r j : ℂ)) p q := by
  apply tsum_nonneg
  intro j
  exact real_atom_nonneg (r j) p q (h j).1 (h j).2
