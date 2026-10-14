-- Prove2me | solution 1 for actuarial_d_mthly_one_per_year
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:38.965036+00:00
-- url     : https://prove2.me/submissions/d1346ff2-137f-40de-845f-4c20d5a5c150

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_mthlyPath
import Definitions.Def_actuarial_d_annPath

open ActuarialJointD

theorem solution (years : ℕ) (d b s : ℕ → ℝ) : mthlyPath years 1 d b s = annPath years d b s := by
  simp [annPath, mthlyPath]
