-- Prove2me | solution 1 for RInf.induced_eigen_one
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T01:05:12.545251+00:00
-- url     : https://prove2.me/submissions/72558dec-531b-4d11-886b-eb51efe50fac

import Mathlib
import Definitions.Def_RInf_alg
import Definitions.Def_RInf_braid
open RInf

theorem solution {n : Nat} {P Q : Type*} [Group P] [AddCommGroup Q]
    (W : BraidWorld n P Q) (α : P ≃* P) : HasEigenOne (W.act α) := by
  obtain ⟨σ, hσ⟩ := W.factor α
  rw [hσ]
  exact W.rep_eigen σ
