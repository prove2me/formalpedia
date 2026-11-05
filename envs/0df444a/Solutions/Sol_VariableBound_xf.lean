-- Prove2me | solution 1 for VariableBound.xf
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:23:29.72325+00:00
-- url     : https://prove2.me/submissions/fb92e8e1-7864-4fb5-a3ed-beeec5f6e18b

import Theorems.Thm_VariableBound_StepParity_cutoff
import Definitions.Def_AppVariablesStatement
import Definitions.Def_ClauseBound_ParityChecks_StepOne
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.List.GetD
import Definitions.Def_VariableBound_StepParity

set_option autoImplicit false

open VariableBound
open Finset ParityChecks AppVariables StepParity

theorem solution : AppVariables.XFStmt := by
  intro X E _ _ _ V nb L β n M hβ hM hnM
  have choose_mul (A : Finset E) (c : ℕ) (y : ℤ) :
      ((#A).choose c : ℤ) * y = ∑ _S₀ ∈ A.powerset with #_S₀ = c, y := by
    simp [← Finset.powersetCard_eq_filter, Finset.card_powersetCard]
  constructor
  · simpa only [AppVariables.Xsum, choose_mul] using
      (VariableBound.StepParity.cutoff (X := X) (E := E) V L
        (fun ξ => ((#(V ξ)).choose (nb + 1) : ℤ)) hβ hM)
  · simpa only [AppVariables.Fsum, ParityChecks.eta, Finset.sum_mul] using
      (VariableBound.StepParity.cutoff (X := X) (E := E) V L
        (fun ξ => ParityChecks.eta V nb ξ) (ν := n + 1) (M' := M)
        (Nat.succ_le_succ (Nat.zero_le n)) hnM)
