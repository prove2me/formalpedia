-- Prove2me | solution 1 for actuarial_f_protected_replacement_instalment_respects_survivor_floor
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:07:32.64998+00:00
-- url     : https://prove2.me/submissions/30d4467e-5d7a-4f75-999a-1fdce23ea016

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_memberDue
import Definitions.Def_actuarial_f_estateInstalment
import Definitions.Def_actuarial_f_linkedFirstTranche
import Definitions.Def_actuarial_f_gmpProtectedReplacementInstalment

open ActuarialUnderpinsF

theorem B1h_repl_ge (P : Prop) (c s : ℝ) :
    s ≤ gmpProtectedSurvivorReplacement P c s := by
  unfold gmpProtectedSurvivorReplacement gmpProtectedSurvivorParallel
  split_ifs
  · exact le_rfl
  · exact le_max_right _ _

theorem solution
    (h r g z i j t : ℕ) (a b c : ℕ → ℝ)
    (sa sb : ℕ → ℕ → ℝ) (estate ga gb gc : ℕ → ℝ)
    (gs : ℕ → ℕ → ℝ) (ge : ℕ → ℝ)
    (memberSupplement : ℕ → ℕ → ℕ → ℝ)
    (statutorySurvivor : ℕ → ℕ → ℕ → ℕ → ℝ)
    (hm : 0 ≤ linkedFirstTranche r z i t a b ga gb +
      c z * gc t * memberDue r i t + memberSupplement z i t +
        estateInstalment h r g z i t estate ge) :
    statutorySurvivor z i j t ≤
      gmpProtectedReplacementInstalment h r g z i j t a b c sa sb
        estate ga gb gc gs ge memberSupplement statutorySurvivor := by
  unfold gmpProtectedReplacementInstalment
  have := B1h_repl_ge (estateDue h r g i t = 1)
    (gmpProtectedContractualSurvivor h z i j t a b sa sb gs) (statutorySurvivor z i j t)
  linarith
