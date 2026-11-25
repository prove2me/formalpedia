-- Prove2me | solution 1 for PI.VolStabSW.fFSplit_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:32:33.77436+00:00
-- url     : https://prove2.me/submissions/cd235b4a-d427-4cda-b66f-43c834875eb3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFFS
import Theorems.Thm_PI_VolStabSW_FiniteFieldSplitting_fFSplit_nat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
namespace PI.VolStabSW
theorem _root_.solution : FFSplit := by
  unfold FFSplit
  intro k _ _ M a ha J hJ hJd T hT hTd
  have h := FiniteFieldSplitting.fFSplit_nat M a ha J hJ hJd T hT hTd
  simp only [FiniteFieldSplitting.swapR] at h
  rw [h, Nat.cast_mul, Nat.cast_prod, Nat.cast_pow]
  congr 1
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have h1 : 1 ≤ Nat.card k := Nat.card_pos
  have hi : (i : ℕ) ≤ M := by have := i.isLt; omega
  rw [Nat.cast_sub (Nat.pow_le_pow_right h1 hi), Nat.cast_pow, Nat.cast_pow]
end PI.VolStabSW
