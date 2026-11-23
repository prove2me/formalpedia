-- Prove2me | solution 1 for PI.GGConvScalarW.psiU_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:43.700773+00:00
-- url     : https://prove2.me/submissions/35a837b3-c5bf-44f0-9409-62bcd1d84b1d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_SuperdiagSgnConj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
noncomputable section
open Classical
open PI PI.GGConvScalarW
open Formalism.L2.SG.GGMirabolic
variable {F : Type} [Field F] [Fintype F] {k : ℕ}
namespace PI.GGConvScalarW
theorem _root_.solution (ψ₀ : AddChar F ℂ) (x : GL (Fin k) F) : psiU ψ₀ x ≠ 0 := by
  unfold psiU
  intro h
  have h1 := AddChar.map_add_eq_mul ψ₀ (superdiag k (x : Matrix (Fin k) (Fin k) F)) (-(superdiag k (x : Matrix (Fin k) (Fin k) F)))
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at h1
  exact one_ne_zero h1
end PI.GGConvScalarW
