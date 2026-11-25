-- Prove2me | solution 1 for PI.GGConvScalarW.psiU_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:40:58.264818+00:00
-- url     : https://prove2.me/submissions/e525cda5-dc62-4448-8e93-d5486109e9a5

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
theorem _root_.solution (ψ₀ : AddChar F ℂ) : psiU ψ₀ (1 : GL (Fin k) F) = 1 := by
  unfold psiU
  have h0 : superdiag k (1 : Matrix (Fin k) (Fin k) F) = 0 := by
    unfold superdiag
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    split_ifs with h
    · rw [Matrix.one_apply_ne]
      intro e
      rw [e] at h
      omega
    · rfl
  rw [Units.val_one, h0, AddChar.map_zero_eq_one]
end PI.GGConvScalarW
