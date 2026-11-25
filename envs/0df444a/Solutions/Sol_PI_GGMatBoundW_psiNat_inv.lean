-- Prove2me | solution 1 for PI.GGMatBoundW.psiNat_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:21:38.373619+00:00
-- url     : https://prove2.me/submissions/84662c32-8a8e-4c2e-8445-5f6b71bbeaec

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_PermRepApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_SuperdiagSgnConj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_GammaMatrixInverse
import Theorems.Thm_PI_GGMatBoundW_addChar_inv_eq_conj
import Theorems.Thm_PI_GGConvScalarW_isUni_inv
import Theorems.Thm_PI_GGConvScalarW_psiU_inv_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ComplexConjugate
noncomputable section
open Classical
open PI PI.GGMatBoundW
open Formalism.L2.SG.GGMirabolic PI.GGConvScalarW
namespace PI.GGMatBoundW
theorem _root_.solution {F : Type} [Field F] [Fintype F] {k : ℕ} (ψ₀ : AddChar F ℂ) (u : GL (Fin k) F) :
    psiNat ψ₀ u⁻¹ = conj (psiNat ψ₀ u) := by
  unfold psiNat
  by_cases hu : IsUni k u
  · rw [if_pos (isUni_inv hu), if_pos hu]
    rw [eq_inv_of_mul_eq_one_left (psiU_inv_mul ψ₀ hu)]
    unfold psiU
    exact addChar_inv_eq_conj ψ₀ _
  · have hu' : ¬ IsUni k u⁻¹ := fun h => hu (by simpa using isUni_inv h)
    rw [if_neg hu', if_neg hu, map_zero]
end PI.GGMatBoundW
