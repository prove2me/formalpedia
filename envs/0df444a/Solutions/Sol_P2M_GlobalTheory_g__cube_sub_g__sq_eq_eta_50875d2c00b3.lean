-- Prove2me | solution 1 for P2M_GlobalTheory_g__cube_sub_g__sq_eq_eta_50875d2c00b3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:33:53.728923+00:00
-- url     : https://prove2.me/submissions/c511dc7d-7715-46da-a50e-b181136b2bf0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsPolynomialModularJOfHasQExpansion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeDeterminedByInvariants
import Theorems.Thm_P2M_GlobalTheory_g__cube_sub_g__sq_eq_discriminant_b8dac546ba0a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter PeriodPair
open scoped Topology Real UpperHalfPlane
noncomputable section
open GlobalTheory
variable {L : PeriodPair} {a : ℂ} {τ : ℍ} (ha : a ≠ 0)
  (h : ∀ x, x ∈ L.lattice ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x)
include ha h
namespace GlobalTheory
theorem _root_.solution :
    L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = (2 * π / a) ^ 12 * ModularForm.eta τ ^ 24 :=
  g₂_cube_sub_g₃_sq_eq_discriminant ha h
end GlobalTheory
