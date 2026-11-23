-- Prove2me | solution 1 for P2M_GlobalTheory_g__cube_div_eq_modularJ_a1bc96193403
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:58:33.823091+00:00
-- url     : https://prove2.me/submissions/4844b9d8-f337-4820-8073-a047f240f604

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsPolynomialModularJOfHasQExpansion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeDeterminedByInvariants
import Theorems.Thm_GlobalTheory_latticeCurve_j
import Theorems.Thm_GlobalTheory_modularJ_def
import Theorems.Thm_P2M_GlobalTheory_latticeCurve_c__6ffa6b5cc0c0


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
    1728 * L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) = modularJ τ := by
  rw [modularJ_def, ← latticeCurve_j ha h, WeierstrassCurve.j, Units.val_inv_eq_inv_val,
    WeierstrassCurve.coe_Δ', latticeCurve_Δ, latticeCurve_c₄]
  ring
end GlobalTheory
