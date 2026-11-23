-- Prove2me | solution 1 for P2M_GlobalTheory_IsHomothetic_g__eq_8571fef95872
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:38:25.147089+00:00
-- url     : https://prove2.me/submissions/bc506647-1634-4ed8-839f-40198738aeb3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsPolynomialModularJOfHasQExpansion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeDeterminedByInvariants
import Theorems.Thm_GlobalTheory_IsHomothetic_G_eq


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
namespace GlobalTheory
namespace IsHomothetic
theorem _root_.solution {L L' : PeriodPair} {c : ℂ} (h : IsHomothetic c L L') :
    L'.g₃ = (c ^ 6)⁻¹ * L.g₃ := by
  rw [g₃, g₃, h.G_eq]; ring
end IsHomothetic
end GlobalTheory
