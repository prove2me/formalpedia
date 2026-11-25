-- Prove2me | solution 1 for P2M_GlobalTheory_lattice_eq_of_g__eq_of_g__eq_399c7fadf18d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:43:34.872061+00:00
-- url     : https://prove2.me/submissions/c3080cb6-9fba-440e-8a98-8cd660154d9d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsPolynomialModularJOfHasQExpansion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeDeterminedByInvariants
import Theorems.Thm_P2M_GlobalTheory_lattice_le_of_g__eq_of_g__eq_4fd8d18e060a

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
theorem _root_.solution {L L' : PeriodPair} (h₂ : L.g₂ = L'.g₂)
    (h₃ : L.g₃ = L'.g₃) : L.lattice = L'.lattice :=
  le_antisymm (lattice_le_of_g₂_eq_of_g₃_eq h₂ h₃) (lattice_le_of_g₂_eq_of_g₃_eq h₂.symm h₃.symm)
end GlobalTheory
