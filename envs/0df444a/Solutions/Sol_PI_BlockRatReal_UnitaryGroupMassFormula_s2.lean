-- Prove2me | solution 1 for PI.BlockRatReal.UnitaryGroupMassFormula.s2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:40:57.370575+00:00
-- url     : https://prove2.me/submissions/51f82086-19d2-4cbd-b1f4-3303f99445da

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BlockRatReal
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_WeylLeDual
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_SumIcoTsubTelescope
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_RowDivStable
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylMap
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylRowStable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalRealBlocks_Bridge
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylModuleRowActionStable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.BlockRatReal PI.BlockRatReal.UnitaryGroupMassFormula
namespace PI.BlockRatReal.UnitaryGroupMassFormula
theorem _root_.solution {R : Type} [CommRing R] (k : ℕ) (ν : Fin k → ℕ) (g : Matrix (Fin k) (Fin k) R)
    (f : MvPolynomial (Fin k × Fin k) R) (hf : f ∈ PI.BlockRatReal.dualWeyl R k k ν) :
    Formalism.GradedWeylDivisibility.rowAct R g f ∈ PI.BlockRatReal.dualWeyl R k k ν := by
  have h1 : f ∈ Formalism.GradedWeylDivisibility.dualWeyl R k k ν := hf
  exact Formalism.GradedWeylDivisibility.dualWeylModuleRowActionStable R k k ν g f h1
end PI.BlockRatReal.UnitaryGroupMassFormula
