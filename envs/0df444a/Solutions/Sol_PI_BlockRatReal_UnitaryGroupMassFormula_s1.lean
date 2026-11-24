-- Prove2me | solution 1 for PI.BlockRatReal.UnitaryGroupMassFormula.s1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:16:36.810807+00:00
-- url     : https://prove2.me/submissions/1b323e14-0a90-4fba-bedd-0c9c753b04f5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BlockRatReal
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_WeylLeDual
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_SumIcoTsubTelescope
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_RowDivStable
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylMap
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylRowStable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalRealBlocks_Bridge
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylModuleMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylModuleRowDividedPowerStable
import Theorems.Thm_Formalism_GradedWeylDivisibility_highestWeightVectorMem
import Theorems.Thm_Formalism_GradedWeylDivisibility_weylLeDual_of


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
theorem _root_.solution {S : Type} [CommRing S] (φ : ℤ →+* S) (k : ℕ) (ν : Fin k → ℕ) (hν : Antitone ν)
    (f : MvPolynomial (Fin k × Fin k) ℤ) (hf : f ∈ PI.BlockRatReal.weyl ℤ k k le_rfl ν) :
    MvPolynomial.map φ f ∈ PI.BlockRatReal.dualWeyl S k k ν := by
  have hle := Formalism.GradedWeylDivisibility.weylLeDual_of Formalism.GradedWeylDivisibility.highestWeightVectorMem Formalism.GradedWeylDivisibility.dualWeylModuleRowDividedPowerStable
  have h1 : f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℤ k k ν := hle ℤ k k le_rfl ν hν hf
  exact Formalism.GradedWeylDivisibility.dualWeylModuleMap ℤ S φ k k ν f h1
end PI.BlockRatReal.UnitaryGroupMassFormula
