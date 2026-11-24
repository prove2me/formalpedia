-- Prove2me | solution 1 for PI.BlockRatReal.UnitaryGroupMassFormula.map_map_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:39.304192+00:00
-- url     : https://prove2.me/submissions/9d8d80d4-3e33-4049-ae95-898f9aaa8f9d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BlockRatReal
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_WeylLeDual
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_SumIcoTsubTelescope
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_RowDivStable
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylMap
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylRowStable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalRealBlocks_Bridge

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
theorem _root_.solution {LL : Type} [Field LL] (φ : LL →+* ℂ) {σ : Type} (f : MvPolynomial σ ℤ) :
    MvPolynomial.map φ (MvPolynomial.map (Int.castRingHom LL) f) = MvPolynomial.map (Int.castRingHom ℂ) f := by
  rw [MvPolynomial.map_map, RingHom.ext_int (φ.comp (Int.castRingHom LL)) (Int.castRingHom ℂ)]
end PI.BlockRatReal.UnitaryGroupMassFormula
