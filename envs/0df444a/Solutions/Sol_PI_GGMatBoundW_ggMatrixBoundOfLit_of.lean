-- Prove2me | solution 1 for PI.GGMatBoundW.ggMatrixBoundOfLit_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:50:32.336441+00:00
-- url     : https://prove2.me/submissions/fbeb59f8-a303-41b2-9281-15736fd67a0c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_PermRepApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_GgMatrixBoundOfLitOf
import Theorems.Thm_PI_GGMatBoundW_ggMatrixBound_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open scoped ComplexConjugate ComplexOrder
noncomputable section
open Classical
open PI PI.GGMatBoundW
open Formalism.L2.SG.GGMirabolic
namespace PI.GGMatBoundW
theorem _root_.solution (hM : MatrixEq) (hH : TotHerm) (hE : EigBound) (hS : SpecPSD)
    (hCL : ConvScalarOfLit) (hRB : GenericRatioOfBound) (hCU : CardUni) : GGMatrixBoundOfLit :=
  fun hGG hMB => ggMatrixBound_of hM hH hE hS (hCL hGG) (hRB hMB hCU)
end PI.GGMatBoundW
