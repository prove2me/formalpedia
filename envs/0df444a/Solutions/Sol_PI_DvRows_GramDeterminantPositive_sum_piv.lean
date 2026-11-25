-- Prove2me | solution 1 for PI.DvRows.GramDeterminantPositive.sum_piv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:47:46.895373+00:00
-- url     : https://prove2.me/submissions/0d8f226e-0686-4519-9cd4-cf2ee3e760b5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_MulVecInjectiveOfKer
import Theorems.Thm_PI_DvRows_GramDeterminantPositive_piv_involutive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open PI.DvRows.GramDeterminantPositive
open Matrix
open scoped ComplexOrder
open NumberField Formalism.BasicNotions PI.Dv
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable (A : HLat K) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K)
namespace PI.DvRows.GramDeterminantPositive
theorem _root_.solution (F : InfinitePlace K → ℝ) : ∑ v, F (piv v) = ∑ v, F v :=
  Equiv.sum_comp (Function.Involutive.toPerm _ piv_involutive) F
end PI.DvRows.GramDeterminantPositive
