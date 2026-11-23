-- Prove2me | solution 1 for PI.Dv.Tr.phiS_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:58:09.056165+00:00
-- url     : https://prove2.me/submissions/cbb9bb39-4181-4f6c-b388-96cbc869251e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_ESMulESOfNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.Tr
open PI.Dv
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.Tr
theorem _root_.solution (T : GoodSet K G) (s : T.S) (X : Module.End K (T.W s)) :
    phiS T s X = ∑ x : G, (cf T s * LinearMap.trace K (T.W s) (T.tau s x⁻¹ * X)) • MonoidAlgebra.of K G x :=
  rfl
end PI.Dv.Tr
