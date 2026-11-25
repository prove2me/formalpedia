-- Prove2me | solution 1 for PI.Dv.TIW.rk_cut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:02:07.140839+00:00
-- url     : https://prove2.me/submissions/c87b998a-20cc-4c58-8a52-fc7e4d3c0cc7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_MatVTransvection
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsSmulMemTer
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_BlockHyp
import Theorems.Thm_PI_Dv_TIW_cut_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace PI.Dv.TIW
theorem _root_.solution (M : Submodule (𝓞 K) V) (hM : Submodule.span K (M : Set V) = ⊤) (X : Submodule K V) :
    Formalism.HN.rkK (M ⊓ X.restrictScalars (𝓞 K)) = Module.finrank K X := by
  rw [Formalism.HN.rkK, cut_span M hM X]
end PI.Dv.TIW
