-- Prove2me | solution 1 for PI.Dv.ProjGramW.sums_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:39:52.647335+00:00
-- url     : https://prove2.me/submissions/98ec33b2-64b8-4e8d-9435-ba5eb58211da

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_AlgebraMapNeZeroOfNotMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_IdxDet
import Theorems.Thm_PI_Dv_ProjGramW_colOp_col

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjGramW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace PI.Dv.ProjGramW
theorem _root_.solution {d : ℕ} (j0 : Fin d) (v : Fin d → K) (r : Fin d → 𝓞 K) (hr : r j0 = 0) :
    ∑ k, r k • famC (stdE (K := K) d) (colOp j0 v) k = ∑ k, r k • stdE d k := by
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : k = j0
  · rw [hk, hr, zero_smul, zero_smul]
  · rw [colOp_col j0 v k hk]
end PI.Dv.ProjGramW
