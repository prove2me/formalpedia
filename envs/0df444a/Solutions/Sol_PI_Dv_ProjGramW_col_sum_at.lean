-- Prove2me | solution 1 for PI.Dv.ProjGramW.col_sum_at
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:35:48.225711+00:00
-- url     : https://prove2.me/submissions/ecc06a66-d00c-42f6-afb9-f1cf860aab58

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_AlgebraMapNeZeroOfNotMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_IdxDet
import Theorems.Thm_PI_Dv_ProjGramW_famC_std_apply
import Theorems.Thm_PI_Dv_ProjGramW_sum_smul_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjGramW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace PI.Dv.ProjGramW
theorem _root_.solution {d : ℕ} (j0 : Fin d) (v : Fin d → K) (r : Fin d → 𝓞 K) :
    (∑ k, r k • famC (stdE (K := K) d) (colOp j0 v) k) j0 = algebraMap (𝓞 K) K (r j0) * v j0 := by
  rw [sum_smul_apply, Finset.sum_eq_single j0]
  · rw [famC_std_apply]
    simp [colOp, Algebra.smul_def]
  · intro k _ hk
    rw [famC_std_apply]
    simp [colOp, hk, Ne.symm hk]
  · intro h
    exact absurd (Finset.mem_univ _) h
end PI.Dv.ProjGramW
