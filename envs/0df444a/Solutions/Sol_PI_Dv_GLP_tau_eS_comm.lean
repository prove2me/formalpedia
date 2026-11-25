-- Prove2me | solution 1 for PI.Dv.GLP.tau_eS_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:39:23.325418+00:00
-- url     : https://prove2.me/submissions/531845fa-eebe-4448-8c44-1fb756ec4546

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionLattices_FinrankIntertw
import Theorems.Thm_PI_Dv_GLP_asAlg_eS
import Theorems.Thm_PI_Dv_GLP_cS_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.GLP
open Representation
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.GLP
theorem _root_.solution (T : GoodSet K G) (s t : T.S) (g : G) :
    (T.tau t).asAlgebraHom (eS T s) * T.tau t g = T.tau t g * (T.tau t).asAlgebraHom (eS T s) := by
  rw [asAlg_eS, Finset.sum_mul, Finset.mul_sum]
  simp only [smul_mul_assoc, mul_smul_comm, ← map_mul]
  refine Fintype.sum_equiv (MulAut.conj g⁻¹).toEquiv _ _ fun x => ?_
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, inv_inv]
  have hc := cS_conj T s g⁻¹ x
  rw [inv_inv] at hc
  rw [hc]
  congr 2
  group
end PI.Dv.GLP
