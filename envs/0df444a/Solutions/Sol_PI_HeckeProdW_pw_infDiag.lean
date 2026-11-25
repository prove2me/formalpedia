-- Prove2me | solution 1 for PI.HeckeProdW.pw_infDiag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:41:52.128802+00:00
-- url     : https://prove2.me/submissions/14c0affc-36ce-4412-a0e2-61f81e2632df

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HeckeLocalProduct_Kernel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HeckeLocalProduct_PvLocalSelf
import Theorems.Thm_PI_HeckeProdW_infDiag_eq
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_HCFR_infIdele_fst_ne
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_HCFR_infIdele_fst_self


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host RestrictedProduct
open PI PI.HeckeProdW
variable {L : Type} [Field L] [NumberField L]
namespace PI.HeckeProdW
theorem _root_.solution (w : InfinitePlace L) (k : Lˣ) : pw w (infDiag k) = (atInf w k : w.Completion) := by
  rw [infDiag_eq, map_prod, Finset.prod_eq_single w]
  · exact infIdele_fst_self L w _
  · intro b _ hb
    exact infIdele_fst_ne L b w (Ne.symm hb) _
  · intro h
    exact absurd (Finset.mem_univ w) h
end PI.HeckeProdW
