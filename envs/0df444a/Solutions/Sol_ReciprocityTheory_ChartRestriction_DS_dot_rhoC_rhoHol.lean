-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.dot_rhoC_rhoHol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:33:38.515801+00:00
-- url     : https://prove2.me/submissions/6fcb58c3-6290-4013-bdb2-2b10281ee7e4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CsqDdPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARUnit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rhoC_mul_sign_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (ε : Fin n → Bool) : dot (rhoC ε) (rhoHol ε) = 0 :=
  rhoC_mul_sign_sum ε (fun t => if t then (qOf ε : ℝ) / 2 else -(pOf ε : ℝ) / 2)
end ReciprocityTheory.ChartRestriction.DS
