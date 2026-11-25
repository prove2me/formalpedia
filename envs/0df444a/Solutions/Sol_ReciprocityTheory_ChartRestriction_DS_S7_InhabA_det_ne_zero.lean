-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.InhabA.det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:13:49.37608+00:00
-- url     : https://prove2.me/submissions/eda20997-1d89-4b44-baf9-f942db499874

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_Lemmata_MovedPointExistence_ExistsMoved
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_InhabA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_InhabA_star_det_mul_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.S7.InhabA
open ReciprocityTheory.ChartRestriction.DS
variable {m : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7.InhabA
theorem _root_.solution {ε : Fin m → Bool} (s : Bool) {k : Matrix (Fin m) (Fin m) ℂ} (hk : k ∈ Kset ε) :
    (k.submatrix (fun x : {a // ε a = s} => x.1) (fun x : {a // ε a = s} => x.1)).det ≠ 0 := by
  intro h
  have := star_det_mul_det s hk
  rw [h, mul_zero] at this
  exact zero_ne_one this
end ReciprocityTheory.ChartRestriction.DS.S7.InhabA
