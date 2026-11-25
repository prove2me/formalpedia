-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.lminor_LMU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:25:14.619544+00:00
-- url     : https://prove2.me/submissions/d20bde45-31f6-4f9a-b1a6-5b5d4c602b9d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_LeviVReLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantNormalForms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DetSubUpper
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_KappaStatementHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_LminorMapConj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_sub_LMU

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
open Matrix ReciprocityTheory.ChartRestriction.G.FD
variable {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
theorem _root_.solution (L M U : Matrix (Fin r) (Fin r) ℂ)
    (hL : ∀ a c : Fin r, c < a → L a c = 0) (hU : ∀ a c : Fin r, c < a → U a c = 0) (k : Fin (r + 1)) :
    lminor (Lᵀ * M * U) k =
      (L.submatrix (Fin.castLE (Nat.le_of_lt_succ k.isLt)) (Fin.castLE (Nat.le_of_lt_succ k.isLt))).det *
        lminor M k *
        (U.submatrix (Fin.castLE (Nat.le_of_lt_succ k.isLt)) (Fin.castLE (Nat.le_of_lt_succ k.isLt))).det := by
  unfold lminor
  rw [sub_LMU _ L M U hL hU, det_mul, det_mul, det_transpose]
end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
