-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.kronFun_qExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:58:54.871049+00:00
-- url     : https://prove2.me/submissions/62292998-1e21-465b-b2ea-b9fe287f5a6c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEisInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDeltaInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalSer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalMF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQExpEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQPrin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGmForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGmQ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_IsIntegralOfRoot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModFrobSer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModKronSer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModKronPt
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_L1_Gm_isMF__25d25372ce7e
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kronFun_isMF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_aC_conv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_dC_conv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_aC_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_dC_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Cg_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Cg_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Conv_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Conv_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Conv_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Conv_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsMF_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsMF_conv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsMF_ev_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsMF_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsMF_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsMF_qExp_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsMF_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_LowUnit_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_ev_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_ev_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_ev_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_ev_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_qm_one_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {p : ℕ} (hp : p.Prime) :
    qExpansion 1 (kronFun p) = qExpansion 1 (Gm p) + (aC * dC ^ p - aC ^ p * dC) ^ 2 := by
  have hq : ∀ τ : ℍ, ‖qm 1 τ‖ < 1 := fun τ => by
    rw [qm_one_eq]
    simpa using UpperHalfPlane.norm_qParam_lt_one 1 τ
  have hG := Gm_isMF' hp
  have c1 : Conv (aC * dC ^ p) := aC_conv.mul (dC_conv.pow p)
  have c2 : Conv (aC ^ p * dC) := (aC_conv.pow p).mul dC_conv
  have c3 : Conv (aC * dC ^ p - aC ^ p * dC) := c1.sub c2
  apply (kronFun_isMF hp).qExp_eq (hG.conv.add (c3.pow 2))
  intro τ
  rw [ev_add hG.conv (c3.pow 2) (hq τ), hG.ev_eq τ, ev_pow c3 2 (hq τ), ev_sub c1 c2 (hq τ),
    ev_mul aC_conv (dC_conv.pow p) (hq τ), ev_pow dC_conv p (hq τ), ev_mul (aC_conv.pow p) dC_conv (hq τ),
    ev_pow aC_conv p (hq τ), aC_ev, dC_ev]
  rfl
end ReciprocityTheory.ChartRestriction.L1
