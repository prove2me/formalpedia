-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.ChooseW.star_li
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:41:25.787811+00:00
-- url     : https://prove2.me/submissions/197b71a6-9617-4272-a329-b5d3a023144a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_SepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_LatticeIsometry
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_Choose
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
open NumberField Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
open PI.UnitaryGroupMassFormula.LCG.ChooseW
variable {E : Type*} [Field E] [StarRing E] {n : ℕ}
namespace PI.UnitaryGroupMassFormula.LCG.ChooseW
theorem _root_.solution {k : ℕ} (v : Fin k → Fin n → E) (h : LinearIndependent E v) :
    LinearIndependent E (fun a => sv (v a)) := by
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro g hg i
  have h0 : ∑ a, starRingEnd E (g a) • v a = 0 := by
    funext j
    have := congrArg (starRingEnd E) (congrFun hg j)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sv, map_sum, map_mul,
      starRingEnd_self_apply, map_zero, Pi.zero_apply] at this ⊢
    rw [← this]
  have := h _ h0 i
  simpa using this
end PI.UnitaryGroupMassFormula.LCG.ChooseW
