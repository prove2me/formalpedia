-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.GLChiPf.mulSingle_comp_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:35:29.075282+00:00
-- url     : https://prove2.me/submissions/df2409c5-f159-4b91-83f4-964b3bc7047b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_LocSplitChiOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_GLDelta
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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq
open PI.UnitaryGroupMassFormula.AdIndexEq.GLChiPf
open Matrix
variable {k : Type} [Field k] {n : ℕ}
namespace PI.UnitaryGroupMassFormula.AdIndexEq.GLChiPf
theorem _root_.solution (i j : Fin n) (d : kˣ) :
    (Pi.mulSingle i d : Fin n → kˣ) ∘ (Equiv.swap i j) = Pi.mulSingle j d := by
  funext x
  simp only [Function.comp_apply]
  by_cases hxj : x = j
  · subst hxj; simp
  · by_cases hxi : x = i
    · subst hxi
      rw [Equiv.swap_apply_left, Pi.mulSingle_eq_of_ne (Ne.symm hxj), Pi.mulSingle_eq_of_ne hxj]
    · rw [Equiv.swap_apply_of_ne_of_ne hxi hxj, Pi.mulSingle_eq_of_ne hxi, Pi.mulSingle_eq_of_ne hxj]
end PI.UnitaryGroupMassFormula.AdIndexEq.GLChiPf
