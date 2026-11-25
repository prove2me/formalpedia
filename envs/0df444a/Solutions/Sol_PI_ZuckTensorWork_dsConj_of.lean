-- Prove2me | solution 1 for PI.ZuckTensorWork.dsConj_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:16:33.300725+00:00
-- url     : https://prove2.me/submissions/f91a6182-ab58-4d9c-b6f4-fb8789cdad76

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_ZuckTensor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualChoice
import Theorems.Thm_PI_ZuckTensorWork_dualWeight_dualWeight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped InnerProductSpace
noncomputable section
open PI PI.ZuckTensorWork
open PI.UpqRep PI.ZuckTensor
namespace PI.ZuckTensorWork
theorem _root_.solution (h1 : URepConj) (h2 : IrredConj) (h3 : SqIntConj) (h4 : KTypeConj) (h5 : KTypeConjInv)
    (h6 : LowKRev) (h7 : VNormRev) : DSConj := by
  intro n ε H _ _ σ lam ⟨hc, hn, hu, hi, hs, ⟨S, hS⟩, hmin⟩
  refine ⟨inferInstanceAs (CompleteSpace H), inferInstanceAs (Nontrivial H), h1 n ε H σ hu, h2 n ε H σ hi, h3 n ε H σ hs,
    ⟨cjSub S, by rw [h6]; exact h4 n ε H σ _ S hS⟩, fun μ S' hS' => ?_⟩
  have := hmin (revP μ) (cjSubInv S') (h5 n ε H σ μ S' hS')
  rw [h6, h7]
  calc vNormSq ε (lowK ε lam) ≤ vNormSq ε (revP μ) := this
    _ = vNormSq (revE ε) (revP (revP μ)) := (h7 n ε (revP μ)).symm
    _ = vNormSq (revE ε) μ := by rw [dualWeight_dualWeight]
end PI.ZuckTensorWork
