-- Prove2me | solution 1 for PI.FockOneDegW.isKC_Eab
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:29.106347+00:00
-- url     : https://prove2.me/submissions/82d04fd8-86b0-4fa6-84e3-ba699923ea22

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_RedDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_FockInnerEqSumRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_RaisingLoweringSplit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_SameBlockOfPosC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial FockRaiseLowInner
open PI PI.FockOneDegW
namespace PI.FockOneDegW
theorem _root_.solution {p q : ℕ} {a b : Ix p q} (h : sameBlock a b) : IsKC (Eab a b) := by
  intro x y hxy
  simp only [Eab, Matrix.single_apply]
  split_ifs with h'
  · obtain ⟨rfl, rfl⟩ := h'
    exact absurd h hxy
  · rfl
end PI.FockOneDegW
