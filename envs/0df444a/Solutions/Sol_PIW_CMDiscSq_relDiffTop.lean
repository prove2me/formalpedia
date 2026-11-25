-- Prove2me | solution 1 for PIW.CMDiscSq.relDiffTop
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:54:25.294878+00:00
-- url     : https://prove2.me/submissions/ec5c8e5a-8f27-4b92-9745-7f3af39c7806

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMDiscriminantSquare_AdjoinEqTopOfStarNe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMDiscriminantSquare_SubMemDifferentIdeal
import Theorems.Thm_PIW_CMDiscSq_sub_mem_differentIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
open PIW PIW.CMDiscSq
namespace PIW.CMDiscSq
theorem _root_.solution : RelDiffTop := by
  intro F E _ _ _ _ _ _ hFE
  obtain ⟨⟨_, _, hP⟩, hR⟩ := hFE
  by_contra hne
  obtain ⟨P, hPmax, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨θ, t, ht, hθt⟩ := hP P hPmax
  apply hθt
  apply hle
  apply sub_mem_differentIdeal hR θ t ht
  intro h0
  apply hθt
  rw [h0]
  exact P.zero_mem
end PIW.CMDiscSq
