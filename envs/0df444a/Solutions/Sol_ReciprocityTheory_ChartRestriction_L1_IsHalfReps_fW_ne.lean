-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.IsHalfReps.fW_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:33:13.530967+00:00
-- url     : https://prove2.me/submissions/797276e5-06c5-4faf-9858-50e4ffeb52ae

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedDefs
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedHalf
import Theorems.Thm_Formalism_L2_Th1_F_pDerivZero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
variable {L : PeriodPair} {α : ℂ} {T : Finset ℂ}
namespace ReciprocityTheory.ChartRestriction.L1
namespace IsHalfReps
theorem _root_.solution (h : IsHalfReps L α T) {x : ℂ} (hx : x ∈ xsOf L T) : fW L.g₂ L.g₃ x ≠ 0 := by
  obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hx
  have hPL := h.notMem hP
  unfold fW
  rw [← L.derivWeierstrassP_sq P hPL]
  exact pow_ne_zero 2 (fun h0 => (h.1 P hP).2 ((pDerivZero L P hPL).mp h0))
end IsHalfReps
end ReciprocityTheory.ChartRestriction.L1
