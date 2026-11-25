-- Prove2me | solution 1 for QPK.prodSet_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:06:05.43372+00:00
-- url     : https://prove2.me/submissions/49a689d9-db4e-4107-869e-88081b183807

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_HaarExist
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_ProdSetIsClosed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal Pointwise
open QPK
variable {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
namespace QPK
theorem _root_.solution (N H : Set G) : prodSet N H = N * H := by
  ext s
  simp only [prodSet, Set.mem_setOf_eq, Set.mem_mul]
  constructor
  · rintro ⟨m, hm, h, hh, rfl⟩
    exact ⟨m, hm, h, hh, rfl⟩
  · rintro ⟨m, hm, h, hh, rfl⟩
    exact ⟨m, hm, h, hh, rfl⟩
end QPK
