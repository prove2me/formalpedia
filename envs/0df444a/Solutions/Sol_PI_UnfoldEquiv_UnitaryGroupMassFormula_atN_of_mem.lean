-- Prove2me | solution 1 for PI.UnfoldEquiv.UnitaryGroupMassFormula.atN_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:32:51.530892+00:00
-- url     : https://prove2.me/submissions/719ea9a3-8456-4c9d-a402-20073f8ba200

import Definitions.Def_Formalism_PeriodIntegrals_UnfoldEquiv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnfoldingEquivalence_ExtractFreeFillMatrix
import Theorems.Thm_PI_UnfoldEquiv_UnitaryGroupMassFormula_mem_Ufl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI.UnfoldEquiv PI.UnfoldEquiv.Loc
noncomputable section
open PI PI.UnfoldEquiv PI.UnfoldEquiv.UnitaryGroupMassFormula
variable {k : Type} [CommRing k]
namespace PI.UnfoldEquiv.UnitaryGroupMassFormula
theorem _root_.solution {n c i : ℕ} {v : Fin (n + c) → k} (hv : v ∈ Ufl k n c i) : atN v (n + i) = 0 := by
  unfold atN
  split_ifs with h
  · exact (mem_Ufl.1 hv) ⟨n + i, h⟩ (lt_irrefl _)
  · rfl
end PI.UnfoldEquiv.UnitaryGroupMassFormula
