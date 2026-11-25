-- Prove2me | solution 1 for PI.Dv.ProjBW.mem_zl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:47:31.497602+00:00
-- url     : https://prove2.me/submissions/1a7ec159-2d91-4f6d-b073-32191959335e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_HarderNarasimhan_FinalCor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MajorantVanishing_MajAtZeroRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjBW
open NumberField Formalism.HN
variable {R V E : Type*} [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
namespace PI.Dv.ProjBW
theorem _root_.solution (ρ : V →+ E) (N : Submodule R V) (u : E) : u ∈ zl ρ N ↔ ∃ z ∈ N, ρ z = u := Iff.rfl
end PI.Dv.ProjBW
