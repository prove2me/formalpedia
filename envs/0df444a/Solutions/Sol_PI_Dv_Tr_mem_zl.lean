-- Prove2me | solution 1 for PI.Dv.Tr.mem_zl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:36:22.481266+00:00
-- url     : https://prove2.me/submissions/e524210e-5496-492e-b8c3-c246c7a79120

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_FinalCor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_DegGeOfInj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.Tr
open Formalism.HN
variable {R : Type} [Ring R] {V W : Type} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
namespace PI.Dv.Tr
theorem _root_.solution {ρ : V →+ E} {L : Submodule R V} {u : E} : u ∈ zl ρ L ↔ ∃ x ∈ L, ρ x = u :=
  AddSubgroup.mem_map
end PI.Dv.Tr
