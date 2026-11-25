-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.SplitGL.snd_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:36:19.574446+00:00
-- url     : https://prove2.me/submissions/20bb4d93-5fb4-4b05-a867-720342ea38a4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Commensurated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_SplitGL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq PI.UnitaryGroupMassFormula.AdIndexEq.SplitGL
open Matrix
variable {R k : Type} [CommRing R] [Field k] {n : Type} [Fintype n] [DecidableEq n]
variable (σ : R →+* R) (π : R ≃+* k × k) (hπ : ∀ r, π (σ r) = (π r).swap)
include hπ
namespace PI.UnitaryGroupMassFormula.AdIndexEq.SplitGL
theorem _root_.solution (r : R) : p2 π (σ r) = p1 π r := by
  show (π (σ r)).2 = (π r).1
  rw [hπ]
  rfl
end PI.UnitaryGroupMassFormula.AdIndexEq.SplitGL
