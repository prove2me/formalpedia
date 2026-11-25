-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.SplitGL.p1_sigma_eq_p2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:36:16.8873+00:00
-- url     : https://prove2.me/submissions/97d5d34d-2223-4594-8dd2-afaa9d1aed8f

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
theorem _root_.solution (r : R) : p1 π (σ r) = p2 π r := by
  show (π (σ r)).1 = (π r).2
  rw [hπ]
  rfl
end PI.UnitaryGroupMassFormula.AdIndexEq.SplitGL
