-- Prove2me | solution 1 for PI.VolSemiDirect.W.Cj.inG_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:32:36.444874+00:00
-- url     : https://prove2.me/submissions/ff5a566f-0dae-410b-9472-95533713864e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_CjDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_GlGeneratedTransvectionsDiag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.Cj
open Matrix
variable {A : Type} [CommRing A] {k : ℕ}
namespace PI.VolSemiDirect.W.Cj
theorem _root_.solution {M N : Matrix (Fin k) (Fin k) A} (hM : InG M) (hN : InG N) : InG (M * N) := by
  obtain ⟨g, hg, rfl⟩ := hM
  obtain ⟨h, hh, rfl⟩ := hN
  exact ⟨g * h, Subgroup.mul_mem _ hg hh, Units.val_mul _ _⟩
end PI.VolSemiDirect.W.Cj
