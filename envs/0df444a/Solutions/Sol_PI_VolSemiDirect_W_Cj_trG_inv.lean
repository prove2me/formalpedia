-- Prove2me | solution 1 for PI.VolSemiDirect.W.Cj.trG_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:00:50.4589+00:00
-- url     : https://prove2.me/submissions/7f7b2e8b-f69d-4a58-ad53-fce75e424a4d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_MapPhiOfModM
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_NnrealEqOneOfMulSelf
import Theorems.Thm_PI_VolSemiDirect_W_Cj_trG_mul
import Theorems.Thm_PI_VolSemiDirect_W_Cj_trG_one

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
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Measure
open scoped NNReal
variable {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A] [MeasurableSpace A]
  [BorelSpace A] {k : ℕ}
namespace PI.VolSemiDirect.W.Cj
theorem _root_.solution (X : GL (Fin k) A) : trG X⁻¹ = (trG X)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← trG_mul, mul_inv_cancel, trG_one]
end PI.VolSemiDirect.W.Cj
