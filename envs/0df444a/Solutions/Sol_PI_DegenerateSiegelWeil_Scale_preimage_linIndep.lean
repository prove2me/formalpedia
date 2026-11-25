-- Prove2me | solution 1 for PI.DegenerateSiegelWeil.Scale.preimage_linIndep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:02:03.901672+00:00
-- url     : https://prove2.me/submissions/168c3875-f73b-44b7-837e-68e3e6eef2a4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SiegelWeilVolume_IsFibreFamilyReindex
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SiegelWeilVolume_MulTupApplyEqSum
import Theorems.Thm_PI_DegenerateSiegelWeil_Scale_mulTup_mul
import Theorems.Thm_PI_DegenerateSiegelWeil_Scale_mulTup_one
import Theorems.Thm_PI_DegenerateSiegelWeil_Scale_linIndep_mulTup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DegenerateSiegelWeil PI.DegenerateSiegelWeil.Scale
open MeasureTheory Topology Set Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolStabSW
open scoped ENNReal NNReal TensorProduct Matrix
variable {K : Type} [CommRing K] {n M : ℕ}
namespace PI.DegenerateSiegelWeil.Scale
theorem _root_.solution (D : (Matrix (Fin n) (Fin n) K)ˣ) :
    mulTup (M := M) (D : Matrix (Fin n) (Fin n) K) ⁻¹' {X | LinearIndependent K X} =
      {X | LinearIndependent K X} := by
  ext X
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  constructor
  · intro h
    have h1 := linIndep_mulTup D⁻¹ h
    rwa [mulTup_mul, Units.mul_inv, mulTup_one] at h1
  · exact linIndep_mulTup D
end PI.DegenerateSiegelWeil.Scale
