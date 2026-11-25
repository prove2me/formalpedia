-- Prove2me | solution 1 for PI.VolSemiDirect.W.zero_mem_nbhdA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:54:19.512795+00:00
-- url     : https://prove2.me/submissions/e6791010-8d53-4762-884e-c5ac4bda2f49

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ClosedStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdicCompactDensity_ExistsNatLocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_EqZeroOfMemNbhdA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
  IsDedekindDomain.HeightOneSpectrum
open scoped TensorProduct Matrix
variable (F : Type) [Field F] [NumberField F]
namespace PI.VolSemiDirect.W
theorem _root_.solution : (0 : AF F) ∈ nbhdA F := by
  have h : algebraMap F (AF F) 0 ∈ nbhdA F := by
    refine ⟨?_, fun v => ?_⟩
    · show ‖algebraMap F (InfiniteAdeleRing F) 0‖ < 1
      rw [InfiniteAdeleRing.coe_norm_eq_abs_norm]
      simp
    · show (algebraMap F (FiniteAdeleRing (𝓞 F) F) 0) v ∈ v.adicCompletionIntegers F
      rw [map_zero]
      exact zero_mem _
  rwa [map_zero] at h
end PI.VolSemiDirect.W
