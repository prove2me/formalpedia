-- Prove2me | solution 1 for PI.VolStabSW.tensNA_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:18:43.903305+00:00
-- url     : https://prove2.me/submissions/11787701-1801-49cf-8848-bc1d3e764d47

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVNA
import Theorems.Thm_PI_VolStabSW_hasCOSub_of_lat
import Theorems.Thm_PI_VolStabSW_exists_pow_tendsto_zero_Fv
import Theorems.Thm_PI_VolStabSW_PositiveNearLattice_isClopen_latV
import Theorems.Thm_PI_VolStabSW_PositiveNearLattice_isCompact_latV


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Topology Filter
open scoped TensorProduct
namespace PI.VolStabSW
theorem _root_.solution : TensNA := by
  unfold TensNA InCtx
  intro F E _ _ _ _ _ σ _ M J _ _ _ a _ _ X0 hT _ v
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨π, h0, hπ⟩ := exists_pow_tendsto_zero_Fv v
  exact hasCOSub_of_lat (latSub (Module.finBasis F E) v a M)
    (PositiveNearLattice.isClopen_latV (b := Module.finBasis F E) (v := v) a M).isOpen
    (PositiveNearLattice.isCompact_latV (b := Module.finBasis F E) (v := v) a M) π h0 hπ
end PI.VolStabSW
