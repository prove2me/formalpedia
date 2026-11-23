-- Prove2me | solution 1 for PI.VolStabSW.PositiveNearLattice.continuous_projFin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:00:12.108806+00:00
-- url     : https://prove2.me/submissions/dad868a2-7cd2-43d6-a493-dc8eda421264

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibInfEx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_ReciprocityTheory_GeneralLinearIntegers_AlgebraMapIntMemOint
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_PosNear
import Theorems.Thm_PI_VolStabSW_PositiveNearLattice_continuous_map_tens

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
open PI.VolStabSW.PositiveNearLattice
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
variable [FiniteDimensional F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
include b
namespace PI.VolStabSW.PositiveNearLattice
theorem _root_.solution {M a : ℕ} :
    Continuous (projFin (F := F) (E := E) (M := M) (n := a)) :=
  continuous_pi fun x => continuous_pi fun i =>
    (continuous_map_tens b (sndA F) (by exact continuous_snd)).comp
      ((continuous_apply i).comp (continuous_apply x))
end PI.VolStabSW.PositiveNearLattice
