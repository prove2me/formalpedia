-- Prove2me | solution 1 for PI.VolStabW.PositiveNearLattice.continuous_projInf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:18:58.079967+00:00
-- url     : https://prove2.me/submissions/c16f9c10-987b-45dc-a749-3038110b3aaf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_VolStabFromSWW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_ReciprocityTheory_GeneralLinearIntegers_AlgebraMapIntMemOint
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PosNear
import Theorems.Thm_PI_VolStabW_PositiveNearLattice_continuous_map_tens

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open PI.VolStabW.PositiveNearLattice
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
variable [FiniteDimensional F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
include b
namespace PI.VolStabW.PositiveNearLattice
theorem _root_.solution {M a : ℕ} :
    Continuous (projInf (F := F) (E := E) (M := M) (n := a)) :=
  continuous_pi fun x => continuous_pi fun i =>
    (continuous_map_tens b (fstA F) (by exact continuous_fst)).comp
      ((continuous_apply i).comp (continuous_apply x))
end PI.VolStabW.PositiveNearLattice
