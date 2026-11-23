-- Prove2me | solution 1 for PI.VolStabSW.TopoMeas.continuous_projV
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:00:14.035856+00:00
-- url     : https://prove2.me/submissions/23715f87-a04f-4b33-acc7-1c09865086e6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TopoAF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_MeasOrbSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TopoMeas
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
open PI PI.VolStabSW PI.VolStabSW.TopoMeas
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Filter Topology PI.VolFromSW
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
namespace PI.VolStabSW.TopoMeas
theorem _root_.solution {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    {M a : ℕ} : Continuous (projV (F := F) (E := E) v (M := M) (n := a)) :=
  continuous_pi fun x => continuous_pi fun i =>
    (PI.VolStabSW.PositiveNearLattice.continuous_map_tens b (evalV F v)
      (by exact RestrictedProduct.continuous_eval v)).comp
      ((continuous_apply i).comp (continuous_apply x))
end PI.VolStabSW.TopoMeas
