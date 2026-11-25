-- Prove2me | solution 1 for PI.VolStabSW.PositiveNearLattice.isSB_latV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:18:32.575393+00:00
-- url     : https://prove2.me/submissions/ccd3848e-95cd-4692-8b53-e8008e51cb65

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibInfEx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_ReciprocityTheory_GeneralLinearIntegers_AlgebraMapIntMemOint
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_PosNear
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
open PI.VolStabSW.PositiveNearLattice
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
namespace PI.VolStabSW.PositiveNearLattice
theorem _root_.solution (a M : ℕ) :
    IsSB ((latV (M := M) (n := a) b v).indicator (fun _ => (1 : ℂ))) := by
  refine ⟨(LocallyConstant.indicator (LocallyConstant.const _ (1 : ℂ))
    (isClopen_latV b v a M)).isLocallyConstant, ?_⟩
  exact HasCompactSupport.intro' (isCompact_latV b v a M) (isClopen_latV b v a M).isClosed
    fun Y hY => Set.indicator_of_notMem hY _
end PI.VolStabSW.PositiveNearLattice
