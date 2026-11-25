-- Prove2me | solution 1 for PI.VolStabSW.isCOBasis_latSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:18:41.710099+00:00
-- url     : https://prove2.me/submissions/249e8d5a-dbd2-46e8-bca9-e85e83ddd2ea

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVNA
import Theorems.Thm_PI_VolStabSW_exists_pow_tendsto_zero_Fv
import Theorems.Thm_PI_VolStabSW_isCOBasis_scaled
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
theorem _root_.solution {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    [FiniteDimensional F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
    (v : HeightOneSpectrum (𝓞 F)) (a M : ℕ) :
    IsCOBasis (scaledB (Fv F v) (latSub b v a M)) := by
  obtain ⟨π, h0, hπ⟩ := exists_pow_tendsto_zero_Fv v
  exact isCOBasis_scaled (latSub b v a M)
    (PositiveNearLattice.isClopen_latV (b := b) (v := v) a M).isOpen
    (PositiveNearLattice.isCompact_latV (b := b) (v := v) a M) π h0 hπ
end PI.VolStabSW
