-- Prove2me | solution 1 for PI.VolStabSW.LatFactsW.isCompact_hermO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:18:01.822891+00:00
-- url     : https://prove2.me/submissions/7c8c6911-f6a1-470d-ad58-ef7aa77fe921

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_UnifVSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensHL
import Theorems.Thm_PI_VolStabSW_PositiveNearLattice_isCompact_latV
import Theorems.Thm_PI_VolStabSW_locallyCompact_Fv


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
open PI.VolStabSW.LatFactsW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
namespace PI.VolStabSW.LatFactsW
theorem _root_.solution (σ : E →ₐ[F] E) (a : ℕ) :
    IsCompact (hermO b v σ a : Set (HermR (Fv F v) σ a)) := by
  have := locallyCompact_Fv F v
  exact (isClosed_HermR (Fv F v) σ a).isClosedEmbedding_subtypeVal.isCompact_preimage
    (PositiveNearLattice.isCompact_latV b v a a)
end PI.VolStabSW.LatFactsW
