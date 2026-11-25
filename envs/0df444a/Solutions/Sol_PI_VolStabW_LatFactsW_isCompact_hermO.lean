-- Prove2me | solution 1 for PI.VolStabW.LatFactsW.isCompact_hermO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:52:30.228864+00:00
-- url     : https://prove2.me/submissions/45c03cbb-5b15-4d70-bae2-3d1026f88db2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_UnifVSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHL
import Theorems.Thm_PI_VolStabW_PositiveNearLattice_isCompact_latV
import Theorems.Thm_PI_VolStabW_locallyCompact_Fv


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
open PI.VolStabW.LatFactsW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
namespace PI.VolStabW.LatFactsW
theorem _root_.solution (σ : E →ₐ[F] E) (a : ℕ) :
    IsCompact (hermO b v σ a : Set (HermR (Fv F v) σ a)) := by
  have := locallyCompact_Fv F v
  exact (isClosed_HermR (Fv F v) σ a).isClosedEmbedding_subtypeVal.isCompact_preimage
    (PositiveNearLattice.isCompact_latV b v a a)
end PI.VolStabW.LatFactsW
