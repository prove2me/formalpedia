-- Prove2me | solution 1 for PI.VolStabW.LatFactsW.isOpen_hermO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:35:11.621092+00:00
-- url     : https://prove2.me/submissions/409a8c39-7a2b-48c7-b55c-00c1c8c02be3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_UnifVSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHL
import Theorems.Thm_PI_VolStabW_PositiveNearLattice_isClopen_latV


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
theorem _root_.solution (σ : E →ₐ[F] E) (a : ℕ) : IsOpen (hermO b v σ a : Set (HermR (Fv F v) σ a)) :=
  continuous_subtype_val.isOpen_preimage _ (PositiveNearLattice.isClopen_latV b v a a).isOpen
end PI.VolStabW.LatFactsW
