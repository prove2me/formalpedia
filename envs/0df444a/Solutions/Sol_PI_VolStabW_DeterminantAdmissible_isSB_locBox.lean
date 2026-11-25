-- Prove2me | solution 1 for PI.VolStabW.DeterminantAdmissible.isSB_locBox
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:05:44.83254+00:00
-- url     : https://prove2.me/submissions/b3b4a213-40d2-4615-82cb-6f9a3cb1ddb8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DetAdmB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DetAdmC
import Theorems.Thm_PI_VolStabW_DeterminantAdmissible_isClopen_locBox
import Theorems.Thm_PI_VolStabW_DeterminantAdmissible_isCompact_locBox

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.DeterminantAdmissible
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Topology Filter Set
  PI.VolStabW.PositiveNearLattice MeasurableSpace PI.VolFromSW PI.VolStabW
open scoped TensorProduct ENNReal RestrictedProduct CompactlySupported
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E) {a M : ℕ}
variable {b}
namespace PI.VolStabW.DeterminantAdmissible
theorem _root_.solution {D : Fin a × Fin M × Fin d → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)}
    (hD : IsBoxD D) (v : HeightOneSpectrum (𝓞 F)) :
    IsSB ((locBox b D v).indicator (1 : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ)) :=
  ⟨(LocallyConstant.indicator (LocallyConstant.const _ (1 : ℂ)) (isClopen_locBox hD v)).isLocallyConstant,
    HasCompactSupport.intro' (isCompact_locBox hD v) (isClopen_locBox hD v).isClosed
      fun Y hY => Set.indicator_of_notMem hY _⟩
end PI.VolStabW.DeterminantAdmissible
