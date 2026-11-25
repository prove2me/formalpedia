-- Prove2me | solution 1 for PI.VolStabW.DeterminantAdmissible.isClopen_locBox
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:56:02.363974+00:00
-- url     : https://prove2.me/submissions/5fb16ff7-f851-44a9-962e-ede90604570e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DetAdmB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DetAdmC

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
    (hD : IsBoxD D) (v : HeightOneSpectrum (𝓞 F)) : IsClopen (locBox b D v) :=
  (show IsClopen (Set.pi univ fun c => D c v) from ⟨isClosed_set_pi (fun c _ => (hD.1 c v).1.isClosed),
    isOpen_set_pi finite_univ (fun c _ => (hD.1 c v).1.isOpen)⟩).preimage (crdH b (Fv F v)).continuous
end PI.VolStabW.DeterminantAdmissible
