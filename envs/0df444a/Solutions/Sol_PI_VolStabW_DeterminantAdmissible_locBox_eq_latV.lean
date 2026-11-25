-- Prove2me | solution 1 for PI.VolStabW.DeterminantAdmissible.locBox_eq_latV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:56:33.267111+00:00
-- url     : https://prove2.me/submissions/298125f9-3235-47d3-9b4e-4c2374b71dc8

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
    (v : HeightOneSpectrum (𝓞 F)) (hv : ∀ c, D c v = (v.adicCompletionIntegers F : Set (Fv F v))) :
    locBox b D v = latV b v := by
  ext Y
  simp only [locBox, latV, mem_preimage, Set.mem_univ_pi, Set.mem_ofPred_eq]
  constructor
  · intro h x i k
    have h1 := h (x, i, k)
    rw [hv] at h1
    exact h1
  · intro h c
    rw [hv]
    exact h c.1 c.2.1 c.2.2
end PI.VolStabW.DeterminantAdmissible
