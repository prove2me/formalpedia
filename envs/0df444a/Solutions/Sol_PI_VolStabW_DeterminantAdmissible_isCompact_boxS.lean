-- Prove2me | solution 1 for PI.VolStabW.DeterminantAdmissible.isCompact_boxS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:27:16.763349+00:00
-- url     : https://prove2.me/submissions/41b6d60a-c424-4211-823c-228a318eb39f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DetAdmA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DetAdmB
import Theorems.Thm_PI_VolStabW_DeterminantAdmissible_boxS_eq
import Theorems.Thm_PI_VolStabW_DeterminantAdmissible_isCompact_finite_adele_box


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
  MeasurableSpace
open scoped TensorProduct ENNReal RestrictedProduct
variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]
namespace PI.VolStabW.DeterminantAdmissible
theorem _root_.solution {D : ι → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)} (hD : IsBoxD D) :
    IsCompact (boxS D) := by
  rw [boxS_eq]
  exact isCompact_univ_pi fun c => isCompact_finite_adele_box (fun v => (hD.1 c v).2)
    (by filter_upwards [hD.2] with v hv using hv c)
end PI.VolStabW.DeterminantAdmissible
