-- Prove2me | solution 1 for PI.VolStabW.DeterminantAdmissible.psiH_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:57:42.837245+00:00
-- url     : https://prove2.me/submissions/f91a2965-3c7a-43e5-a445-48a576b2b006

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DetAdmB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DetAdmC
import Theorems.Thm_PI_VolStabW_PositiveNearLattice_crd_map


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
  {a M : ℕ}
namespace PI.VolStabW.DeterminantAdmissible
theorem _root_.solution (X : Fin a → Fin M → AF F ⊗[F] E) :
    (psiH F E a M X).1 = crdH (Module.finBasis F E) (Ainf F) (projInf X) := by
  funext c
  exact (crd_map (Module.finBasis F E) (fstA F) (X c.1 c.2.1) c.2.2).symm
end PI.VolStabW.DeterminantAdmissible
