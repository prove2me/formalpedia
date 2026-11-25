-- Prove2me | solution 1 for PI.VolStabW.FiniteThetaCoordinates.crd_incl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:04:01.184516+00:00
-- url     : https://prove2.me/submissions/9cafe039-37b9-4932-849c-e9f447374d5f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_VolStabFromSWW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FinTheta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.FiniteThetaCoordinates
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
namespace PI.VolStabW.FiniteThetaCoordinates
theorem _root_.solution (R : Type) [CommRing R] [Algebra F R] (x : E) (k : Fin d) :
    crd b R (inclR R x) k = algebraMap F R (b.repr x k) := by
  simp [crd, inclR, Algebra.TensorProduct.basis_repr_tmul]
end PI.VolStabW.FiniteThetaCoordinates
