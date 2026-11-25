-- Prove2me | solution 1 for PI.VolStabSW.FiniteThetaCoordinates.crd_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:11:49.745884+00:00
-- url     : https://prove2.me/submissions/12532622-849f-4303-a14c-2cf74e597daf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibInfEx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FinTheta
import Theorems.Thm_PI_VolStabSW_FiniteThetaCoordinates_crd_sum
import Theorems.Thm_PI_VolStabSW_FiniteThetaCoordinates_crd_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW PI.VolStabSW.FiniteThetaCoordinates
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
namespace PI.VolStabSW.FiniteThetaCoordinates
theorem _root_.solution (R : Type) [CommRing R] [Algebra F R] {M : ℕ}
    (m : Matrix (Fin M) (Fin M) (R ⊗[F] E)) (y : Fin M → R ⊗[F] E) (i : Fin M) (k : Fin d) :
    crd b R ((m.mulVec y) i) k = ∑ j, ∑ p, ∑ q, crd b R (m i j) p * crd b R (y j) q *
      algebraMap F R (b.repr (b p * b q) k) := by
  simp only [Matrix.mulVec, dotProduct, crd_sum, crd_mul]
end PI.VolStabSW.FiniteThetaCoordinates
