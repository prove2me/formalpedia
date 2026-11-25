-- Prove2me | solution 1 for PI.VolStabW.FiniteThetaCoordinates.crd_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:33:31.580385+00:00
-- url     : https://prove2.me/submissions/e013f871-c020-4202-afd3-bc7f41581425

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_VolStabFromSWW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FinTheta
import Theorems.Thm_PI_VolStabW_FiniteThetaCoordinates_crd_sum
import Theorems.Thm_PI_VolStabW_FiniteThetaCoordinates_crd_mul

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
theorem _root_.solution (R : Type) [CommRing R] [Algebra F R] {M : ℕ}
    (m : Matrix (Fin M) (Fin M) (R ⊗[F] E)) (y : Fin M → R ⊗[F] E) (i : Fin M) (k : Fin d) :
    crd b R ((m.mulVec y) i) k = ∑ j, ∑ p, ∑ q, crd b R (m i j) p * crd b R (y j) q *
      algebraMap F R (b.repr (b p * b q) k) := by
  simp only [Matrix.mulVec, dotProduct, crd_sum, crd_mul]
end PI.VolStabW.FiniteThetaCoordinates
