-- Prove2me | solution 1 for PI.VolStabW.FiniteThetaCoordinates.norm_crd_mulVec_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:49:40.505257+00:00
-- url     : https://prove2.me/submissions/6abcd349-4ba7-4d66-9d88-584555c3d9a5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_VolStabFromSWW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FinTheta
import Theorems.Thm_PI_VolStabW_FiniteThetaCoordinates_crd_mulVec

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
theorem _root_.solution {R K : Type} [CommRing R] [Algebra F R] [NormedField K]
    [IsUltrametricDist K] (φ : R →+* K)
    {M : ℕ} (m : Matrix (Fin M) (Fin M) (R ⊗[F] E)) (y : Fin M → R ⊗[F] E)
    (hA : ∀ i j p, ‖φ (crd b R (m i j) p)‖ ≤ 1) (hB : ∀ j q, ‖φ (crd b R (y j) q)‖ ≤ 1)
    (hC : ∀ p q k, ‖φ (algebraMap F R (b.repr (b p * b q) k))‖ ≤ 1) (i : Fin M) (k : Fin d) :
    ‖φ (crd b R ((m.mulVec y) i) k)‖ ≤ 1 := by
  rw [crd_mulVec]
  simp only [map_sum, map_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun j _ => ?_
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun p _ => ?_
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun q _ => ?_
  rw [norm_mul, norm_mul]
  exact mul_le_one₀ (mul_le_one₀ (hA i j p) (norm_nonneg _) (hB j q)) (norm_nonneg _) (hC p q k)
end PI.VolStabW.FiniteThetaCoordinates
