-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_RatLocalAffine_eq_zero_of_intCast_mul_eq_zero_bbfecc57b868
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:04:59.798858+00:00
-- url     : https://prove2.me/submissions/977566ca-6496-40de-a8dd-2a04fcdce654

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_RatLocalAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PRatLocalAffine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
open GroundTheory.Heights₂.Heights.Model.RatLocalAffine
namespace GroundTheory.Heights₂.Heights.Model.RatLocalAffine
theorem _root_.solution {A : Type} [CommRing A] (hA : (Int.castRingHom A).Flat)
    {n : ℤ} (hn : n ≠ 0) {a : A} (h : (n : A) * a = 0) : a = 0 := by
  have : Module.Flat ℤ A := RingHom.flat_algebraMap_iff.mp (by rwa [algebraMap_int_eq])
  have hr := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := A) (mem_nonZeroDivisors_of_ne_zero hn)
  apply hr
  show n • a = n • (0 : A)
  rw [smul_zero, zsmul_eq_mul]
  exact h
end GroundTheory.Heights₂.Heights.Model.RatLocalAffine
