-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_hasProjectiveDimensionLE_zero_of_forall_not_isSMulRegular_aff001e5abe6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:42:32.021074+00:00
-- url     : https://prove2.me/submissions/1b2f7aa5-241d-487f-ad3d-a6f9d559ca53

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFDLocalization
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_AuslanderBuchsbaumDepthBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_ne_zero_mul_eq_zero_of_forall_not_isSMulRegular_d0c61a5979dd
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_free_of_hasProjectiveDimensionLT_of_mul_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open IsLocalRing CategoryTheory RingTheory.Sequence Ideal
open scoped Pointwise
universe u
variable {R : Type u} [CommRing R]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution [IsLocalRing R] [IsNoetherianRing R]
    (h : ∀ y ∈ maximalIdeal R, ¬ IsSMulRegular R y) (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] (k : ℕ) (hM : HasProjectiveDimensionLT (ModuleCat.of R M) (k + 1)) :
    HasProjectiveDimensionLE (ModuleCat.of R M) 0 := by
  obtain ⟨s, hs, hms⟩ := exists_ne_zero_mul_eq_zero_of_forall_not_isSMulRegular h
  have : Module.Free R M := GroundTheory.Arith.SchemeCoh.free_of_hasProjectiveDimensionLT_of_mul_eq_zero hs hms k M hM
  exact (projective_iff_hasProjectiveDimensionLE_zero _).mp (by
    rw [← IsProjective.iff_projective]; infer_instance)
end GroundTheory.Heights₂.Heights
