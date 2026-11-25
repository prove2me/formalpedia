-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_finprod_iSup_algebraMap_int_cb052d817af6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:32:07.667247+00:00
-- url     : https://prove2.me/submissions/2e91987f-9357-4ca6-944b-4c51b527d78d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CardEmbeddingsRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FieldChange

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
open NumberField Module
noncomputable section
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {ι : Type*} [Finite ι] {y : ι → 𝓞 K} (hy : y ≠ 0) :
    ∏ᶠ w : FinitePlace L, ⨆ i, w (algebraMap K L (y i)) =
      (∏ᶠ v : FinitePlace K, ⨆ i, v (y i)) ^ finrank K L := by
  set y' : ι → 𝓞 L := fun i ↦ algebraMap (𝓞 K) (𝓞 L) (y i) with hy'
  have hinj : Function.Injective (algebraMap (𝓞 K) (𝓞 L)) := by
    intro a b hab
    have h1 : algebraMap K L (a : K) = algebraMap K L (b : K) := congrArg (fun t : 𝓞 L ↦ (t : L)) hab
    exact RingOfIntegers.ext ((algebraMap K L).injective h1)
  have hy'0 : y' ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
    exact Function.ne_iff.mpr ⟨i, fun h ↦ hi (hinj (h.trans (map_zero _).symm))⟩
  have hK := absNorm_mul_finprod_finitePlace_eq_one (K := K) hy
  have hL := absNorm_mul_finprod_finitePlace_eq_one (K := L) hy'0
  have hspan : Ideal.span (Set.range y') =
      (Ideal.span (Set.range y)).map (algebraMap (𝓞 K) (𝓞 L)) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  rw [hspan, Ideal.absNorm_algebraMap, ← IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L] at hL
  have hL' : ∏ᶠ w : FinitePlace L, ⨆ i, w (algebraMap K L (y i)) =
      ∏ᶠ w : FinitePlace L, ⨆ i, w (y' i) := rfl
  rw [hL']
  set N : ℝ := ((Ideal.span (Set.range y)).absNorm : ℝ)
  have hN : N ≠ 0 := by
    intro h
    rw [h, zero_mul] at hK
    exact zero_ne_one hK
  push_cast at hL
  rw [eq_inv_of_mul_eq_one_right hL, eq_inv_of_mul_eq_one_right hK, inv_pow]
end GroundTheory.Heights₂.Heights
