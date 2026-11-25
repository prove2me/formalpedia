-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_isIntegral_mul_of_fracMap_31178a133ad5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:39:56.110938+00:00
-- url     : https://prove2.me/submissions/b5e83330-e8a9-43d9-87bd-9da47a424b30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StMinimalPrimePlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_CurveNormalisationFiniteLemmas
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocalOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMinimalPrimePlace
import Theorems.Thm_GroundTheory_Arith_Toric_LowerBound_mul


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
open MvPolynomial ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.MinimalPrimePlace
variable {A B : Type*} [CommRing A] [CommRing B]
namespace GroundTheory.Heights₂.Heights.MinimalPrimePlace
theorem _root_.solution [IsDomain B] (π : A →+* B) (hπ : Function.Surjective π)
    (hker : RingHom.ker π ∈ minimalPrimes A) {e x : FractionRing A} (he1 : fracMap π hker e = 1)
    (hek : ∀ z, fracMap π hker z = 0 → e * z = 0) (hx : IsIntegral B (fracMap π hker x)) :
    IsIntegral A (e * x) := by
  obtain ⟨g, hg, hgx⟩ := hx
  obtain ⟨G, hGmap, -, hG⟩ := Polynomial.lifts_and_degree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective hπ g) hg
  refine ⟨Polynomial.X * G, Polynomial.monic_X.mul hG, ?_⟩
  have hz : e * Polynomial.aeval (e * x) G = 0 := by
    refine hek _ ?_
    rw [fracMap_aeval, hGmap, map_mul, he1, one_mul, Polynomial.aeval_def]
    exact hgx
  rw [Polynomial.aeval_def] at hz
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_X]
  linear_combination x * hz
end GroundTheory.Heights₂.Heights.MinimalPrimePlace
