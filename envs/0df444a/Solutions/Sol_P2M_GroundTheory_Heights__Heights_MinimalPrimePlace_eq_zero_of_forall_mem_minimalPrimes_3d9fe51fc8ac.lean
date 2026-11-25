-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_eq_zero_of_forall_mem_minimalPrimes_3d9fe51fc8ac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:28:15.76779+00:00
-- url     : https://prove2.me/submissions/61ebdc8a-f510-4df0-804e-114c5411bd3c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StMinimalPrimePlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_CurveNormalisationFiniteLemmas
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocalOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMinimalPrimePlace

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
theorem _root_.solution [IsReduced A] {x : A} (h : ∀ q ∈ minimalPrimes A, x ∈ q) :
    x = 0 := by
  have hx : x ∈ sInf (minimalPrimes A) := Submodule.mem_sInf.2 h
  have hrad : sInf (minimalPrimes A) = (⊥ : Ideal A).radical := Ideal.sInf_minimalPrimes
  rw [hrad] at hx
  obtain ⟨k, hk⟩ := hx
  exact IsNilpotent.eq_zero ⟨k, Ideal.mem_bot.1 hk⟩
end GroundTheory.Heights₂.Heights.MinimalPrimePlace
