-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ChartSpecCount_exists_pow_mul_eq_map_6a642e1766c5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:14:05.396034+00:00
-- url     : https://prove2.me/submissions/d4096629-9691-477a-ad41-8c902627e7ca

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StChartPrimElt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StLocAwaySpec
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StChartSpecCount
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartSpecCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open Polynomial
open GroundTheory.Heights₂.Heights.Inter.ChartSpecCount
namespace GroundTheory.Heights₂.Heights.Inter.ChartSpecCount
theorem _root_.solution {R : Type*} [CommRing R] (E : R) {Q : Type*}
    (F : MvPolynomial Q (Localization.Away E)) :
    ∃ (n : ℕ) (F' : MvPolynomial Q R),
      MvPolynomial.map (algebraMap R (Localization.Away E)) F' =
        MvPolynomial.C (algebraMap R (Localization.Away E) (E ^ n)) * F := by
  induction F using MvPolynomial.induction_on with
  | C a =>
    obtain ⟨n, b, hb⟩ := IsLocalization.Away.surj E a
    refine ⟨n, MvPolynomial.C b, ?_⟩
    rw [MvPolynomial.map_C, ← MvPolynomial.C_mul, map_pow, mul_comm, hb]
  | add F G hF hG =>
    obtain ⟨n, F', hF'⟩ := hF
    obtain ⟨k, G', hG'⟩ := hG
    refine ⟨n + k, MvPolynomial.C (E ^ k) * F' + MvPolynomial.C (E ^ n) * G', ?_⟩
    simp only [map_add, map_mul, MvPolynomial.map_C, hF', hG', pow_add, map_pow]
    ring
  | mul_X F i hF =>
    obtain ⟨n, F', hF'⟩ := hF
    exact ⟨n, F' * MvPolynomial.X i, by rw [map_mul, MvPolynomial.map_X, hF', mul_assoc]⟩
end GroundTheory.Heights₂.Heights.Inter.ChartSpecCount
