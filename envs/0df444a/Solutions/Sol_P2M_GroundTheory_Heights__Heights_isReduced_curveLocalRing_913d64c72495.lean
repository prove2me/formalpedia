-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isReduced_curveLocalRing_913d64c72495
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:13:10.581188+00:00
-- url     : https://prove2.me/submissions/4cc0954b-7fbc-458b-9ae0-7ab2edf9b66b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_LocalIntegralClosureChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_CurveNormalisationFiniteLemmas

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
open MvPolynomial ComplexSets FieldNumbers
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (h : IsRadicalAt I q) : IsReduced (curveLocalRing I q) := by
  refine (Ideal.isRadical_iff_quotient_reduced _).1 ?_
  rw [Ideal.IsRadical, ← IsLocalization.map_radical (RingHom.ker (eval q)).primeCompl]
  refine Ideal.map_le_iff_le_comap.2 fun f hf ↦ ?_
  obtain ⟨s, hs, hsf⟩ := h f hf
  have hu : IsUnit (algebraMap _ (Localization.AtPrime (RingHom.ker (eval q))) s) :=
    IsLocalization.map_units _ (⟨s, fun h' ↦ hs (RingHom.mem_ker.1 h')⟩ : (RingHom.ker (eval q)).primeCompl)
  exact (Ideal.unit_mul_mem_iff_mem _ hu).1 (by rw [← map_mul]; exact Ideal.mem_map_of_mem _ hsf)
end GroundTheory.Heights₂.Heights
