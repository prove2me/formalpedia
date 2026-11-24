-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_isLocalization_quot_8dc8f141d538
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:49.941568+00:00
-- url     : https://prove2.me/submissions/1a7e0dbc-c363-4103-972e-c83481895d8a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecChartQuot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.SpecChart
variable {A : Type*} [CommRing A] (W : Ideal A) [W.IsPrime] (P : Ideal A)
namespace GroundTheory.Heights₂.Heights.Vertical.SpecChart
theorem _root_.solution :
    IsLocalization (W.primeCompl.map (Ideal.Quotient.mk P))
      (Localization.AtPrime W ⧸ P.map (algebraMap A (Localization.AtPrime W))) := by
  rw [_root_.isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, s, hs, rfl⟩
    rw [Ideal.Quotient.algebraMap_quotient_map_quotient]
    exact (IsLocalization.map_units (Localization.AtPrime W) (⟨s, hs⟩ : W.primeCompl)).map _
  · intro z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective W.primeCompl x
    refine ⟨⟨Ideal.Quotient.mk P a, ⟨_, s.1, s.2, rfl⟩⟩, ?_⟩
    simp only [Ideal.Quotient.algebraMap_quotient_map_quotient, ← map_mul, IsLocalization.mk'_spec]
  · intro x y h
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Ideal.Quotient.algebraMap_quotient_map_quotient, Ideal.Quotient.algebraMap_quotient_map_quotient,
      Ideal.Quotient.eq, ← map_sub, IsLocalization.mem_map_algebraMap_iff W.primeCompl] at h
    obtain ⟨⟨⟨p, hp⟩, ⟨t, ht⟩⟩, h⟩ := h
    simp only at h
    rw [← map_mul, IsLocalization.eq_iff_exists W.primeCompl] at h
    obtain ⟨⟨u, hu⟩, h⟩ := h
    refine ⟨⟨Ideal.Quotient.mk P (u * t), ⟨u * t, W.primeCompl.mul_mem hu ht, rfl⟩⟩, ?_⟩
    simp only
    rw [← map_mul, ← map_mul, Ideal.Quotient.eq, ← mul_sub]
    have h' : u * ((a - b) * t) = u * p := h
    rw [show u * t * (a - b) = u * ((a - b) * t) by ring, h']
    exact P.mul_mem_left _ hp
end GroundTheory.Heights₂.Heights.Vertical.SpecChart
