-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_mul_span_eq_one_of_le_d361b21de1fd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:05:59.157358+00:00
-- url     : https://prove2.me/submissions/883bad78-ec02-4c89-9d30-1f2f61d4beba

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwinEqBundleLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_span_span_of_le_5980be65a218

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
open scoped Pointwise
variable {S : Type*} [CommRing S] {Ω : Type*} [Field Ω] [Algebra S Ω]
variable {A B : Subalgebra S Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
theorem _root_.solution (hAB : A ≤ B) {L L' : Submodule A Ω} (h : L * L' = 1) :
    Submodule.span B (L : Set Ω) * Submodule.span B (L' : Set Ω) = 1 := by
  rw [Submodule.span_mul_span]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨p, hp, q, hq, rfl⟩
    have hpq : p * q ∈ L * L' := Submodule.mul_mem_mul hp hq
    rw [h, Submodule.mem_one] at hpq
    obtain ⟨a, ha⟩ := hpq
    exact Submodule.mem_one.2 ⟨⟨a, hAB a.2⟩, ha⟩
  · rw [Submodule.one_le]
    have h1 : (1 : Ω) ∈ L * L' := h ▸ Submodule.mem_one.2 ⟨1, map_one _⟩
    rw [Submodule.mul_eq_span_mul_set] at h1
    exact (span_span_of_le hAB ((L : Set Ω) * (L' : Set Ω))).le (Submodule.subset_span h1)
end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
