-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_Domination_birational_clear_005110b90e73
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:09:55.977838+00:00
-- url     : https://prove2.me/submissions/a29d99ba-aa4a-4f50-be3d-5579266bc9fc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PDomination

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.Domination
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N N' : ℕ}
  {x : Fin (N + 1) → Ω} {x' : Fin (N' + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.Domination
theorem _root_.solution (hbir : IsBirationalPt S x) {i : Fin (N + 1)} (hi : x i ≠ 0) (g : Ω) :
    ∃ d ∈ {y | ∃ (f : Poly S N) (e : ℕ), f.IsHomogeneous e ∧ aeval x f ≠ 0 ∧ aeval x f / x i ^ e = y},
      d * g ∈ chartRing S x (singleChart hi) := by
  obtain ⟨I, a, b, ⟨f, s, e, hs, hf, hse, rfl⟩, ⟨f', s', e', hs', hf', hse', rfl⟩, hb0, hgb⟩ := hbir g
  have hs0 := eval_ne_zero_of_mem_monos I hs
  have hs0' := eval_ne_zero_of_mem_monos I hs'
  have hf'0 : aeval x f' ≠ 0 := by
    intro h
    apply hb0
    rw [h, zero_div]
  have key : aeval x s * aeval x f' * g = aeval x f * aeval x s' := by
    calc aeval x s * aeval x f' * g
        = aeval x s * aeval x s' * (g * (aeval x f' / aeval x s')) := by
          field_simp
      _ = aeval x s * aeval x s' * (aeval x f / aeval x s) := by rw [hgb]
      _ = aeval x f * aeval x s' := by
          field_simp
  refine ⟨aeval x (s * f') / x i ^ (e + e'),
    ⟨s * f', e + e', hse.mul hf', by rw [map_mul]; exact mul_ne_zero hs0 hf'0, rfl⟩, ?_⟩
  refine ⟨f * s', X i ^ (e + e'), e + e', pow_mem (X_mem_monos (Finset.mem_singleton_self i)) _,
    hf.mul hse', isHomogeneous_X_pow i _, ?_⟩
  rw [map_pow, aeval_X, map_mul, map_mul, div_mul_eq_mul_div, key]
end GroundTheory.Heights₂.Heights.Kleiman.Domination
