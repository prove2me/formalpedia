-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_idealMod_mem_form_fa180a587675
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:35:33.534582+00:00
-- url     : https://prove2.me/submissions/13207432-0231-445b-99ba-4d6f6ca6a989

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem

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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (J : Ideal (Poly S N)) (I : Chart x) {a : Ω} (ha : a ∈ idealMod J I) :
    ∃ (g s : Poly S N) (e : ℕ), g ∈ J ∧ s ∈ monos I.1 ∧ g.IsHomogeneous e ∧ s.IsHomogeneous e ∧
      a = aeval x g / aeval x s := by
  refine Submodule.span_induction (p := fun a _ => ∃ (g s : Poly S N) (e : ℕ), g ∈ J ∧
      s ∈ monos I.1 ∧ g.IsHomogeneous e ∧ s.IsHomogeneous e ∧ a = aeval x g / aeval x s)
    ?_ ?_ ?_ ?_ ha
  · rintro _ h; exact h
  · exact ⟨0, 1, 0, J.zero_mem, one_mem _, isHomogeneous_zero _ _ _, isHomogeneous_one _ _, by simp⟩
  · rintro _ _ - - ⟨g, s, e, hg, hs, hge, hse, rfl⟩ ⟨g', s', e', hg', hs', hge', hse', rfl⟩
    refine ⟨g * s' + s * g', s * s', e + e', J.add_mem (J.mul_mem_right _ hg) (J.mul_mem_left _ hg'),
      mul_mem hs hs', (hge.mul hse').add (hse.mul hge'), hse.mul hse', ?_⟩
    rw [div_add_div _ _ (eval_ne_zero_of_mem_monos I hs) (eval_ne_zero_of_mem_monos I hs')]
    simp only [map_add, map_mul]
  · rintro c _ - ⟨g, s, e, hg, hs, hge, hse, rfl⟩
    obtain ⟨f, t, d, ht, hf, htd, hc⟩ := c.2
    refine ⟨f * g, t * s, d + e, J.mul_mem_left _ hg, mul_mem ht hs, hf.mul hge, htd.mul hse, ?_⟩
    rw [chartRing_smul_def, hc, map_mul, map_mul, div_mul_div_comm]
end GroundTheory.Heights₂.Heights.Kleiman
