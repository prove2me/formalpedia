-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SnapperHyperplaneMid_exists_eq_of_mem_idealMod_3bbfd4d1f565
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:20:58.658897+00:00
-- url     : https://prove2.me/submissions/02a63ac8-bee5-4dbd-af6f-fc3cd704a0cb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperHyperplane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperDevissage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperHyperplaneMid

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
open GroundTheory.Heights₂.Heights.Kleiman.SnapperHyperplaneMid
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.SnapperHyperplaneMid
theorem _root_.solution {pp : Ideal (Poly k N)} {I : Chart x} {z : Ω} (hz : z ∈ idealMod pp I) :
    ∃ (g s : Poly k N) (e : ℕ), g ∈ pp ∧ s ∈ monos I.1 ∧ g.IsHomogeneous e ∧ s.IsHomogeneous e ∧
      z = aeval x g / aeval x s := by
  induction hz using Submodule.span_induction with
  | mem z hz => exact hz
  | zero =>
    exact ⟨0, 1, 0, pp.zero_mem, one_mem _, isHomogeneous_zero _ _ _, isHomogeneous_one _ _, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨g, s, e, hg, hs, hge, hse, rfl⟩ := ha
    obtain ⟨g', s', e', hg', hs', hge', hse', rfl⟩ := hb
    refine ⟨g * s' + s * g', s * s', e + e', pp.add_mem (pp.mul_mem_right _ hg) (pp.mul_mem_left _ hg'),
      mul_mem hs hs', (hge.mul hse').add (hse.mul hge'), hse.mul hse', ?_⟩
    rw [div_add_div _ _ (eval_ne_zero_of_mem_monos I hs) (eval_ne_zero_of_mem_monos I hs')]
    simp only [map_add, map_mul]
  | smul a b _ hb =>
    obtain ⟨f, s₀, e₀, hs₀, hf, hse₀, ha⟩ := a.2
    obtain ⟨g, s, e, hg, hs, hge, hse, rfl⟩ := hb
    refine ⟨f * g, s₀ * s, e₀ + e, pp.mul_mem_left _ hg, mul_mem hs₀ hs, hf.mul hge, hse₀.mul hse, ?_⟩
    rw [chartRing_smul_def, ha, map_mul, map_mul, div_mul_div_comm]
end GroundTheory.Heights₂.Heights.Kleiman.SnapperHyperplaneMid
