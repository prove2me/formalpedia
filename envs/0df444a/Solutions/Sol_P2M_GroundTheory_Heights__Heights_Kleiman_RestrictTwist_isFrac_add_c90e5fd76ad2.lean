-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_isFrac_add_c90e5fd76ad2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:14:14.663036+00:00
-- url     : https://prove2.me/submissions/c5f01e9f-814e-430d-b9be-7c7d4a06e43b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrictTwist

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
open GroundTheory.Heights₂.Heights.Kleiman.RestrictTwist
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {K' : Type w} [Field K'] [Algebra S K']
namespace GroundTheory.Heights₂.Heights.Kleiman.RestrictTwist
theorem _root_.solution {x : Fin (N + 1) → Ω} {c : ℤ} {I : Finset (Fin (N + 1))} {z z' : Ω}
    {t t' : Poly S N × Poly S N × ℕ × ℕ} (hI : ∀ s ∈ monos (S := S) I, aeval x s ≠ 0)
    (h : IsFrac x c I z t) (h' : IsFrac x c I z' t') :
    IsFrac x c I (z + z')
      (t.1 * t'.2.1 + t.2.1 * t'.1, t.2.1 * t'.2.1, t.2.2.1 + t'.2.2.1, t.2.2.2 + t'.2.2.1) := by
  obtain ⟨f, s, e, e'⟩ := t
  obtain ⟨f', s', d, d'⟩ := t'
  obtain ⟨hs, hf, hse, hc, rfl⟩ := h
  obtain ⟨hs', hf', hse', hc', rfl⟩ := h'
  dsimp only at hs hf hse hc hs' hf' hse' hc' ⊢
  refine ⟨mul_mem hs hs', (hf.mul hse').add ?_, hse.mul hse', by push_cast; omega, ?_⟩
  · have hdeg : e + d' = e' + d := by omega
    rw [← hdeg]; exact hse.mul hf'
  · simp only [map_add, map_mul]
    rw [div_add_div _ _ (hI s hs) (hI s' hs')]
end GroundTheory.Heights₂.Heights.Kleiman.RestrictTwist
