-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_isFrac_mul_3dd39e0d5705
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:14:16.788879+00:00
-- url     : https://prove2.me/submissions/23e488c4-2d7d-48d9-a3f0-63515ea922ef

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
theorem _root_.solution {x : Fin (N + 1) → Ω} {c : ℤ} {I : Finset (Fin (N + 1))} {z : Ω}
    {t : Poly S N × Poly S N × ℕ × ℕ} {g u : Poly S N} {d : ℕ} (hu : u ∈ monos I)
    (hg : g.IsHomogeneous d) (hud : u.IsHomogeneous d) (h : IsFrac x c I z t) :
    IsFrac x c I (aeval x g / aeval x u * z) (g * t.1, u * t.2.1, d + t.2.2.1, d + t.2.2.2) := by
  obtain ⟨f, s, e, e'⟩ := t
  obtain ⟨hs, hf, hse, hc, rfl⟩ := h
  dsimp only at hs hf hse hc ⊢
  refine ⟨mul_mem hu hs, hg.mul hf, hud.mul hse, by push_cast; omega, ?_⟩
  simp only [map_mul, div_mul_div_comm]
end GroundTheory.Heights₂.Heights.Kleiman.RestrictTwist
