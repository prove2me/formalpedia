-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_idealMod_mul_le_ff09cd164858
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:20:26.086252+00:00
-- url     : https://prove2.me/submissions/4d45ec0e-6e55-4ca0-98ed-65c9280a9406

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepThreeAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepThreeOnW
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThree

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
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (J J' : Ideal (Poly k N)) (I : Chart x) :
    idealMod (x := x) J I * idealMod (x := x) J' I ≤ idealMod (x := x) (J * J') I := by
  rw [idealMod, idealMod, Submodule.span_mul_span, Submodule.span_le]
  rintro _ ⟨_, ⟨f, s, e, hf, hs, hfe, hse, rfl⟩, _, ⟨f', s', e', hf', hs', hfe', hse', rfl⟩, rfl⟩
  refine Submodule.subset_span ⟨f * f', s * s', e + e', Ideal.mul_mem_mul hf hf', mul_mem hs hs',
    hfe.mul hfe', hse.mul hse', ?_⟩
  simp only [map_mul, div_mul_div_comm]
end GroundTheory.Heights₂.Heights.Kleiman
