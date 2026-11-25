-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_form_mul_mem_twistMod_68a967b0a55b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:21:11.317569+00:00
-- url     : https://prove2.me/submissions/61d32151-4aed-40fd-879c-d673a36c7b0a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsClaimSeq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsZeroIdealChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimSeq

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
theorem _root_.solution {h : Poly k N} {d : ℕ} (hh : h.IsHomogeneous d) {c : ℤ} (I : Chart x)
    {o : Ω} (ho : o ∈ twistMod k x c I) : aeval x h * o ∈ twistMod k x (c + d) I := by
  refine Submodule.span_induction (p := fun o _ => aeval x h * o ∈ twistMod k x (c + d) I) ?_ ?_ ?_ ?_ ho
  · rintro _ ⟨f, s, e, e', hs, hf, hse, hc, rfl⟩
    exact Submodule.subset_span ⟨h * f, s, e, d + e', hs, hh.mul hf, hse, by push_cast; omega,
      by rw [map_mul, mul_div_assoc]⟩
  · rw [mul_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [mul_add]; exact Submodule.add_mem _ ha hb
  · intro a z _ hz
    have := Submodule.smul_mem _ a hz
    rw [chartRing_smul_def] at this ⊢
    rwa [mul_left_comm]
end GroundTheory.Heights₂.Heights.Kleiman
