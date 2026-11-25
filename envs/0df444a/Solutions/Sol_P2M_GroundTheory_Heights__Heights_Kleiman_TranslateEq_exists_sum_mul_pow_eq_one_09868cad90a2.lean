-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_exists_sum_mul_pow_eq_one_09868cad90a2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:28:48.302986+00:00
-- url     : https://prove2.me/submissions/47bdc182-d870-4cd1-b73d-50723db456bb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwinEqBundleLocal

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
variable (A : Subalgebra S Ω) {k : ℕ} (f c : Fin k → Ω)
namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
theorem _root_.solution (hf : ∀ l, f l ∈ A) (hc : ∀ l, c l ∈ A) (hs : ∑ l, c l * f l = 1)
    (n : ℕ) : ∃ d : Fin k → Ω, (∀ l, d l ∈ A) ∧ ∑ l, d l * f l ^ n = 1 := by
  let f' : Fin k → A := fun l => ⟨f l, hf l⟩
  have htop : Ideal.span (Set.range f') = ⊤ := by
    rw [Ideal.eq_top_iff_one, Ideal.span, Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun l => ⟨c l, hc l⟩, Subtype.ext ?_⟩
    simpa [f'] using hs
  have h1 := Ideal.span_pow_eq_top _ htop n
  rw [← Set.range_comp, Ideal.eq_top_iff_one, Ideal.span, Submodule.mem_span_range_iff_exists_fun] at h1
  obtain ⟨d, hd⟩ := h1
  refine ⟨fun l => d l, fun l => (d l).2, ?_⟩
  have := congrArg Subtype.val hd
  simpa [f'] using this
end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
