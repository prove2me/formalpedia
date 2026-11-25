-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_pow_div_mem_chartRingI_68ce525af692
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:05:59.877796+00:00
-- url     : https://prove2.me/submissions/b0044311-47a1-4113-a455-adffd4143cb4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CoordIdealIsMultiProjPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_EqZeroOrIsHomogeneousOfMemPolyPiece

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
open MvPolynomial
noncomputable section
variable (S : Type) [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω]
namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
theorem _root_.solution (x : Fin (N + 1) → Ω) (I : Kleiman.Chart x) (i₀ : Fin (N + 1))
    {s : Poly S N} (hs : s ∈ Kleiman.monos I.1) :
    ∃ e : ℕ, s.IsHomogeneous e ∧ x i₀ ^ e / aeval x s ∈ IndefiniteRowSideFullHecke.Kleiman.chartRingI S x I.1 := by
  induction hs using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨i, hi, rfl⟩ := ha
    refine ⟨1, isHomogeneous_X S i, ?_⟩
    rw [pow_one, aeval_X]
    exact Algebra.subset_adjoin ⟨i, hi, i₀, rfl⟩
  | one => exact ⟨0, isHomogeneous_one _ _, by simp⟩
  | mul a b _ _ ha hb =>
    obtain ⟨e, hae, hea⟩ := ha
    obtain ⟨e', hbe, heb⟩ := hb
    refine ⟨e + e', hae.mul hbe, ?_⟩
    have : x i₀ ^ (e + e') / aeval x (a * b) = (x i₀ ^ e / aeval x a) * (x i₀ ^ e' / aeval x b) := by
      rw [map_mul, pow_add, mul_div_mul_comm]
    rw [this]
    exact mul_mem hea heb
end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
