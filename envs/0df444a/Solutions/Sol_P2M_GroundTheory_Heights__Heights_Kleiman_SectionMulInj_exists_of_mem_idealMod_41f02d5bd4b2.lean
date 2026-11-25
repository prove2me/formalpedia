-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionMulInj_exists_of_mem_idealMod_41f02d5bd4b2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:13:47.887826+00:00
-- url     : https://prove2.me/submissions/b866693a-b376-444d-afd5-d11567caaf4e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionMulInjSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeOnWGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionMulInj
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ChartInvertible_mul_6cd6215982f3


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
open GroundTheory.Heights₂.Heights.Kleiman.SectionMulInj
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionMulInj
theorem _root_.solution (J : Ideal (Poly S N)) (I : Chart x) {z : Ω} (hz : z ∈ idealMod (x := x) J I) :
    ∃ (G m : Poly S N) (e : ℕ), G ∈ J ∧ m ∈ monos I.1 ∧ G.IsHomogeneous e ∧ m.IsHomogeneous e ∧
      z = aeval x G / aeval x m := by
  induction hz using Submodule.span_induction with
  | mem z hz => exact hz
  | zero => exact ⟨0, 1, 0, J.zero_mem, one_mem _, isHomogeneous_zero _ _ _, isHomogeneous_one _ _, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨G, m, e, hG, hm, hGe, hme, rfl⟩ := ha
    obtain ⟨G', m', e', hG', hm', hGe', hme', rfl⟩ := hb
    refine ⟨G * m' + m * G', m * m', e + e', J.add_mem (J.mul_mem_right _ hG) (J.mul_mem_left _ hG'),
      mul_mem hm hm', (hGe.mul hme').add (hme.mul hGe'), hme.mul hme', ?_⟩
    rw [div_add_div _ _ (eval_ne_zero_of_mem_monos I hm) (eval_ne_zero_of_mem_monos I hm')]
    simp only [map_add, map_mul]
  | smul r a _ ha =>
    obtain ⟨F, m₀, e₀, hm₀, hF, hm₀e, hr⟩ := r.2
    obtain ⟨G, m, e, hG, hm, hGe, hme, rfl⟩ := ha
    refine ⟨F * G, m₀ * m, e₀ + e, J.mul_mem_left _ hG, mul_mem hm₀ hm, hF.mul hGe, hm₀e.mul hme, ?_⟩
    rw [chartRing_smul_def, hr, map_mul, map_mul, div_mul_div_comm]
end GroundTheory.Heights₂.Heights.Kleiman.SectionMulInj
