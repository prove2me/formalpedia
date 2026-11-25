-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_exists_eq_div_of_mem_idealMod_28db016029d7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:24:52.504958+00:00
-- url     : https://prove2.me/submissions/08e49787-a057-41de-ac2f-961769189bf3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsRestrQuotTorsionFree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFibreSectionsFlat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrQuotTorsionFree

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
theorem _root_.solution {J : Ideal (Poly S N)} {I : Chart x} {z : Ω}
    (hz : z ∈ idealMod J I) :
    ∃ (f m : Poly S N) (e : ℕ), f ∈ J ∧ m ∈ monos I.1 ∧ f.IsHomogeneous e ∧
      m.IsHomogeneous e ∧ z = aeval x f / aeval x m := by
  induction hz using Submodule.span_induction with
  | mem z hz => exact hz
  | zero =>
    exact ⟨0, 1, 0, J.zero_mem, one_mem _, isHomogeneous_zero _ _ _, isHomogeneous_one _ _, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨f, m, e, hf, hm, hfe, hme, rfl⟩ := ha
    obtain ⟨f', m', e', hf', hm', hfe', hme', rfl⟩ := hb
    refine ⟨f * m' + m * f', m * m', e + e', J.add_mem (J.mul_mem_right _ hf) (J.mul_mem_left _ hf'),
      mul_mem hm hm', (hfe.mul hme').add (hme.mul hfe'), hme.mul hme', ?_⟩
    rw [div_add_div _ _ (eval_ne_zero_of_mem_monos I hm) (eval_ne_zero_of_mem_monos I hm')]
    simp only [map_add, map_mul]
  | smul a z _ hz =>
    obtain ⟨f, m, e, hf, hm, hfe, hme, rfl⟩ := hz
    obtain ⟨g, n, d, hn, hg, hnd, ha⟩ := a.2
    refine ⟨g * f, n * m, d + e, J.mul_mem_left _ hf, mul_mem hn hm, hg.mul hfe, hnd.mul hme, ?_⟩
    rw [chartRing_smul_def, ha, map_mul, map_mul, div_mul_div_comm]
end GroundTheory.Heights₂.Heights.Kleiman
