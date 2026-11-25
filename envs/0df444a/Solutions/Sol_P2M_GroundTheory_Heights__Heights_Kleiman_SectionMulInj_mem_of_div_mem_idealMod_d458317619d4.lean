-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionMulInj_mem_of_div_mem_idealMod_d458317619d4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:26:50.817535+00:00
-- url     : https://prove2.me/submissions/ed9a7dd2-6b9b-4e49-9f75-23016d4d5b6c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionMulInjSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeOnWGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionMulInj
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionMulInj_exists_of_mem_idealMod_41f02d5bd4b2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionMulInj_not_mem_of_mem_monos_0bf0f5564de5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ChartInvertible_mul_6cd6215982f3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_primeOf_of_isHomogeneous_ce26327b239d


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
theorem _root_.solution {pp : Ideal (Poly S N)} (hpp : pp.IsPrime) (hZ : primeOf (S := S) x ≤ pp)
    {I : Chart x} (hX : ∀ j ∈ I.1, (X j : Poly S N) ∉ pp) {F m : Poly S N} {e : ℕ} (hm : m ∈ monos I.1)
    (hF : F.IsHomogeneous e) (hme : m.IsHomogeneous e) (h : aeval x F / aeval x m ∈ idealMod (x := x) pp I) :
    F ∈ pp := by
  obtain ⟨G, m', e', hG, hm', hGe, hme', heq⟩ := exists_of_mem_idealMod pp I h
  have h0 := eval_ne_zero_of_mem_monos I hm
  have h0' := eval_ne_zero_of_mem_monos I hm'
  have hdiff : F * m' - m * G ∈ primeOf (S := S) x := by
    have hhom : (F * m' - m * G).IsHomogeneous (e + e') := (hF.mul hme').sub (hme.mul hGe)
    rw [mem_primeOf_of_isHomogeneous x hhom, map_sub, map_mul, map_mul, sub_eq_zero]
    rw [div_eq_div_iff h0 h0'] at heq
    rw [heq, mul_comm]
  have hFm : F * m' ∈ pp := by
    have := pp.add_mem (hZ hdiff) (pp.mul_mem_left m hG)
    rwa [sub_add_cancel] at this
  exact (hpp.mem_or_mem hFm).resolve_right (not_mem_of_mem_monos hpp hX hm')
end GroundTheory.Heights₂.Heights.Kleiman.SectionMulInj
