-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionMulInj_mem_or_mem_3afecbde79cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:38:37.213896+00:00
-- url     : https://prove2.me/submissions/c8388e4d-4af4-4903-89a1-13de030b4b77

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionMulInjSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeOnWGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionMulInj
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionMulInj_mem_of_div_mem_idealMod_d458317619d4
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
theorem _root_.solution {pp : Ideal (Poly S N)} (hpp : pp.IsPrime) (hZ : primeOf (S := S) x ≤ pp)
    {I : Chart x} (hX : ∀ j ∈ I.1, (X j : Poly S N) ∉ pp) (a b : chartRing S x I)
    (h : (a : Ω) * b ∈ idealMod (x := x) pp I) :
    (a : Ω) ∈ idealMod (x := x) pp I ∨ (b : Ω) ∈ idealMod (x := x) pp I := by
  obtain ⟨F, m, e, hm, hF, hme, ha⟩ := a.2
  obtain ⟨F', m', e', hm', hF', hme', hb⟩ := b.2
  rw [ha, hb, div_mul_div_comm, ← map_mul, ← map_mul] at h
  have := mem_of_div_mem_idealMod hpp hZ hX (mul_mem hm hm') (hF.mul hF') (hme.mul hme') h
  refine (hpp.mem_or_mem this).imp (fun hF0 => ?_) (fun hF0 => ?_)
  · rw [ha]; exact Submodule.subset_span ⟨F, m, e, hF0, hm, hF, hme, rfl⟩
  · rw [hb]; exact Submodule.subset_span ⟨F', m', e', hF0, hm', hF', hme', rfl⟩
end GroundTheory.Heights₂.Heights.Kleiman.SectionMulInj
