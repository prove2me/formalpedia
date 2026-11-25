-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFiltration_Point_proof_d22f31b4a055
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:54:08.147978+00:00
-- url     : https://prove2.me/submissions/9c1d39cd-25d4-475a-bee2-06b686119857

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationPoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ideal_eq_of_isHomogeneous_48fc59908dff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_chartPrime_iff_8a48624344f9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_coe_aeval_ratio__8300418e303d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_homogeneousComponent_mem_primeOf_077b7ab281b2
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
universe u v w
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace PrimeFiltration.Point
theorem _root_.solution : PrimeFiltration.Point.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x pp hpp hhom hle j hj hX
  refine ⟨?_, ?_⟩
  · rw [Ideal.isPrime_iff]
    refine ⟨?_, ?_⟩
    · rw [Ideal.ne_top_iff_one]
      rw [mem_chartPrime_iff (f := 1) (s := 1) hj hle hX (isHomogeneous_one _ _) (one_mem _)
        (isHomogeneous_one _ _) (by simp)]
      exact (Ideal.ne_top_iff_one pp).mp hpp.ne_top
    · intro a b hab
      obtain ⟨f, s, e, hs, hf, hse, ha⟩ := a.2
      obtain ⟨g, t, d, ht, hg, htd, hb⟩ := b.2
      have hab' : ((a * b : chartRing S x (singleChart hj)) : Ω) = aeval x (f * g) / aeval x (s * t) := by
        rw [Subalgebra.coe_mul, ha, hb, map_mul, map_mul, div_mul_div_comm]
      rw [mem_chartPrime_iff hj hle hX (hf.mul hg) (mul_mem hs ht) (hse.mul htd) hab'] at hab
      rw [mem_chartPrime_iff hj hle hX hf hs hse ha, mem_chartPrime_iff hj hle hX hg ht htd hb]
      exact hpp.mem_or_mem hab
  · intro K' _ _ ψ hker
    apply ideal_eq_of_isHomogeneous (fun p hp d => homogeneousComponent_mem_primeOf _ hp d) hhom
    intro f e hf
    rw [mem_primeOf_of_isHomogeneous _ hf, ← comp_aeval_apply, ← RingHom.mem_ker, hker]
    exact mem_chartPrime_iff hj hle hX hf (pow_mem (X_mem_monos (Finset.mem_singleton_self j)) e)
      (isHomogeneous_X_pow j e) (coe_aeval_ratio' hj hf)
end PrimeFiltration.Point
end GroundTheory.Heights₂.Heights.Kleiman
