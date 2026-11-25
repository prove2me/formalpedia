-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFiltration_Restrict_proof_9254d696b6ca
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:26:28.274663+00:00
-- url     : https://prove2.me/submissions/e7541f99-18e6-4100-bb69-3752a11f8180

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationRestrict
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_generator_at_5bc7d5d10cbc

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
namespace PrimeFiltration.Restrict
theorem _root_.solution : PrimeFiltration.Restrict.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x pp _ _ _ j hj _ K' _ _ ψ _ hxy Q
  obtain ⟨Q1, hQ1⟩ := Q.invertible (singleChart hj)
  obtain ⟨q0, hq0, q1, hq1, c0, hc, hψ⟩ := exists_generator_at hj ψ hQ1
  refine ⟨restrictBundle hj ψ hxy Q hq0 hc hψ hQ1 hq1, fun q => residueAt hj ψ (q / q0),
    fun I => ⟨?_, ?_, ?_, rfl⟩⟩
  · intro q hq
    exact Submodule.subset_span ⟨q, hq, rfl⟩
  · intro q hq q' hq'
    beta_reduce
    rw [add_div]
    exact ((regularAt_div hj ψ hxy Q hc hψ hQ1 hq1 I hq).add
      (regularAt_div hj ψ hxy Q hc hψ hQ1 hq1 I hq')).2
  · intro q hq f s e hs hf hse
    have hr := regularAt_chart hj ψ hxy I hs hf hse
    beta_reduce
    rw [mul_div_assoc, (hr.1.mul (regularAt_div hj ψ hxy Q hc hψ hQ1 hq1 I hq)).2, hr.2]
end PrimeFiltration.Restrict
end GroundTheory.Heights₂.Heights.Kleiman
