-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_exists_minimalPrime_mem_zeroSet_eb01412e6298
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:32:04.156322+00:00
-- url     : https://prove2.me/submissions/1735502c-3669-4242-8fa7-26b142fba85d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIsolatedPointsCountPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIsolatedPointsCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Topology ComplexSets
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) {x : Fin n → ℂ}
    (hx : x ∈ zeroSet J) : ∃ P ∈ J.minimalPrimes, x ∈ zeroSet P := by
  have hJ : J ≤ RingHom.ker (eval x) := fun q hq => (RingHom.mem_ker).2 (hx q hq)
  have : (RingHom.ker (eval x : MvPolynomial (Fin n) ℂ →+* ℂ)).IsPrime := RingHom.ker_isPrime _
  obtain ⟨P, hP, hPle⟩ := Ideal.exists_minimalPrimes_le hJ
  exact ⟨P, hP, fun q hq => (RingHom.mem_ker).1 (hPle hq)⟩
end GroundTheory.Heights₂.Heights
