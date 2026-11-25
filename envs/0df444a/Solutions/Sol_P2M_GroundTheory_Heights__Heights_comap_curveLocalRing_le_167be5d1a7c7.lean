-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_comap_curveLocalRing_le_167be5d1a7c7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:26:00.296966+00:00
-- url     : https://prove2.me/submissions/b07e90d5-fee1-4f3e-a764-00c81d933466

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalDimComponentBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalDimComponentBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isUnit_algebraMap_curveLocalRing_358a5a627391


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
open MvPolynomial ComplexSets
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (P : PrimeSpectrum (curveLocalRing I q)) :
    (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q)) P).asIdeal ≤
      RingHom.ker (eval q) := by
  intro x hx
  by_contra h
  exact P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx
    (isUnit_algebraMap_curveLocalRing I q x fun h' ↦ h (RingHom.mem_ker.2 h')))
end GroundTheory.Heights₂.Heights
