-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_monomial_mem_monos_9116ec3eae2a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:01:43.317933+00:00
-- url     : https://prove2.me/submissions/074ea44b-5006-4b7b-82ee-20c5a7098ec2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerrePolyLaurent

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
universe u
open GroundTheory.Heights₂.Heights.Kleiman.LaurentLoc
variable (S : Type u) [CommRing S] (N : ℕ)
variable {S N}
namespace GroundTheory.Heights₂.Heights.Kleiman.LaurentLoc
theorem _root_.solution {I : Finset (Fin (N + 1))} (f : Fin (N + 1) →₀ ℕ) (hf : ∀ j ∉ I, f j = 0) :
    (monomial f 1 : Poly S N) ∈ monos I := by
  rw [monomial_eq, C_1, one_mul]
  refine Submonoid.prod_mem _ fun i hi => Submonoid.pow_mem _ (X_mem_monos ?_) _
  by_contra h
  exact (Finsupp.mem_support_iff.mp hi) (hf i h)
end GroundTheory.Heights₂.Heights.Kleiman.LaurentLoc
