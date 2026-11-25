-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_chartPrime_le_chartPrimeIdeal_1aa727f25bd6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:03:03.366331+00:00
-- url     : https://prove2.me/submissions/c234bac5-a0f3-48c8-841c-2f583f4e9d6a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationPoint

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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {j : Fin (N + 1)}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (hj : x j ≠ 0) (pp : Ideal (Poly S N)) :
    chartPrime pp hj ≤ chartPrimeIdeal x hj pp := by
  rw [chartPrime, Ideal.span_le]
  intro a ha
  exact ha
end GroundTheory.Heights₂.Heights.Kleiman
