-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_Cech_sgn_mul_self_a6716700d2d5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:58:36.813557+00:00
-- url     : https://prove2.me/submissions/016d0c90-5aa3-4aad-a752-ecada683ec86

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTailLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTail

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
  {x : Fin (N + 1) → Ω} (M : FinGradedSub (S := S) (x := x) Ω)
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace Cech
theorem _root_.solution {n : ℕ} (J : Finset (Fin n)) (j : Fin n) : Cech.sgn J j * Cech.sgn J j = 1 := by
  rw [Cech.sgn, ← mul_pow, neg_one_mul, neg_neg, one_pow]
end Cech
end GroundTheory.Heights₂.Heights.Kleiman
