-- Prove2me | solution 1 for P2M_GlobalTheory_T_natCard_homology_of_shortExact_mul__238aab7615a5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:34:25.098652+00:00
-- url     : https://prove2.me/submissions/d3b44ae1-a3dd-4fb0-808f-de8d3db31a44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NatCardHomologyOfShortExactMul
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NatCardHomologyOfShortExactMulStatement
import Theorems.Thm_GlobalTheory_natCard_homology_of_shortExact_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (p : ℕ) (C G : CochainComplex (ModuleCat.{0} ℤ) ℕ) (π : C ⟶ G) (hz : ((p : ℤ) • 𝟙 C) ≫ π = 0), (ShortComplex.mk ((p : ℤ) • 𝟙 C) π hz).ShortExact → ∀ n : ℕ, Nat.card (G.homology n) = Nat.card ((C.homology n) ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : C.homology n →ₗ[ℤ] C.homology n))) * Nat.card (LinearMap.ker ((p : ℤ) • (LinearMap.id : C.homology (n + 1) →ₗ[ℤ] C.homology (n + 1)))) := by
  first | exact @GlobalTheory.natCard_homology_of_shortExact_mul | exact GlobalTheory.natCard_homology_of_shortExact_mul | (intros; apply GlobalTheory.natCard_homology_of_shortExact_mul <;> assumption)
end _root_.GlobalTheory.T
