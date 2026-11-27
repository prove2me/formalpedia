-- Prove2me | solution 1 for P2M_GlobalTheory_T_mem_polyring_of_integral_closure_range__97cef6d2bba2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:53:20.296097+00:00
-- url     : https://prove2.me/submissions/8cc04445-4724-4c12-ab3e-1426bf8bae71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemPolyringOfIntegralClosureRange
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemPolyringOfIntegralClosureRangeStatement
import Theorems.Thm_GlobalTheory_mem_polyring_of_integral_closure_range


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {K : Type} [Field K] {D : ℕ} (y : Fin D → K), AlgebraicIndependent ℤ y → ∀ (t : K), t ∈ Subfield.closure (Set.range y) → ∀ {ι : Type} (z : ι → K), (∀ i, ∃ p : MvPolynomial (Fin D) ℤ, aeval y p = z i) → ∀ (f : Polynomial (MvPolynomial ι ℤ)), f.Monic → f.eval₂ (aeval z).toRingHom t = 0 → ∃ T₀ : MvPolynomial (Fin D) ℤ, t = aeval y T₀ := by
  first | exact @GlobalTheory.mem_polyring_of_integral_closure_range | exact GlobalTheory.mem_polyring_of_integral_closure_range | (intros; apply GlobalTheory.mem_polyring_of_integral_closure_range <;> assumption)
end _root_.GlobalTheory.T
