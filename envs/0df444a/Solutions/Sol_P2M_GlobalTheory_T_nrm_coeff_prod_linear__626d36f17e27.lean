-- Prove2me | solution 1 for P2M_GlobalTheory_T_nrm_coeff_prod_linear__626d36f17e27
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:51:10.617219+00:00
-- url     : https://prove2.me/submissions/206eed3e-cb3e-4a0e-9091-3ad72a824104

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NrmCoeffProdLinear
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NrmCoeffProdLinearStatement
import Theorems.Thm_GlobalTheory_Nef_nrm_coeff_prod_linear


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k F : Type) [Field k] [Field F] [Algebra k F], ∀ (v : Place k F) (m : ℕ) (α β : Fin m → F), nrm v (fun a : Fin (m + 1) => (∏ j, (Polynomial.C (α j) + Polynomial.C (β j) * Polynomial.X)).coeff a) = ∏ j, max (v.1 (α j)) (v.1 (β j)) := by
  first | exact @GlobalTheory.Nef.nrm_coeff_prod_linear | exact GlobalTheory.Nef.nrm_coeff_prod_linear | (intros; apply GlobalTheory.Nef.nrm_coeff_prod_linear <;> assumption)
end _root_.GlobalTheory.T
