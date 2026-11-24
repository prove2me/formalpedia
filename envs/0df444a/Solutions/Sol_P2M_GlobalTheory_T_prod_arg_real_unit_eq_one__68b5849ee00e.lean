-- Prove2me | solution 1 for P2M_GlobalTheory_T_prod_arg_real_unit_eq_one__68b5849ee00e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:35:07.375813+00:00
-- url     : https://prove2.me/submissions/da406c88-1316-4be4-9a18-313cedebf01a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdArgRealUnitEqOne
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdArgRealUnitEqOneStatement
import Theorems.Thm_GlobalTheory_prod_arg_real_unit_eq_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (q : ℕ), q.Prime → 2 < q →
    ∀ u : (𝓞 E)ˣ, (u : 𝓞 E) - 1 ∈ Ideal.span {((q : ℕ) : 𝓞 E)} →
    (∀ φ : E →+* ℂ, starRingEnd ℂ (φ ((u : 𝓞 E) : E)) = φ ((u : 𝓞 E) : E)) →
    ∏ w : InfinitePlace E, (w.embedding ((u : 𝓞 E) : E) / ((‖w.embedding ((u : 𝓞 E) : E)‖ : ℝ) : ℂ)) = 1 := by
  first | exact @GlobalTheory.prod_arg_real_unit_eq_one | exact GlobalTheory.prod_arg_real_unit_eq_one | (intros; apply GlobalTheory.prod_arg_real_unit_eq_one <;> assumption)
end _root_.GlobalTheory.T
