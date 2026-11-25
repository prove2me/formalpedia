-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation.monic_X_pow_add_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:49:39.581252+00:00
-- url     : https://prove2.me/submissions/6070cf73-e4fa-4626-9448-241db14e3a78

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TchOfIntegral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormEqOfNormSubLt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorRes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation
open Polynomial Finset
variable (l : ℕ) [Fact l.Prime]
namespace ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation
theorem _root_.solution {R : Type*} [CommRing R] [Nontrivial R] (d : ℕ) (a : ℕ → R) :
    (X ^ d + ∑ i ∈ range d, C (a i) * X ^ i).Monic := by
  refine monic_X_pow_add
    (lt_of_le_of_lt (degree_sum_le _ _) ((Finset.sup_lt_iff (WithBot.bot_lt_coe d)).2 ?_))
  intro i hi
  exact (degree_C_mul_X_pow_le i (a i)).trans_lt (WithBot.coe_lt_coe.2 (mem_range.1 hi))
end ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation
