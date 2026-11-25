-- Prove2me | solution 1 for ReciprocityTheory.Gal.eq_of_valuation_lt_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:11:16.910688+00:00
-- url     : https://prove2.me/submissions/8665d2c0-b1a9-40f1-a344-6164f2791e76

import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalB
import Theorems.Thm_ReciprocityTheory_Gal_le_of_valuation_lt_one_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open NumberField IsDedekindDomain Pointwise
open scoped nonZeroDivisors
open ReciprocityTheory ReciprocityTheory.Gal
variable {Ω : Type*} [Field Ω]
namespace ReciprocityTheory.Gal
theorem _root_.solution (F : Type*) [Field F] [NumberField F] [Algebra F Ω]
    [IsAlgClosure F Ω] {A A' : ValuationSubring Ω}
    (h : ∀ b : Ω, IsIntegral ℤ b → (A.valuation b < 1 ↔ A'.valuation b < 1)) : A = A' :=
  le_antisymm (le_of_valuation_lt_one_iff F h)
    (le_of_valuation_lt_one_iff F fun b hb => (h b hb).symm)
end ReciprocityTheory.Gal
