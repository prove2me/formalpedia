-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Cmp.valuation_le_iff_Kloc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:53:17.376301+00:00
-- url     : https://prove2.me/submissions/cd0a7796-7690-475b-a0b4-c4864ed4e61c

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_MemRangeOfAevalRatEqZero
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ModelA
import Theorems.Thm_ReciprocityTheory_Neutral_Cmp_valuation_lt_iff_Kloc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Cmp
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain ValuativeRel
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]
attribute [local instance] locRel
namespace ReciprocityTheory.Neutral.Cmp
theorem _root_.solution (ι : Ω →+* PadicAlgCl p) (x y : Kloc F ι) :
    valuation (Kloc F ι) x ≤ valuation (Kloc F ι) y ↔ ‖(x : PadicAlgCl p)‖ ≤ ‖(y : PadicAlgCl p)‖ := by
  rw [← not_lt, valuation_lt_iff_Kloc, not_lt]
end ReciprocityTheory.Neutral.Cmp
