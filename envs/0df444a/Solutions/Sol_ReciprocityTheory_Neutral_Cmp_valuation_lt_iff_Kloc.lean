-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Cmp.valuation_lt_iff_Kloc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:36:44.013104+00:00
-- url     : https://prove2.me/submissions/b0c66856-31c7-4616-97a8-a51cb32415eb

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_MemRangeOfAevalRatEqZero
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ModelA
import Theorems.Thm_ReciprocityTheory_Neutral_Cmp_locVal_apply
import Theorems.Thm_ReciprocityTheory_Neutral_Cmp_locVal_compat

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
    valuation (Kloc F ι) x < valuation (Kloc F ι) y ↔ ‖(x : PadicAlgCl p)‖ < ‖(y : PadicAlgCl p)‖ := by
  have := locVal_compat (F := F) ι
  rw [(ValuativeRel.isEquiv (valuation (Kloc F ι)) (locVal ι)).lt_iff_lt, ← NNReal.coe_lt_coe,
    locVal_apply, locVal_apply]
end ReciprocityTheory.Neutral.Cmp
