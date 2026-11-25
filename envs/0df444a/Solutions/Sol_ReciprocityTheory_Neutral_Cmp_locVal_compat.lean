-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Cmp.locVal_compat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:21:08.594419+00:00
-- url     : https://prove2.me/submissions/15946d40-01c7-458c-84a5-21d5035065b5

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_MemRangeOfAevalRatEqZero
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ModelA

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
theorem _root_.solution (ι : Ω →+* PadicAlgCl p) : (locVal (F := F) ι).Compatible := Valuation.Compatible.ofValuation _
end ReciprocityTheory.Neutral.Cmp
