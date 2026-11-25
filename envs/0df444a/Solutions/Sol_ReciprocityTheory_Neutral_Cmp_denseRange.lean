-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Cmp.denseRange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:09:28.451796+00:00
-- url     : https://prove2.me/submissions/73ec7e38-2e19-45f4-9d5d-7a87e1e64630

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_Kloc
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_MemRangeOfAevalRatEqZero
import Theorems.Thm_ReciprocityTheory_Neutral_Cmp_denseRange_of_isAlgClosed

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
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]
variable (F)
include F
namespace ReciprocityTheory.Neutral.Cmp
theorem _root_.solution (ι : Ω →+* PadicAlgCl p) : DenseRange ι := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  exact denseRange_of_isAlgClosed ι
end ReciprocityTheory.Neutral.Cmp
