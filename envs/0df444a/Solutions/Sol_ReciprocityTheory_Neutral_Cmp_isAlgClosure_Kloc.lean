-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Cmp.isAlgClosure_Kloc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:56:47.8425+00:00
-- url     : https://prove2.me/submissions/c8862d2d-1ce4-44f1-bb0e-452d70da3051

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_Kloc
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_MemRangeOfAevalRatEqZero

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
namespace ReciprocityTheory.Neutral.Cmp
theorem _root_.solution (ι : Ω →+* PadicAlgCl p) : IsAlgClosure (Kloc F ι) (PadicAlgCl p) := by
  exact ⟨inferInstance, inferInstance⟩
end ReciprocityTheory.Neutral.Cmp
