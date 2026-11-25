-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Cmp.padicAlgCl_norm_sub_le_max
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:35:40.732963+00:00
-- url     : https://prove2.me/submissions/33469a29-a292-4627-a0f6-71427d7660cf

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ContinuousGK
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_Inertia
import Theorems.Thm_ReciprocityTheory_Neutral_Cmp_norm_add_le_max_padic

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
theorem _root_.solution (x y : PadicAlgCl p) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  simpa [sub_eq_add_neg] using norm_add_le_max_padic x (-y)
end ReciprocityTheory.Neutral.Cmp
