-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Cmp.norm_natCast_p_Kloc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:35:39.046956+00:00
-- url     : https://prove2.me/submissions/3bb0eb23-a684-4fef-9fe4-20ba036c8bb9

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
theorem _root_.solution (ι : Ω →+* PadicAlgCl p) : ‖(((p : ℕ) : Kloc F ι) : PadicAlgCl p)‖ < 1 := by
  have h : (((p : ℕ) : Kloc F ι) : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) (p : ℚ_[p]) := by
    simp
  rw [h, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one
end ReciprocityTheory.Neutral.Cmp
