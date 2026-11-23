-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Cmp.Compat.valuation_lt_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:17:12.182071+00:00
-- url     : https://prove2.me/submissions/fc4e05c3-b33a-4d23-909c-a015187951c3

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_Kloc
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ValuationIntCastLtOneIff
import Theorems.Thm_ReciprocityTheory_Neutral_Cmp_Compat_valuation_le_one_iff

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
open scoped Pointwise
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]
namespace ReciprocityTheory.Neutral.Cmp
namespace Compat
theorem _root_.solution {A : ValuationSubring Ω} {ι : Ω →+* PadicAlgCl p} (h : Compat p A ι) (x : Ω) :
    A.valuation x < 1 ↔ ‖ι x‖ < 1 := by
  by_cases hx : x = 0
  · subst hx
    simp
  · have hx' : x⁻¹ ≠ 0 := inv_ne_zero hx
    have h1 : A.valuation x < 1 ↔ 1 < A.valuation x⁻¹ := by
      rw [Valuation.one_lt_val_iff _ hx', inv_inv]
    have hn : 0 < ‖ι x‖ := norm_pos_iff.mpr ((map_ne_zero ι).mpr hx)
    rw [h1, ← not_le, h.valuation_le_one_iff, map_inv₀, norm_inv, not_le, one_lt_inv₀ hn]
end Compat
end ReciprocityTheory.Neutral.Cmp
