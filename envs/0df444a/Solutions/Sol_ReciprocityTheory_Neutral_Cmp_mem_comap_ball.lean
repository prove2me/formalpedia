-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Cmp.mem_comap_ball
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:21:11.149463+00:00
-- url     : https://prove2.me/submissions/6aaf3887-0879-400d-a97e-df8a4b261645

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_Kloc
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ValuationIntCastLtOneIff

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
theorem _root_.solution (ι : Ω →+* PadicAlgCl p) (x : Ω) :
    x ∈ ((PadicAlgCl.valued p).v.valuationSubring.comap ι) ↔ ‖ι x‖ ≤ 1 := by
  rw [ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff]
  show ‖ι x‖₊ ≤ 1 ↔ ‖ι x‖ ≤ 1
  rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
end ReciprocityTheory.Neutral.Cmp
