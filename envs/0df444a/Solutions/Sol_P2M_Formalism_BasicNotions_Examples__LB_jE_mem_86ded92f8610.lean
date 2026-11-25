-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__LB_jE_mem_86ded92f8610
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:12:48.61737+00:00
-- url     : https://prove2.me/submissions/c35576af-b20b-4a3e-9217-3317303c5a1d

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocA
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.LB
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Pointwise Formalism.BasicNotions.Loc
variable {l : ℕ} [hl : Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  (j : Ω →+* PadicAlgCl l)
namespace Formalism.BasicNotions.Examples₂.LB
theorem _root_.solution (x : E) : jE j x ∈ KwF (E := E) j := by
  rw [← (Module.finBasis ℚ E).sum_repr x, map_sum]
  refine IntermediateField.sum_mem _ fun i _ => ?_
  rw [Algebra.smul_def, map_mul, eq_ratCast (algebraMap ℚ E), map_ratCast]
  exact mul_mem (SubfieldClass.ratCast_mem _ _) (IntermediateField.subset_adjoin ℚ_[l] _ ⟨i, rfl⟩)
end Formalism.BasicNotions.Examples₂.LB
