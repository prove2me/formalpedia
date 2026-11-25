-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__LB_algebraMap_mem_clE_52b103178853
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:11:32.993542+00:00
-- url     : https://prove2.me/submissions/07cb7fd6-c20b-4ff9-a16e-5cd725727917

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
theorem _root_.solution (x : ℚ_[l]) : algebraMap ℚ_[l] (PadicAlgCl l) x ∈ clE (E := E) j := by
  have hcont : Continuous (algebraMap ℚ_[l] (PadicAlgCl l)) :=
    (AddMonoidHomClass.isometry_of_norm (algebraMap ℚ_[l] (PadicAlgCl l))
      (PadicAlgCl.norm_extends l)).continuous
  have hclosed : IsClosed {y : ℚ_[l] | algebraMap ℚ_[l] (PadicAlgCl l) y ∈ clE (E := E) j} := by
    have hc : IsClosed ((clE (E := E) j : Subfield (PadicAlgCl l)) : Set (PadicAlgCl l)) := by
      first
      | exact Subfield.isClosed_topologicalClosure _
      | exact isClosed_closure
    exact hc.preimage hcont
  have hQ : ∀ q : ℚ, algebraMap ℚ_[l] (PadicAlgCl l) (q : ℚ_[l]) ∈ clE (E := E) j := by
    intro q
    rw [map_ratCast]
    exact Subfield.le_topologicalClosure _ (SubfieldClass.ratCast_mem _ q)
  exact (Padic.denseRange_ratCast l).induction_on x hclosed hQ
end Formalism.BasicNotions.Examples₂.LB
