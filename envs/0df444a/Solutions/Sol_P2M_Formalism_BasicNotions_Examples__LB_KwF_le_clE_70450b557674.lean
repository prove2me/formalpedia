-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__LB_KwF_le_clE_70450b557674
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:46:46.115221+00:00
-- url     : https://prove2.me/submissions/55f5b91d-bf1a-4b0e-9ebf-515242cb4a3c

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocA
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocB
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_algebraMap_mem_clE_52b103178853

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
theorem _root_.solution : (KwF (E := E) j : Set (PadicAlgCl l)) ⊆
    closure (Set.range fun x : E => j (algebraMap E Ω x)) := by
  let F : IntermediateField ℚ_[l] (PadicAlgCl l) :=
    Subfield.toIntermediateField (clE (E := E) j) (algebraMap_mem_clE j)
  have hle : KwF (E := E) j ≤ F := by
    rw [KwF, IntermediateField.adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    exact Subfield.le_topologicalClosure _ (RingHom.mem_fieldRange.mpr ⟨_, rfl⟩)
  intro x hx
  have h1 : x ∈ ((clE (E := E) j : Subfield (PadicAlgCl l)) : Set (PadicAlgCl l)) := hle hx
  have h2 : ((clE (E := E) j : Subfield (PadicAlgCl l)) : Set (PadicAlgCl l)) =
      closure (Set.range fun x : E => j (algebraMap E Ω x)) := by
    show closure ((jE (E := E) j).fieldRange : Set (PadicAlgCl l)) = _
    rw [RingHom.coe_fieldRange]
    rfl
  rwa [h2] at h1
end Formalism.BasicNotions.Examples₂.LB
