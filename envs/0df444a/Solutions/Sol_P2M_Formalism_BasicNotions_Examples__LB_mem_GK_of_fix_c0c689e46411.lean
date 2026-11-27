-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__LB_mem_GK_of_fix_c0c689e46411
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:51:02.694394+00:00
-- url     : https://prove2.me/submissions/987f2bbe-3757-4d0e-9852-2da3d97535dd

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
theorem _root_.solution (σ : GQ l) (h : ∀ x : E, σ (jE j x) = jE j x) :
    σ ∈ (KwF (E := E) j).fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  have hle : KwF (E := E) j ≤ IntermediateField.fixedField (Subgroup.zpowers σ) := by
    rw [KwF, IntermediateField.adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    intro f hf
    have hst : Subgroup.zpowers σ ≤
        MulAction.stabilizer (GQ l) (jE (E := E) j (Module.finBasis ℚ E i)) :=
      Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr (h _))
    exact MulAction.mem_stabilizer_iff.mp (hst hf)
  intro x hx
  exact (IntermediateField.mem_fixedField_iff _ _).mp (hle hx) σ (Subgroup.mem_zpowers σ)
end Formalism.BasicNotions.Examples₂.LB
