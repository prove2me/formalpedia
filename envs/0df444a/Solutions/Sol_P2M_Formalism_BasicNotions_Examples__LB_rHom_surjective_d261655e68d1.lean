-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__LB_rHom_surjective_d261655e68d1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:21:44.788076+00:00
-- url     : https://prove2.me/submissions/1cb3b5b5-97b2-4d39-9a04-30cfeb95d77f

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocB
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocC
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_j_rHom_06cfa976bc62
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_exists_ext_b6f487c55f36

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
  [IsAlgClosure E Ω] [CharZero Ω]
variable [IsAlgClosure ℚ Ω] (j : Ω →+* PadicAlgCl l)
variable {j} {A : ValuationSubring Ω} (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1)
namespace Formalism.BasicNotions.Examples₂.LB
theorem _root_.solution : Function.Surjective (rHom (E := E) hj) := by
  rintro ⟨g, hg⟩
  obtain ⟨σ, hσ⟩ := exists_ext hj g hg
  have hfix : ∀ y ∈ Set.range fun i => jE (E := E) j (Module.finBasis ℚ E i), σ y = y := by
    rintro _ ⟨i, rfl⟩
    simp only [jE, RingHom.comp_apply]
    rw [hσ, AlgEquiv.commutes]
  have hmem : σ ∈ (KwF (E := E) j).fixingSubgroup := by
    have hz : Subgroup.zpowers σ ≤ (KwF (E := E) j).fixingSubgroup := by
      rw [← IntermediateField.le_iff_le]
      unfold KwF
      rw [IntermediateField.adjoin_le_iff]
      intro y hy
      rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
      intro τ hτ
      have hst : Subgroup.zpowers σ ≤ MulAction.stabilizer (GQ l) y := by
        rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
        exact hfix y hy
      have h2 := hst hτ
      rwa [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at h2
    exact hz (Subgroup.mem_zpowers σ)
  refine ⟨⟨σ, hmem⟩, Subtype.ext (AlgEquiv.ext fun x => j.injective ?_)⟩
  rw [j_rHom]
  exact hσ x
end Formalism.BasicNotions.Examples₂.LB
