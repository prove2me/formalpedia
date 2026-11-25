-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__Tame_exists_test_5e3aaaee6b64
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:46:49.215803+00:00
-- url     : https://prove2.me/submissions/383a2437-a47e-4119-a1ad-5d9f5767709d

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExistsTameGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.Tame
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω)
variable [IsAlgClosure E Ω]
attribute [instance] Test.grp Test.fin
namespace Formalism.BasicNotions.Examples₂.Tame
theorem _root_.solution (y : Ω) : ∃ t : Test E Ω, ∀ κ ∈ t.φ.ker, κ y = y := by
  have : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  let L := FiniteGaloisIntermediateField.adjoin E ({y} : Set Ω)
  have hk := IntermediateField.restrictNormalHom_ker L.toIntermediateField
  refine ⟨{ A' := L ≃ₐ[E] L, φ := AlgEquiv.restrictNormalHom L.toIntermediateField
            ho := by rw [hk]; exact L.toIntermediateField.fixingSubgroup_isOpen }, fun κ hκ => ?_⟩
  change κ ∈ (AlgEquiv.restrictNormalHom L.toIntermediateField).ker at hκ
  rw [hk, IntermediateField.mem_fixingSubgroup_iff] at hκ
  exact hκ y (FiniteGaloisIntermediateField.subset_adjoin E {y} rfl)
end Formalism.BasicNotions.Examples₂.Tame
