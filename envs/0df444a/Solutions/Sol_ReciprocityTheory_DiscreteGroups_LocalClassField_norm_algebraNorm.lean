-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.norm_algebraNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:14:31.098169+00:00
-- url     : https://prove2.me/submissions/e0c09f7b-0faa-4b2b-a2e6-4cd71c5ebd33

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtD
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtE
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsA
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_norm_algHom
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_finDim_extendScalars_of_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh
noncomputable section
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
variable {K L}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) (x : IntermediateField.extendScalars h) :
    ‖((Algebra.norm K x : K) : PadicAlgCl p)‖ =
      ‖(x : PadicAlgCl p)‖ ^ Module.finrank K (IntermediateField.extendScalars h) := by
  have := finDim_extendScalars_of_le p hL h
  have h1 := Algebra.norm_eq_prod_embeddings K (PadicAlgCl p) x
  have h2 : ((Algebra.norm K x : K) : PadicAlgCl p) = algebraMap K (PadicAlgCl p) (Algebra.norm K x) := rfl
  rw [h2, h1, norm_prod, Finset.prod_congr rfl (fun σ _ => ?_), Finset.prod_const, Finset.card_univ,
    AlgHom.card]
  exact norm_algHom (E := L) (σ.restrictScalars ℚ_[p]) ⟨x.1, x.2⟩
end ReciprocityTheory.DiscreteGroups.LocalClassField
