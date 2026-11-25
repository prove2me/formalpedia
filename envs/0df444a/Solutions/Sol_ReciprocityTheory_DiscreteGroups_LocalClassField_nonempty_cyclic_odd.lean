-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.nonempty_cyclic_odd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:01:59.442225+00:00
-- url     : https://prove2.me/submissions/2fadee26-c97c-49b0-ba28-7da3035bf47f

import Mathlib
import Definitions.Def_ReciprocityTheory_GroupCohomology_IsLowExists
import Definitions.Def_ReciprocityTheory_GroupCohomology_LowNat
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Duality
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_FinCoh

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open ReciprocityTheory.Coh CategoryTheory
noncomputable section
universe u
variable {R : Type u} [CommRing R]
variable {C : Type u} [CommGroup C] [Fintype C] [TopologicalSpace C] [IsTopologicalGroup C]
  [DiscreteTopology C]
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (M : TRep R C) (g : C) (hg : ∀ x, x ∈ Subgroup.zpowers g) (i : ℕ) (hi : Odd i) :
    Nonempty (M.H i ≃ₗ[R] (LinearMap.ker M.rho.norm ⧸
      (LinearMap.range (M.rho g - LinearMap.id)).comap (LinearMap.ker M.rho.norm).subtype)) := by
  have e := scEquiv _ _ (Rep.FiniteCyclicGroup.subCompNormHom (Rep.of M.rho) g).zero _ rfl
  exact ⟨finEquiv M i ≪≫ₗ
    (Rep.FiniteCyclicGroup.groupCohomologyIsoOdd (Rep.of M.rho) g hg i hi).toLinearEquiv ≪≫ₗ e⟩
end ReciprocityTheory.DiscreteGroups.LocalClassField
