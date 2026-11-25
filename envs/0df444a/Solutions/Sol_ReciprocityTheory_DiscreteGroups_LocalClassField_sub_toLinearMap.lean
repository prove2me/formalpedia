-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.sub_toLinearMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:02:03.144323+00:00
-- url     : https://prove2.me/submissions/01280baa-983a-4af1-a2e2-042835cc6853

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
theorem _root_.solution (M : TRep R C) (g : C) :
    (Rep.applyAsHom (Rep.of M.rho) g - 𝟙 (Rep.of M.rho)).hom.toLinearMap = M.rho g - LinearMap.id := rfl
end ReciprocityTheory.DiscreteGroups.LocalClassField
