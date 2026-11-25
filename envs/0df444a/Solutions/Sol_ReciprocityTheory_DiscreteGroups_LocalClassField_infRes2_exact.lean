-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.infRes2_exact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:13:56.222678+00:00
-- url     : https://prove2.me/submissions/80349789-0501-4d8f-bf9d-53df676dd876

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_SubsingletonHOfSubsingleton
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_EqZeroOfResEqZeroOfCoprime
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Deg2_exact2


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open ReciprocityTheory.Coh Function
noncomputable section
universe u
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {G' : Type u} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (M : TRep R G) (N : Subgroup G) [N.Normal] (hN : IsOpen (N : Set G))
    (Q : TRep R (G ⧸ N)) (P : Pair Q M) (hP : IsInvRep M N Q P) (h1 : Subsingleton ((M.resSub N).H 1)) :
    Exact (P.hom.H 2) ((resP M N).hom.H 2) :=
  Deg2.exact2 M N Q P hN hP h1
end ReciprocityTheory.DiscreteGroups.LocalClassField
