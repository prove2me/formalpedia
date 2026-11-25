-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2.normA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:00:58.135074+00:00
-- url     : https://prove2.me/submissions/2cc05ba8-0299-4391-affe-25ecc2efc0fe

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_IsTwoCocycleCoboundary
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_CurriedCoboundaryEq
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Deg2_cur_sub
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Deg2_isTwoCocycle_curried
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Deg2_continuous_cur
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Deg2_curried_coboundary_eq
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Deg2_retr_mul_rep
import Theorems.Thm_P2M_ReciprocityTheory_DiscreteGroups_LocalClassField_Deg2_retr_mul__8f5c13bf08eb
import Theorems.Thm_P2M_ReciprocityTheory_DiscreteGroups_LocalClassField_Deg2_rep_mul__0df8de4ab8c8
import Theorems.Thm_P2M_ReciprocityTheory_DiscreteGroups_LocalClassField_Deg2_continuous_retr__8e3672736de6
import Theorems.Thm_P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__continuous_rep_745e730e9170
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Deg2_stepA


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
open ReciprocityTheory.Coh ReciprocityTheory.Coh.InflationRestrictionInvariants ReciprocityTheory.Coh.CohomologyFunctoriality₂ ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (M : TRep R G) (N : Subgroup G)
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
theorem _root_.solution (hN : IsOpen (N : Set G)) (x : M.coch.X 2) (hx : M.coch.d 2 x = 0)
    (h0 : ∀ n ∈ N, ∀ m ∈ N, cur M x n m = 0) :
    ∃ w : M.coch.X 1, ∀ n ∈ N, ∀ g, cur M (x - M.coch.d 1 w) n g = 0 := by
  have hc : Continuous fun g : G => - cur M x (retr N g) (rep N g) :=
    (continuous_cur M x (continuous_retr' N hN) (continuous_rep N hN)).neg
  refine ⟨mk1 M _ hc, fun n hn g => ?_⟩
  rw [cur_sub, curried_coboundary_eq]
  exact stepA (isTwoCocycle_curried M x hx) (retr_mul_rep N) (fun g => (retr N g).2) (retr_mul' N) (rep_mul' N) h0 n hn g
end ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
