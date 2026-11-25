-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2.normB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:17:08.055968+00:00
-- url     : https://prove2.me/submissions/808fade9-4c78-4f84-be51-2b2962c6ddc1

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_IsTwoCocycleCoboundary
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_CurriedCoboundaryEq
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Deg2_cur_sub
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Deg2_isTwoCocycle_curried
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Deg2_continuous_cur
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Deg2_curried_coboundary_eq
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Deg2_continuous_comp_rep
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Deg2_retr_mul_rep
import Theorems.Thm_P2M_ReciprocityTheory_DiscreteGroups_LocalClassField_Deg2_retr_mul__8f5c13bf08eb
import Theorems.Thm_P2M_ReciprocityTheory_DiscreteGroups_LocalClassField_Deg2_rep_mul__0df8de4ab8c8
import Theorems.Thm_P2M_ReciprocityTheory_DiscreteGroups_LocalClassField_Deg2_continuous_retr__8e3672736de6
import Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_memZ
import Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_mem_oneCoboundaries_iff
import Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_mk_eq_zero_iff
import Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_wach_d1_eq_zero_iff
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Deg2_stepB
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Deg2_theta_mul


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
theorem _root_.solution [N.Normal] (hN : IsOpen (N : Set G)) (h1 : Subsingleton ((M.resSub N).H 1)) (x : M.coch.X 2)
    (hx : M.coch.d 2 x = 0) (h0 : ∀ n ∈ N, ∀ g, cur M x n g = 0) :
    ∃ w : M.coch.X 1, ∀ n ∈ N, ∀ g, cur M (x - M.coch.d 1 w) n g = 0 ∧ cur M (x - M.coch.d 1 w) g n = 0 := by
  have hC := isTwoCocycle_curried M x hx
  have hex : ∀ g : G, ∃ e : M.V, (g ∈ N → e = 0) ∧
      ∀ n ∈ N, cur M x g (g⁻¹ * n * g) = e - M.rho n e := by
    intro g
    by_cases hg : g ∈ N
    · exact ⟨0, fun _ => rfl, fun n _ => by rw [h0 g hg, map_zero, sub_zero]⟩
    · let θ : (M.resSub N).coch.X 1 := ⟨fun v => cur M x g (g⁻¹ * (v 0 : G) * g),
        continuous_cur M x continuous_const
          ((continuous_const.mul (continuous_subtype_val.comp (continuous_apply 0))).mul continuous_const)⟩
      have hθ : (M.resSub N).coch.d 1 θ = 0 := by
        rw [wach_d1_eq_zero_iff]
        intro a b
        show cur M x g (g⁻¹ * ((a * b : N) : G) * g) =
          cur M x g (g⁻¹ * (a : G) * g) + M.rho (a : G) (cur M x g (g⁻¹ * (b : G) * g))
        have e1 : g⁻¹ * ((a * b : N) : G) * g = (g⁻¹ * (a : G) * g) * (g⁻¹ * (b : G) * g) := by
          rw [Subgroup.coe_mul]; group
        rw [e1, theta_mul hC h0 g _ (Subgroup.Normal.conj_mem' ‹_› _ a.2 g)]
        congr 3
        group
      have hz : (Submodule.Quotient.mk ⟨θ, (memZ _).2 hθ⟩ : (M.resSub N).H 1) = 0 := Subsingleton.elim _ _
      rw [mk_eq_zero_iff, mem_oneCoboundaries_iff] at hz
      obtain ⟨m, hm⟩ : ∃ m : M.V, ∀ a : N, cur M x g (g⁻¹ * (a : G) * g) = M.rho (a : G) m - m := hz
      refine ⟨-m, fun h => absurd h hg, fun n hn => ?_⟩
      have h' : cur M x g (g⁻¹ * n * g) = M.rho n m - m := hm ⟨n, hn⟩
      rw [h', map_neg]; abel
  choose e he0 he using hex
  have hc : Continuous fun g : G => M.rho (retr N g : G) (e (rep N g)) :=
    M.cont.comp (f := fun g : G => ((retr N g : G), e (rep N g)))
      ((continuous_retr' N hN).prodMk (continuous_comp_rep N hN e))
  refine ⟨mk1 M _ hc, fun n hn g => ?_⟩
  rw [cur_sub, curried_coboundary_eq, cur_sub, curried_coboundary_eq]
  exact stepB hC (retr_mul_rep N) (fun g => (retr N g).2) (retr_mul' N) (rep_mul' N) h0 e he0 he n hn g
end ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
