-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsChow_DivCycleGeneric_proof_19c8cc37fe81
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:53:47.888098+00:00
-- url     : https://prove2.me/submissions/a7e8a994-8861-4bc3-b68c-72e215eed6ad

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PObjectsDivCycleGeneric
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_DivCycleGeneric_length_eq_6cefeeea48bf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_DivCycleGeneric_blkEquiv_apply_b5c60a5abd6f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_DivCycleGeneric_algebraMap_generic_8829ce0fabef
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_DivCycleGeneric_genericIdeal_eq_ab3f42321e11
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_DivCycleGeneric_disjoint_iff_isHorizontal_a353c136abe0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_DivCycleGeneric_algebraMap_linForm_2ec74aa66477
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_DivCycleGeneric_map_comap_horizontal_605d4997ca31

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.ObjectsChow
open GroundTheory.Heights₂.Heights.ObjectsChow.DivCycleGeneric
open MvPolynomial
variable {n : ℕ}
attribute [local instance] genericAlgebra
open Classical
namespace GroundTheory.Heights₂.Heights.ObjectsChow.DivCycleGeneric
theorem _root_.solution : Statement := by
  intro n e P u _ _
  set J := P ⊔ Ideal.span {IndefiniteRowSideFullHecke.ArithBezout.linForm u}
  have hJ : genericIdeal P ⊔ Ideal.span {linForm fun j => (u j : ℚ)} =
      J.map (algebraMap _ (MvPolynomial (Fin n) ℚ)) := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, algebraMap_linForm, genericIdeal_eq]
  have hX : ∀ j : Fin n, algebraMap _ (MvPolynomial (Fin n) ℚ)
      (X ⟨(), j⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n)) = X j := fun j => by
    simp [algebraMap_generic, toGeneric, blkEquiv_apply]
  have hsub : (↑((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P (IndefiniteRowSideFullHecke.ArithBezout.linForm u)).filter
      ReciprocityTheory.ChartRestriction.G.Geo.IsHorizontal).support :
        Set (Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n)))) ⊆
        {W | W.IsPrime ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsHorizontal W} := by
    intro W hW
    rw [Finset.mem_coe, Finsupp.mem_support_iff, Finsupp.filter_apply] at hW
    split_ifs at hW with hh
    · refine ⟨?_, hh⟩
      by_contra hp
      apply hW
      show (if W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P (IndefiniteRowSideFullHecke.ArithBezout.linForm u) then _ else 0) = 0
      rw [if_neg fun h => hp h.1.1.1]
    · exact absurd rfl hW
  have hinj : Set.InjOn genericIdeal {W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n)) |
      W.IsPrime ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsHorizontal W} := by
    intro W₁ h₁ W₂ h₂ h
    rw [genericIdeal_eq, genericIdeal_eq] at h
    have := congrArg (Ideal.comap (algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n))
      (MvPolynomial (Fin n) ℚ))) h
    rwa [map_comap_horizontal W₁ h₁.1 h₁.2, map_comap_horizontal W₂ h₂.1 h₂.2] at this
  ext W'
  rw [divCycle, fundCycle, Finsupp.onFinset_apply, hJ]
  by_cases hW' : W'.IsPrime
  · obtain ⟨W, hWp, hWd, rfl⟩ : ∃ W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n)),
        W.IsPrime ∧ Disjoint (intUnits n : Set (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n)))
          (W : Set (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n))) ∧
          W.map (algebraMap _ (MvPolynomial (Fin n) ℚ)) = W' := by
      rw [IsLocalization.isPrime_iff_isPrime_disjoint (intUnits n) (MvPolynomial (Fin n) ℚ)] at hW'
      exact ⟨_, hW'.1, hW'.2, IsLocalization.map_under (intUnits n) (MvPolynomial (Fin n) ℚ) W'⟩
    have hh := (disjoint_iff_isHorizontal W).mp hWd
    have hc := map_comap_horizontal W hWp hh
    conv_rhs => rw [← genericIdeal_eq W, Finsupp.mapDomain_apply' _ _ hsub hinj ⟨hWp, hh⟩]
    rw [Finsupp.filter_apply, if_pos hh]
    show _ = if W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P (IndefiniteRowSideFullHecke.ArithBezout.linForm u) then
      ReciprocityTheory.ChartRestriction.G.Geo.multAt J W else 0
    have hmem : W.map (algebraMap _ (MvPolynomial (Fin n) ℚ)) ∈
        relComps (J.map (algebraMap _ (MvPolynomial (Fin n) ℚ))) ↔
          W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P (IndefiniteRowSideFullHecke.ArithBezout.linForm u) := by
      have hrel : IsRelevant (W.map (algebraMap _ (MvPolynomial (Fin n) ℚ))) ↔
          ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant W := by
        have hXm : ∀ j : Fin n, X j ∈ W.map (algebraMap _ (MvPolynomial (Fin n) ℚ)) ↔
            (X ⟨(), j⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n)) ∈ W := fun j => by
          rw [← hX, ← Ideal.mem_comap, hc]
        simp only [IsRelevant, ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant, hXm]
        exact ⟨fun ⟨j, hj⟩ k => ⟨j, by cases k; exact hj⟩, fun h => h ()⟩
      simp only [relComps, ReciprocityTheory.ChartRestriction.G.Geo.divSupp, Set.mem_ofPred_eq, hrel,
        IsLocalization.minimalPrimes_map (intUnits n) (MvPolynomial (Fin n) ℚ), Set.mem_preimage]
      rw [show Ideal.under _ (W.map (algebraMap _ (MvPolynomial (Fin n) ℚ))) = W from hc]
    have : (W.map (algebraMap _ (MvPolynomial (Fin n) ℚ))).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint (intUnits n) _ W hWp hWd
    by_cases hm : W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P (IndefiniteRowSideFullHecke.ArithBezout.linForm u)
    · rw [if_pos (hmem.mpr hm), if_pos hm, localMult, dif_pos this, ReciprocityTheory.ChartRestriction.G.Geo.multAt, dif_pos hWp,
        length_eq (A' := MvPolynomial (Fin n) ℚ) (intUnits n) J W hWd]
    · rw [if_neg (fun h => hm (hmem.mp h)), if_neg hm]
  · rw [if_neg fun h => hW' h.1.1.1]
    symm
    rw [Finsupp.mapDomain, Finsupp.sum_apply]
    refine Finset.sum_eq_zero fun W hW => ?_
    dsimp only
    rw [Finsupp.single_apply, if_neg]
    rintro rfl
    obtain ⟨hWp, hh⟩ := hsub hW
    apply hW'
    rw [genericIdeal_eq]
    exact IsLocalization.isPrime_of_isPrime_disjoint (intUnits n) _ W hWp ((disjoint_iff_isHorizontal W).mpr hh)
end GroundTheory.Heights₂.Heights.ObjectsChow.DivCycleGeneric
