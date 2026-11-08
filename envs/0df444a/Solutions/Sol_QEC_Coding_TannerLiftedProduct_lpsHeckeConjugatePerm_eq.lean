-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckeConjugatePerm_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:09:17.847253+00:00
-- url     : https://prove2.me/submissions/04e46d65-d0a2-418a-a5a9-d099beb28e5b

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonIntegrals
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCommonDomain
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPerm_of_real_factor
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveSubgroup_perm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeConjugateIntersection_conjugate
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeIntersection_conjugate_upper


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N p : ℕ) [Fact p.Prime] :
    (lpsEffectiveHeckeConjugateIntersection N p).map lpsEffectiveModularGroup.subtype =
      ((lpsEffectiveGamma0 (N*p)).map lpsEffectiveModularGroup.subtype).map
        (MulAut.conj (MulAction.toPerm (lpsHeckeUpperGL ℝ p none))).toMonoidHom := by
  let φ : SL(2,ℤ) →* lpsEffectiveModularGroup :=
    (MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict
  change ((lpsHeckeConjugateIntersection N p).map φ).map lpsEffectiveModularGroup.subtype =
    (((CongruenceSubgroup.Gamma0 (N*p)).map φ).map lpsEffectiveModularGroup.subtype).map _
  have hφ (H : Subgroup SL(2,ℤ)) : (H.map φ).map lpsEffectiveModularGroup.subtype =
      H.map (MulAction.toPermHom SL(2,ℤ) ℍ) := lpsEffectiveSubgroup_perm H
  rw [hφ,hφ,Subgroup.map_map]
  ext π
  constructor
  · intro hπ
    obtain ⟨δ,hδ,hδπ⟩ := Subgroup.mem_map.mp hπ
    obtain ⟨γ,hγ,he⟩ := lpsHeckeConjugateIntersection_conjugate N p δ hδ
    exact Subgroup.mem_map.mpr ⟨γ,hγ,(lpsPerm_of_real_factor _ γ δ he).trans hδπ⟩
  · intro hπ
    obtain ⟨γ,hγ,hγπ⟩ := Subgroup.mem_map.mp hπ
    obtain ⟨δ,hδ,he⟩ := lpsHeckeIntersection_conjugate_upper N p γ hγ
    exact Subgroup.mem_map.mpr ⟨δ,hδ,(lpsPerm_of_real_factor _ γ δ he).symm.trans hγπ⟩
end QEC.Coding.TannerLiftedProduct
