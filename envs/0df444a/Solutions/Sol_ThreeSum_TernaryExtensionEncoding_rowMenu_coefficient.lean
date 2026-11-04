-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.rowMenu_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:20:01.932543+00:00
-- url     : https://prove2.me/submissions/229c9f1a-26b4-4408-88d5-e39036596db4

import Definitions.Def_Submission_ThreeSum_TernaryExtensionSearchCorrect
import Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu
import Definitions.Def_Submission_ThreeSum_LightExtensionSeedRow
import Definitions.Def_Submission_ThreeSum_LightNaturalDot
import Definitions.Def_Submission_ThreeSum_TernaryExtensionSeedSemantics
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_raw_zero
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.LightPolynomialCoefficient.raw_zero



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
attribute [local instance] ThreeSum.TernaryExtensionEncoding._p2m_local_instance_7138b7e7ca_12
variable {f : (ZMod p)[X]}
variable [Fact (Irreducible f)] [Fintype (AdjoinRoot f)]
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution (Λ : ℕ) (ℓ : AdjoinRoot f →ₗ[ZMod p] ZMod p)
    (x y : AdjoinRoot f) (i : Fin Λ) :
    TernaryOriginalRowMenu.seedRow Λ ℓ (x,y) i=ℓ (y*x^i.val) := by
  unfold TernaryOriginalRowMenu.seedRow TernaryOriginalRowMenu.row
    TernaryOriginalRowMenu.evalVector TernaryOriginalRowMenu.vectorPoly
  simp only [LinearMap.comp_apply,LinearMap.flip_apply,LinearMap.coe_mk,AddHom.coe_mk,
    LinearMap.pi_apply,LinearMap.proj_apply,LinearMap.restrictScalars_apply,
    Polynomial.ofFn_eq_sum_monomial,map_sum]
  simp [TernaryOriginalRowMenu.pairing,Pi.single_apply,mul_comm]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    simp [hji]
  · simp
end ThreeSum.TernaryExtensionEncoding
