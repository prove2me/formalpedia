-- Prove2me | solution 1 for ThreeSum.LightIrreducibleFinder.degreeFlag_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:40:37.939812+00:00
-- url     : https://prove2.me/submissions/ce028e4b-21ca-48ae-8a4e-320b924fca0a

import Definitions.Def_Submission_ThreeSum_LightExtensionFactorSearch
import Definitions.Def_Submission_ThreeSum_LightArgumentTable
import Definitions.Def_Submission_ThreeSum_TernaryExtensionSearchCorrect
import Definitions.Def_Submission_ThreeSum_TernaryCoefficientCodes
import Definitions.Def_Submission_ThreeSum_LightTernaryRowSelector
import Definitions.Def_Submission_ThreeSum_LightIrreducibleFinder
import Theorems.Thm_ThreeSum_LightIrreducibleFinder_program_length
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
import Theorems.Thm_ThreeSum_LightExtensionFactorSearch_nohit_all
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_raw_zero
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_factor_check_iff
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_irreducible_code_iff
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
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero


attribute [local simp] ThreeSum.LightIrreducibleFinder.program_length

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightIrreducibleFinder
open Light ThreeSum.LightExtensionFactorPredicate
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 6000000
set_option maxRecDepth 12000
variable {lim : Limits}
open TernaryExtensionEncoding
namespace ThreeSum.LightIrreducibleFinder
theorem _root_.solution (C : Layout) [Fact C.p.Prime] {c : ℕ}
    (hd : 0<C.dim) (hc : c<C.p^C.dim) :
    degreeFlag C (C.p^C.dim) (codeDigits (p := C.p) (c+C.p^C.dim)) (C.dim-1)=1 ↔
      Irreducible (monicOfCode (p := C.p) C.dim c) := by
  have hp := (Fact.out : C.p.Prime).one_lt
  have hq : 0<C.p^C.dim := pow_pos (by omega) _
  have step (e : ℕ) (he : 0<e) (hed : e<C.dim) :
      factorFirst C (C.p^C.dim) (codeDigits (p := C.p) (c+C.p^C.dim)) e=0 ↔
        ∀ u<C.p^e, ∀ v<C.p^(C.dim-e),
          monicOfCode (p := C.p) e u*monicOfCode (C.dim-e) v≠monicOfCode C.dim c := by
    rw [factorFirst,LightExtensionFactorSearch.nohit_all _ _ _ hq (by simpa [atDegree] using Nat.le_of_lt hp)
      (by simpa [atDegree] using Nat.le_of_lt hed) (by simp [atDegree])]
    constructor
    · intro h u hu v hv hm
      apply h u v
      refine ⟨hu,hv,?_⟩
      exact (factor_check_iff hd hed hc hu hv).mpr hm
    · intro h u v hg
      exact h u hg.1 v hg.2.1 ((factor_check_iff hd hed hc hg.1 hg.2.1).mp hg.2.2)
  rw [irreducible_code_iff hd]
  constructor
  · intro h e he hed
    have hh : ∀t<C.dim-1, factorFirst C (C.p^C.dim) (codeDigits (p := C.p) (c+C.p^C.dim)) (t+1)=0 := by
      unfold degreeFlag at h
      split_ifs at h with hh
      · exact hh
    exact (step e he hed).mp (by simpa only [Nat.sub_add_cancel he] using hh (e-1) (by omega))
  · intro h
    unfold degreeFlag
    apply if_pos
    intro t ht
    exact (step (t+1) (by omega) (by omega)).mpr (h (t+1) (by omega) (by omega))
end ThreeSum.LightIrreducibleFinder
