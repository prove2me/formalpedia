-- Prove2me | solution 1 for ThreeSum.LightMomentZeroDetector.modified_memory
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:43:01.010785+00:00
-- url     : https://prove2.me/submissions/f5e2f17b-8ad8-407b-a4db-f08a69494110

import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_Submission_ThreeSum_LightMomentZeroDetector
import Theorems.Thm_ThreeSum_LightMomentZeroDetector_atoms_target
import Theorems.Thm_ThreeSum_LightMomentZeroDetector_atoms_moment
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Seg_congr
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LightMomentDeterminant_eval_modified
import Theorems.Thm_ThreeSum_LightMomentDeterminant_eval_prodCircuits
import Theorems.Thm_ThreeSum_LightMomentDeterminant_eval_sumCircuits
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LightMomentDeterminant.eval_prodCircuits
attribute [local simp] ThreeSum.LightMomentDeterminant.eval_sumCircuits
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero


attribute [local simp] ThreeSum.LightMomentZeroDetector.atoms_target

set_option autoImplicit false
open ThreeSum ThreeSum.LightMomentZeroDetector
open Light ThreeSum.LightMomentDeterminant ThreeSum.LightFixedArithmetic
open FiniteMomentZeroDetector
namespace ThreeSum.LightMomentZeroDetector
theorem _root_.solution (H base : ℕ) (a : ℤ) (μ : ℕ → ℤ) {t : ℕ}
    (v w : Fin t → ℤ) (hm : ∀ k≤2*H, μ (base+k)=moment v w k)
    (d : ℕ) (hd : d≤H) :
    (modified d).eval (fun i => (atoms H i).val ⟨frame [base,a],μ⟩)=(modifiedHankel v w a d).det := by
  rw [eval_modified]
  congr 1
  ext i j
  have h0 := atoms_target H base a μ
  have h1 := atoms_moment H base (i.val+j.val) a μ (by have := i.isLt; have := j.isLt; omega)
  have h2 := atoms_moment H base (i.val+j.val+1) a μ (by have := i.isLt; have := j.isLt; omega)
  have h3 := atoms_moment H base (i.val+j.val+2) a μ (by have := i.isLt; have := j.isLt; omega)
  simp only [←Nat.add_assoc,Nat.reduceAdd] at h1 h2 h3
  simp only [Matrix.of_apply,h0,h1,h2,h3,modifiedHankel,modifiedMoment]
  simp only [Nat.add_assoc]
  rw [hm _ (by have := i.isLt; have := j.isLt; omega),
    hm _ (by have := i.isLt; have := j.isLt; omega),
    hm _ (by have := i.isLt; have := j.isLt; omega)]
end ThreeSum.LightMomentZeroDetector
