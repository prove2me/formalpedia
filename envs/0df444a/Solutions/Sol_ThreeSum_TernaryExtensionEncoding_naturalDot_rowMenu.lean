-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.naturalDot_rowMenu
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:39:50.132021+00:00
-- url     : https://prove2.me/submissions/9bfc5106-de41-482b-93a3-8d9b1e871a05

import Definitions.Def_Submission_ThreeSum_TernaryExtensionSearchCorrect
import Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu
import Definitions.Def_Submission_ThreeSum_LightExtensionSeedRow
import Definitions.Def_Submission_ThreeSum_LightNaturalDot
import Definitions.Def_Submission_ThreeSum_TernaryExtensionSeedSemantics
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_trajectory_rowMenu
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
import Theorems.Thm_ThreeSum_TernaryOriginalRowMenu_row_eq_dot
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
theorem _root_.solution (hf : f.Monic) (hd : 0<f.natDegree) (Λ : ℕ)
    (x y : AdjoinRoot f) (raw : Fin Λ → ℤ)
    (values coefs : ℕ → ℕ)
    (hvalues : ∀ i : Fin Λ, (values i.val : ZMod p)=(raw i : ZMod p))
    (hcoefs : ∀ i : Fin Λ, coefs i.val=
      LightExtensionSeedRow.trajectory (encodedMul hf) (encode hf x) (encode hf y) i.val%p) :
    LightNaturalDot.dot values coefs Λ%p=
      (TernaryOriginalRowMenu.row Λ (constantCoefficient hf hd) (x,y)
        (fun i => (raw i : ZMod p))).val := by
  have he : ((LightNaturalDot.dot values coefs Λ : ℕ) : ZMod p)=
      TernaryOriginalRowMenu.row Λ (constantCoefficient hf hd) (x,y)
        (fun i => (raw i : ZMod p)) := by
    rw [TernaryOriginalRowMenu.row_eq_dot]
    unfold LightNaturalDot.dot LightBooleanDot.dot
    rw [Nat.cast_sum,← Fin.sum_univ_eq_sum_range]
    apply sum_congr rfl
    intro i hi
    rw [Nat.cast_mul,hvalues i,hcoefs i,trajectory_rowMenu hf hd Λ x y i,
      ZMod.natCast_zmod_val]
  have hh := congrArg ZMod.val he
  simpa using hh
end ThreeSum.TernaryExtensionEncoding
