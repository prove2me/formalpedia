-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.first_quotient_code
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:39:49.058726+00:00
-- url     : https://prove2.me/submissions/bca49ffe-9f3a-4397-91e3-71ae3257a561

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
import Theorems.Thm_ThreeSum_LightPairSearch_first_pair_spec
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_raw_zero
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_quotient_code_correct
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_quotient_code_exists
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
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution (hf : f.Monic) (hd : 0<f.natDegree)
    {c x y : ℕ} (hc : c<p^f.natDegree) (hx : x<p^f.natDegree) (hy : y<p^f.natDegree)
    (hm : monicOfCode (p := p) f.natDegree c=f) :
    let q := p^f.natDegree
    let result := LightPairSearch.first
      (LightPairSearch.goodCode q (quotientGood (p := p) f.natDegree c x y)) (q*q)
    0<result ∧ (result-1)%q=encodedMul hf x y := by
  classical
  dsimp only
  let q := p^f.natDegree
  let good := quotientGood (p := p) f.natDegree c x y
  have hq : 0<q := pow_pos (Fact.out : p.Prime).pos _
  have hs := LightPairSearch.first_pair_spec q hq good
  obtain ⟨h,hh,r,hr,hg⟩ := quotient_code_exists hf hd hc hm x y
  have hn : LightPairSearch.first (LightPairSearch.goodCode q good) (q*q)≠0 := by
    intro hz
    exact (hs.1.mp hz h hh r hr) hg
  obtain ⟨code,hcode⟩ := Nat.exists_eq_succ_of_ne_zero hn
  obtain ⟨hu,hv,hgood,hmin⟩ := hs.2 code hcode
  have hcproduct := quotient_code_correct hf hc hx hy hv hm hgood
  refine ⟨Nat.pos_of_ne_zero hn,?_⟩
  change (LightPairSearch.first (LightPairSearch.goodCode q good) (q*q)-1)%q=encodedMul hf x y
  rw [hcode,Nat.succ_sub_one]
  unfold encodedMul
  rw [dif_pos hx,dif_pos hy]
  exact hcproduct.symm
end ThreeSum.TernaryExtensionEncoding
