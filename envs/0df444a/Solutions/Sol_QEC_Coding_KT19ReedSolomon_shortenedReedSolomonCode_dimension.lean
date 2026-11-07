-- Prove2me | solution 1 for QEC.Coding.KT19ReedSolomon.shortenedReedSolomonCode_dimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:17:24.663687+00:00
-- url     : https://prove2.me/submissions/080e8314-5103-405d-8efb-4fde06d87849

import Definitions.Def_QEC_Coding_ReedSolomon_FullLength
import Definitions.Def_QEC_Coding_ReedSolomon_Punctured
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_evaluation_mem_reedSolomonCode
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_mem_reedSolomonCode
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_reedSolomonCode_dimension
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.KT19ReedSolomon.mem_reedSolomonCode
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


section
noncomputable section
namespace QEC
namespace Coding
namespace KT19ReedSolomon
open scoped BigOperators
private theorem restrictSelected_evaluation_selectedInterpolation
    (p k : Nat) [Fact p.Prime] (hkp : k ≤ p)
    (word : Word (ZMod p) (SelectedPunctureLocation p k)) :
    restrictSelected p k (evaluationLinearMap p k (selectedInterpolation p k hkp word)) =
      word := by
  ext point
  change
    ((Lagrange.funEquivDegreeLT
      (s := selectedPunctureLocations p k) (v := fun point : ZMod p => point)
      (by
        intro left hleft right hright heq
        exact heq)).symm word).1.eval point.1 = word point
  exact congrFun ((Lagrange.funEquivDegreeLT
    (s := selectedPunctureLocations p k) (v := fun point : ZMod p => point)
    (by
      intro left hleft right hright heq
      exact heq)).apply_symm_apply word) point
private theorem restrictSelected_evaluation_degreeLTEmbed
    (p a b k : Nat) [Fact p.Prime] (hkp : k ≤ p) (hab : a ≤ b)
    (word : Word (ZMod p) (SelectedPunctureLocation p k))
    (hka : k = a) :
    restrictSelected p k
      (evaluationLinearMap p b
        (degreeLTEmbed p a b hab (by simpa [hka] using selectedInterpolation p k hkp word))) =
      word := by
  subst a
  change restrictSelected p k
      (evaluationLinearMap p k (selectedInterpolation p k hkp word)) = word
  exact restrictSelected_evaluation_selectedInterpolation p k hkp word
private theorem restrictSelected_surjective_on_reedSolomonCode
    (p l k : Nat) [Fact p.Prime] (hkp : k ≤ p) (hkl : k ≤ l) :
    Function.Surjective
      ((restrictSelected p k).domRestrict (reedSolomonCode p l).carrier) := by
  intro word
  let polynomial : Polynomial.degreeLT (ZMod p) l :=
    degreeLTEmbed p k l hkl (selectedInterpolation p k hkp word)
  refine ⟨⟨evaluationLinearMap p l polynomial,
    evaluation_mem_reedSolomonCode p l polynomial⟩, ?_⟩
  exact restrictSelected_evaluation_degreeLTEmbed p k l k hkp hkl word rfl
private theorem restrictKept_injective_on_shortenedReedSolomonDomain
    {p l k : Nat} [Fact p.Prime] :
    Function.Injective
      ((restrictKept p k).domRestrict (shortenedReedSolomonDomain p l k)) := by
  intro left right heq
  apply Subtype.ext
  funext point
  by_cases hselected : point ∈ selectedPunctureLocations p k
  · have hleft : restrictSelected p k left.1 = 0 := left.property.2
    have hright : restrictSelected p k right.1 = 0 := right.property.2
    have hpoint := congrFun hleft ⟨point, hselected⟩
    have hpoint' := congrFun hright ⟨point, hselected⟩
    simpa using hpoint.trans hpoint'.symm
  · have hkept : point ∈ keptPunctureLocations p k := by
      simp [keptPunctureLocations, hselected]
    have hpoint := congrFun heq ⟨point, hkept⟩
    simpa using hpoint
end KT19ReedSolomon
end Coding
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.KT19ReedSolomon
open scoped BigOperators
attribute [local instance] QEC.Coding.KT19ReedSolomon.instNeZeroOfPrime
namespace QEC.Coding.KT19ReedSolomon
theorem _root_.solution (p l k : Nat) [Fact p.Prime]
    (hkp : k ≤ p) (hkl : k ≤ l) (hlp : l ≤ p) :
    Dimension (shortenedReedSolomonCode p l k) = l - k := by
  let selectedMap := (restrictSelected p k).domRestrict (reedSolomonCode p l).carrier
  have hsurjective : Function.Surjective selectedMap := by
    exact restrictSelected_surjective_on_reedSolomonCode p l k hkp hkl
  have hrange : LinearMap.range selectedMap = ⊤ := LinearMap.range_eq_top.mpr hsurjective
  have hrank := LinearMap.finrank_range_add_finrank_ker selectedMap
  rw [hrange, finrank_top, Module.finrank_fintype_fun_eq_card] at hrank
  have hrank' :
      k + Module.finrank (ZMod p) (LinearMap.ker selectedMap) =
        Dimension (reedSolomonCode p l) := by
    simpa [selectedMap, Dimension, selectedPunctureLocations_card p k hkp] using hrank
  have hdomain :
      Module.finrank (ZMod p) (shortenedReedSolomonDomain p l k) =
        Module.finrank (ZMod p) (LinearMap.ker selectedMap) := by
    exact LinearEquiv.finrank_eq shortenedDomainEquivRestrictSelectedKernel
  have hcode :
      Dimension (shortenedReedSolomonCode p l k) =
        Module.finrank (ZMod p) (shortenedReedSolomonDomain p l k) := by
    change Module.finrank (ZMod p)
      ((shortenedReedSolomonDomain p l k).map (restrictKept p k)) = _
    rw [← LinearMap.range_domRestrict]
    exact LinearMap.finrank_range_of_inj
      restrictKept_injective_on_shortenedReedSolomonDomain
  have hrank'' :
      k + Module.finrank (ZMod p) (LinearMap.ker selectedMap) = l :=
    hrank'.trans (reedSolomonCode_dimension p l hlp)
  calc
    Dimension (shortenedReedSolomonCode p l k) =
        Module.finrank (ZMod p) (shortenedReedSolomonDomain p l k) := hcode
    _ = Module.finrank (ZMod p) (LinearMap.ker selectedMap) := hdomain
    _ = l - k := by omega
end QEC.Coding.KT19ReedSolomon
