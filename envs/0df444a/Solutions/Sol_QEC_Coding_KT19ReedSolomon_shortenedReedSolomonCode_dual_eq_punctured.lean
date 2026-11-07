-- Prove2me | solution 1 for QEC.Coding.KT19ReedSolomon.shortenedReedSolomonCode_dual_eq_punctured
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:15:07.725539+00:00
-- url     : https://prove2.me/submissions/8fdcb157-412f-4839-99b4-f2b1e1b636f9

import Definitions.Def_QEC_Coding_ReedSolomon_FullLength
import Definitions.Def_QEC_Coding_ReedSolomon_Punctured
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_shortenedReedSolomonCode_dimension
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_puncturedReedSolomonCode_dimension
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_mem_reedSolomonCode
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_reedSolomonCode_dual
import Theorems.Thm_QEC_Coding_LinearCode_dual_dimension_eq_length_sub_dimension
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
private theorem keptPunctureLocation_card (p k : Nat) [Fact p.Prime]
    (hkp : k ≤ p) :
    Fintype.card (KeptPunctureLocation p k) = p - k := by
  simpa using keptPunctureLocations_card p k hkp
private theorem wordPairing_restrictKept_eq_of_restrictSelected_eq_zero
    {p k : Nat} [Fact p.Prime]
    (left right : Word (ZMod p) (ZMod p))
    (hselected : restrictSelected p k left = 0) :
    wordPairing (restrictKept p k left) (restrictKept p k right) =
      wordPairing left right := by
  classical
  letI selectedPunctureSubtypeFintype :
      Fintype {point : ZMod p // point ∈ selectedPunctureLocations p k} :=
    Subtype.fintype _
  have hsplit :=
    Fintype.sum_subtype_add_sum_subtype
      (fun point : ZMod p => point ∈ selectedPunctureLocations p k)
      (fun point => left point * right point)
  let complementKept :
      {point : ZMod p // ¬ point ∈ selectedPunctureLocations p k} ≃
        KeptPunctureLocation p k :=
    { toFun := fun point => ⟨point.1,
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, point.2⟩⟩
      invFun := fun point => ⟨point.1, (Finset.mem_sdiff.mp point.2).2⟩
      left_inv := fun point => Subtype.ext rfl
      right_inv := fun point => Subtype.ext rfl }
  change (∑ point : KeptPunctureLocation p k, left point.1 * right point.1) =
    ∑ point : ZMod p, left point * right point
  have hselectedSum :
      (∑ point : {point : ZMod p // point ∈ selectedPunctureLocations p k},
        left point.1 * right point.1) = 0 := by
    apply Finset.sum_eq_zero
    intro point _
    have hpoint : left point.1 = 0 := by
      simpa using congrFun hselected
        (⟨point.1, point.2⟩ : SelectedPunctureLocation p k)
    rw [hpoint]
    simp
  have hcomplement :
      (∑ point : {point : ZMod p // ¬ point ∈ selectedPunctureLocations p k},
        left point.1 * right point.1) =
        ∑ point : ZMod p, left point * right point := by
    rw [hselectedSum, zero_add] at hsplit
    exact hsplit
  have hequiv :
      (∑ point : {point : ZMod p // ¬ point ∈ selectedPunctureLocations p k},
        left point.1 * right point.1) =
        ∑ point : KeptPunctureLocation p k, left point.1 * right point.1 := by
    exact Fintype.sum_equiv complementKept _ _ (fun _ => rfl)
  exact hequiv.symm.trans hcomplement
private theorem puncturedReedSolomonCode_le_dual_shortenedComplementary
    (p l k : Nat) [Fact p.Prime] (hlp : l ≤ p) :
    (puncturedReedSolomonCode p l k).carrier ≤
      (shortenedReedSolomonCode p (p - l) k).dual.carrier := by
  intro word hword
  refine ((shortenedReedSolomonCode p (p - l) k).mem_dual word).2 ?_
  intro shortened hshortened
  rcases (mem_puncturedReedSolomonCode word).1 hword with
    ⟨fullWord, hfullWord, hrestrictWord⟩
  rcases (mem_shortenedReedSolomonCode shortened).1 hshortened with
    ⟨fullShortened, hfullShortened, hselected, hrestrictShortened⟩
  have hfullWordDual : fullWord ∈ (reedSolomonCode p (p - l)).dual.carrier := by
    rw [reedSolomonCode_dual p (p - l) (Nat.sub_le _ _)]
    simpa only [Nat.sub_sub_self hlp] using hfullWord
  have horthogonal := (reedSolomonCode p (p - l)).orthogonal_of_mem_dual
    hfullWordDual hfullShortened
  rw [← hrestrictWord, ← hrestrictShortened]
  calc
    wordPairing (restrictKept p k fullWord)
        (restrictKept p k fullShortened) =
        wordPairing (restrictKept p k fullShortened)
          (restrictKept p k fullWord) := by
      simp only [wordPairing_apply, dotProduct_comm]
    _ = wordPairing fullShortened fullWord :=
      wordPairing_restrictKept_eq_of_restrictSelected_eq_zero
        fullShortened fullWord hselected
    _ = 0 := by
      simpa [wordPairing_apply, dotProduct_comm] using horthogonal
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
    (h : Admissible p l k) :
    (shortenedReedSolomonCode p (p - l) k).dual.carrier =
      (puncturedReedSolomonCode p l k).carrier := by
  rcases h with ⟨hp, hk, hkl, hlp, hproduct⟩
  have hkp : k ≤ p := hkl.trans hlp
  have hkm : k ≤ p - l := by omega
  have hkeptLength : l ≤ p - k := by omega
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · exact puncturedReedSolomonCode_le_dual_shortenedComplementary p l k hlp
  · change Dimension (puncturedReedSolomonCode p l k) =
      Dimension (shortenedReedSolomonCode p (p - l) k).dual
    rw [LinearCode.dual_dimension_eq_length_sub_dimension,
      puncturedReedSolomonCode_dimension p l k hkp hkeptLength,
      shortenedReedSolomonCode_dimension p (p - l) k hkp hkm (Nat.sub_le _ _)]
    simp [Length, keptPunctureLocation_card p k hkp]
    omega
end QEC.Coding.KT19ReedSolomon
