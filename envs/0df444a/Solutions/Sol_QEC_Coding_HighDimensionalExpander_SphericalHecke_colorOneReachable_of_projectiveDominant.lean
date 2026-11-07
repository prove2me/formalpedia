-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.colorOneReachable_of_projectiveDominant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:36:53.766512+00:00
-- url     : https://prove2.me/submissions/d1bd8f3f-35cc-44ae-aa05-f6845d44b956

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeGenerators
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_BuildingAdjacency
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_colorOneReachable_smul
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_three
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankThree_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankThree_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_uniformizerUnit
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_diagonalGeneralLinear_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_exists_mem_projectiveDominantDoubleCoset
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourFundamentalHeckeAlgEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourSecondCompoundGeneralLinear_inv_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankThreeFundamentalHeckeAlgEquiv_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankFour_one
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankFour_three
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankFour_two
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankThree_one
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankThree_two
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.coe_uniformizerUnit
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.diagonalGeneralLinear_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourFundamentalHeckeAlgEquiv_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourSecondCompoundGeneralLinear_inv_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankThreeFundamentalHeckeAlgEquiv_apply



set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups LocalTopology Pointwise
open HeckeFunction
universe u
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type u) [Field k] [Finite k] (n : ℕ)
    (hdominant : ∀ weight : ProjectiveDominantCoweight n,
      ColorOneReachable k (n + 1) (QuotientGroup.mk 1)
        (QuotientGroup.mk (dominantCoweight k weight.toDominant)))
    (q : BuildingVertex k (n + 1)) :
    ColorOneReachable k (n + 1) (QuotientGroup.mk 1) q := by
  obtain ⟨weight, hq⟩ :=
    exists_mem_projectiveDominantDoubleCoset k q.out
  rw [projectiveDominantDoubleCoset, dominantDoubleCoset,
    Set.mem_mul] at hq
  obtain ⟨middle, hmiddle, right, hright, hfactor⟩ := hq
  rw [Set.mem_mul] at hmiddle
  obtain ⟨left, hleft, diagonal, hdiagonal, hmiddleFactor⟩ := hmiddle
  rw [Set.mem_singleton_iff] at hdiagonal
  subst diagonal
  have hpath := hdominant weight
  have htranslated := colorOneReachable_smul k (n + 1) left hpath
  have hleftBase : left •
      (QuotientGroup.mk 1 : BuildingVertex k (n + 1)) =
        QuotientGroup.mk 1 := by
    rw [MulAction.Quotient.smul_mk]
    apply QuotientGroup.eq.mpr
    simpa using (maximalCompact k (n + 1)).inv_mem hleft
  have hmiddlePath : ColorOneReachable k (n + 1)
      (QuotientGroup.mk 1)
      (QuotientGroup.mk
        (left * dominantCoweight k weight.toDominant)) := by
    simpa [hleftBase, MulAction.Quotient.smul_mk, smul_eq_mul]
      using htranslated
  have hrightCoset :
      QuotientGroup.mk
          ((left * dominantCoweight k weight.toDominant) * right) =
        (QuotientGroup.mk
          (left * dominantCoweight k weight.toDominant) :
            BuildingVertex k (n + 1)) := by
    apply QuotientGroup.eq.mpr
    simpa [mul_assoc] using (maximalCompact k (n + 1)).inv_mem hright
  have hqOut :
      (QuotientGroup.mk q.out : BuildingVertex k (n + 1)) = q :=
    q.out_eq'
  rw [← hqOut, ← hfactor, ← hmiddleFactor, hrightCoset]
  exact hmiddlePath
end QEC.Coding.HighDimensionalExpander.SphericalHecke
