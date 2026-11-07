-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.projectiveDominantCoweight_rankThree_colorOneReachable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:45:32.435727+00:00
-- url     : https://prove2.me/submissions/b099a078-ade2-4149-841d-051e8a3c95e3

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeGenerators
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_BuildingAdjacency
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_colorOneReachable_smul
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_fundamentalCoweight_rankThree_colorOneReachable
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_three
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankThree_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankThree_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_uniformizerUnit
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_diagonalGeneralLinear_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_dominantCoweight_fundamental
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
    (k : Type u) [Field k] [Finite k]
    (weight : ProjectiveDominantCoweight 2) :
    ColorOneReachable k 3 (QuotientGroup.mk 1)
      (QuotientGroup.mk (dominantCoweight k weight.toDominant)) := by
  refine Nat.strong_induction_on
    (p := fun n => ∀ w : ProjectiveDominantCoweight 2,
      projectiveDominantExponentSum w = n →
        ColorOneReachable k 3 (QuotientGroup.mk 1)
          (QuotientGroup.mk (dominantCoweight k w.toDominant)))
    (projectiveDominantExponentSum weight) ?_ weight rfl
  intro n ih w hw
  by_cases hzero : w = projectiveDominantCoweightZero 2
  · subst w
    simpa using (Relation.ReflTransGen.refl :
      ColorOneReachable k 3 (QuotientGroup.mk 1) (QuotientGroup.mk 1))
  · obtain ⟨previous, color, hdecomp⟩ :=
      exists_rankThree_projective_predecessor w hzero
    let fundamental := fundamentalProjectiveDominantCoweight
      2 (color.val + 1) (by omega)
    have hfundPos : 0 < projectiveDominantExponentSum fundamental := by
      have hterm : 0 < fundamental.toDominant.exponent (0 : Fin 3) := by
        fin_cases color <;>
          simp [fundamental, fundamentalProjectiveDominantCoweight,
            fundamentalDominantCoweight]
      have hle : fundamental.toDominant.exponent (0 : Fin 3) ≤
          projectiveDominantExponentSum fundamental := by
        exact Finset.single_le_sum
          (fun i _ => Nat.zero_le (fundamental.toDominant.exponent i))
          (Finset.mem_univ (0 : Fin 3))
      exact hterm.trans_le hle
    have hpreviousLt : projectiveDominantExponentSum previous < n := by
      rw [← hw, hdecomp, projectiveDominantExponentSum_add]
      exact Nat.lt_add_of_pos_right hfundPos
    have hprevious := ih _ hpreviousLt previous rfl
    have hfund := fundamentalCoweight_rankThree_colorOneReachable k color
    have htranslated := colorOneReachable_smul k 3
      (dominantCoweight k previous.toDominant) hfund
    have htranslated' : ColorOneReachable k 3
        (QuotientGroup.mk (dominantCoweight k previous.toDominant))
        (QuotientGroup.mk
          (dominantCoweight k previous.toDominant *
            dominantCoweight k fundamental.toDominant)) := by
      simpa [MulAction.Quotient.smul_mk, smul_eq_mul, fundamental,
        fundamentalProjectiveDominantCoweight,
        dominantCoweight_fundamental] using htranslated
    have htotal := hprevious.trans htranslated'
    simpa [hdecomp, fundamental,
      dominantCoweight_projectiveDominantCoweightAdd] using htotal
end QEC.Coding.HighDimensionalExpander.SphericalHecke
