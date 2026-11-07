-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.exists_nontrivial_logical_restriction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:08:33.277543+00:00
-- url     : https://prove2.me/submissions/66aee411-d60f-4c39-87d2-94bb593972a8

import Definitions.Def_QEC_Coding_Stabilizer_Cleaning
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_AlternatingStripDistance
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_inGeneratedGroupUpToSign_of_restrictions
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_inBinaryNormalizer_restrictBinaryTo_of_mem
import Theorems.Thm_QEC_Locality_support_restrictBinaryTo_subset


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
open PauliSymplectic
namespace QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
theorem _root_.solution
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (regions : List (Finset ι))
    (hdisjoint : regions.Pairwise Disjoint)
    (hseparated : regions.Pairwise H.NoSharedGenerator)
    (E : Binary ι)
    (hNormalizer : H.code.1.InBinaryNormalizer E)
    (hNontrivial : ¬ H.code.1.InGeneratedGroupUpToSign E)
    (hsupport : support E ⊆ regionUnion regions) :
    ∃ R ∈ regions,
      H.code.1.InBinaryNormalizer (Locality.restrictBinaryTo R E) ∧
      ¬ H.code.1.InGeneratedGroupUpToSign (Locality.restrictBinaryTo R E) ∧
      support (Locality.restrictBinaryTo R E) ⊆ R := by
  by_contra hnone
  push Not at hnone
  have hgenerated :
      ∀ R ∈ regions,
        H.code.1.InGeneratedGroupUpToSign (Locality.restrictBinaryTo R E) := by
    intro R hR
    have hRNormalizer :=
      H.inBinaryNormalizer_restrictBinaryTo_of_mem
        regions hseparated E hsupport hNormalizer R hR
    by_contra hRNontrivial
    exact hnone R hR hRNormalizer hRNontrivial
      (Locality.support_restrictBinaryTo_subset R E)
  exact hNontrivial
    (H.inGeneratedGroupUpToSign_of_restrictions
      regions hdisjoint E hsupport hgenerated)
end QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
