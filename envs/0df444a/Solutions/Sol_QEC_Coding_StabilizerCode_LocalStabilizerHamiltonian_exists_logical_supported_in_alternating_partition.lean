-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.exists_logical_supported_in_alternating_partition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:15:27.393746+00:00
-- url     : https://prove2.me/submissions/97b17489-6a9e-4f9b-8fe7-b1162f54f67b

import Definitions.Def_QEC_Coding_Stabilizer_Cleaning
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_AlternatingStripDistance
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_exists_logical_supported_in_remaining_region

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
    (firstRegions secondRegions : List (Finset ι))
    (hFirstSeparated : firstRegions.Pairwise H.NoSharedGenerator)
    (hSecondDisjoint : secondRegions.Pairwise Disjoint)
    (hSecondSeparated : secondRegions.Pairwise H.NoSharedGenerator)
    (hCover :
      regionUnion firstRegions ∪ regionUnion secondRegions =
        (Finset.univ : Finset ι))
    (P : Binary ι)
    (hPNormalizer : H.code.1.InBinaryNormalizer P)
    (hPNontrivial : ¬ H.code.1.InGeneratedGroupUpToSign P) :
    ∃ R ∈ firstRegions ++ secondRegions, ∃ Q : Binary ι,
      H.code.1.InBinaryNormalizer Q ∧
      ¬ H.code.1.InGeneratedGroupUpToSign Q ∧
      support Q ⊆ R := by
  by_cases hNoLocal : ∀ R ∈ firstRegions, H.NoLocalLogical R
  · obtain ⟨R, hR, Q, hQNormalizer, hQNontrivial, hQSupport⟩ :=
      H.exists_logical_supported_in_remaining_region
        firstRegions secondRegions hFirstSeparated hSecondDisjoint
        hSecondSeparated hCover hNoLocal P hPNormalizer hPNontrivial
    exact
      ⟨R, List.mem_append_right firstRegions hR, Q,
        hQNormalizer, hQNontrivial, hQSupport⟩
  · push Not at hNoLocal
    obtain ⟨R, hR, hRLocal⟩ := hNoLocal
    unfold NoLocalLogical at hRLocal
    push Not at hRLocal
    obtain ⟨Q, hQNormalizer, hQNontrivial, hQSupport⟩ := hRLocal
    exact
      ⟨R, List.mem_append_left secondRegions hR, Q,
        hQNormalizer, hQNontrivial, hQSupport⟩
end QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
