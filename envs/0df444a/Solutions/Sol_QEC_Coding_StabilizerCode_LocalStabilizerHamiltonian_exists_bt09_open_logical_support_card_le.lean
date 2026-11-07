-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.exists_bt09_open_logical_support_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:22:14.546495+00:00
-- url     : https://prove2.me/submissions/99ca6e63-5b88-474e-b1d6-782dc7c42bc8

import Definitions.Def_QEC_Coding_Stabilizer_Cleaning
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_AlternatingStripDistance
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_card_openVerticalInterval_le
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_exists_bt09_open_strip_logical_of_two_le_range
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
open PauliSymplectic
namespace QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
theorem _root_.solution
    {L r : Nat} {κ : Type*} [Fintype κ]
    (H : LocalStabilizerHamiltonian
      (ι := StripGeometry.Site L) (κ := κ))
    (hr : 2 ≤ r) (hL : 2 * (r - 1) ^ 2 ≤ L)
    (hLocal : StripGeometry.HasOpenIntervalGeneratorSupport H r)
    (P : Binary (StripGeometry.Site L))
    (hPNormalizer : H.code.1.InBinaryNormalizer P)
    (hPNontrivial : ¬ H.code.1.InGeneratedGroupUpToSign P) :
    ∃ Q : Binary (StripGeometry.Site L),
      H.code.1.InBinaryNormalizer Q ∧
      ¬ H.code.1.InGeneratedGroupUpToSign Q ∧
      (support Q).card ≤ r * L := by
  obtain ⟨start, width, hwidth, Q,
    hQNormalizer, hQNontrivial, hQSupport⟩ :=
    H.exists_bt09_open_strip_logical_of_two_le_range
      hr hL hLocal P hPNormalizer hPNontrivial
  have hwidthLe : width ≤ r := by
    rcases hwidth with rfl | rfl <;> omega
  refine ⟨Q, hQNormalizer, hQNontrivial, ?_⟩
  exact
    (Finset.card_le_card hQSupport).trans
      ((StripGeometry.card_openVerticalInterval_le L start width).trans
        (Nat.mul_le_mul_right L hwidthLe))
end QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
