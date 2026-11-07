-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.exists_bt09_periodic_strip_logical_of_two_le_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:18:35.596524+00:00
-- url     : https://prove2.me/submissions/480ae72c-790c-41e3-86f8-302a74eb1e88

import Definitions.Def_QEC_Coding_Stabilizer_Cleaning
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_AlternatingStripDistance
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_exists_alternatingWidthDecomposition
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_firstParity_sublist
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_secondParity_sublist
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_secondParity_pairwise
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_mem_openStripListAux_exists
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_openStripListAux_pairwise_disjoint
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_firstParity_periodic_pairwise_intervalSeparated
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_secondParity_periodic_pairwise_intervalSeparated
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_noSharedGenerator_of_periodicIntervalSeparated
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_regionUnion_openStrips_eq_univ
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_regionUnion_firstParity_union_secondParity
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_exists_logical_supported_in_alternating_partition

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
    (hLocal : StripGeometry.HasPeriodicIntervalGeneratorSupport H r)
    (P : Binary (StripGeometry.Site L))
    (hPNormalizer : H.code.1.InBinaryNormalizer P)
    (hPNontrivial : ¬ H.code.1.InGeneratedGroupUpToSign P) :
    ∃ start width, (width = r - 1 ∨ width = r) ∧
      ∃ Q : Binary (StripGeometry.Site L),
        H.code.1.InBinaryNormalizer Q ∧
        ¬ H.code.1.InGeneratedGroupUpToSign Q ∧
        support Q ⊆
          StripGeometry.openVerticalInterval L start width := by
  let D : AlternatingWidthDecomposition L r :=
    Classical.choice (exists_alternatingWidthDecomposition hr hL)
  let strips :=
    StripGeometry.openStripListAux L 0 D.widths
  let firstRegions := StripGeometry.firstParity strips
  let secondRegions := StripGeometry.secondParity strips
  have hWidthLower : ∀ width ∈ D.widths, r - 1 ≤ width := by
    intro width hwidth
    rcases D.width_eq width hwidth with hEq | hEq <;> omega
  have hAllDisjoint : strips.Pairwise Disjoint :=
    StripGeometry.openStripListAux_pairwise_disjoint L 0 D.widths
  have hFirstSeparated :
      firstRegions.Pairwise H.NoSharedGenerator := by
    have hGeometry :=
      StripGeometry.firstParity_periodic_pairwise_intervalSeparated
        L r D.widths D.sum_widths D.even_length hWidthLower
    exact hGeometry.imp fun h =>
      H.noSharedGenerator_of_periodicIntervalSeparated r _ _ hLocal h
  have hSecondSeparated :
      secondRegions.Pairwise H.NoSharedGenerator := by
    have hGeometry :=
      StripGeometry.secondParity_periodic_pairwise_intervalSeparated
        L r D.widths hWidthLower
    exact hGeometry.imp fun h =>
      H.noSharedGenerator_of_periodicIntervalSeparated r _ _ hLocal h
  have hSecondDisjoint : secondRegions.Pairwise Disjoint :=
    StripGeometry.secondParity_pairwise hAllDisjoint
  have hCover :
      regionUnion firstRegions ∪ regionUnion secondRegions =
        (Finset.univ : Finset (StripGeometry.Site L)) := by
    calc
      regionUnion firstRegions ∪ regionUnion secondRegions =
          regionUnion strips := by
            exact
              StripGeometry.regionUnion_firstParity_union_secondParity
                strips
      _ = (Finset.univ : Finset (StripGeometry.Site L)) := by
            exact StripGeometry.regionUnion_openStrips_eq_univ D
  obtain ⟨R, hR, Q, hQNormalizer, hQNontrivial, hQSupport⟩ :=
    H.exists_logical_supported_in_alternating_partition
      firstRegions secondRegions hFirstSeparated hSecondDisjoint
      hSecondSeparated hCover P hPNormalizer hPNontrivial
  have hRStrips : R ∈ strips := by
    rcases List.mem_append.mp hR with hFirst | hSecond
    · exact (StripGeometry.firstParity_sublist strips).subset hFirst
    · exact (StripGeometry.secondParity_sublist strips).subset hSecond
  obtain ⟨start, width, hwidth, rfl⟩ :=
    StripGeometry.mem_openStripListAux_exists hRStrips
  exact
    ⟨start, width, D.width_eq width hwidth, Q,
      hQNormalizer, hQNontrivial, hQSupport⟩
end QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
