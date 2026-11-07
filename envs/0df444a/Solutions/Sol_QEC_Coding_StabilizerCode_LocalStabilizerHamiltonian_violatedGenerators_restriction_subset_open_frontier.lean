-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.violatedGenerators_restriction_subset_open_frontier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:46:48.553764+00:00
-- url     : https://prove2.me/submissions/9250900e-a70a-457c-a08a-8a541ab03c64

import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_AlternatingStripDistance
import Definitions.Def_QEC_Coding_Stabilizer_SupportEnergyBounds
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_StripLogicalPath
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_support_restrictBinaryTo_subset_support
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_rowMajorPrefix_row_bounds
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_open_crossing_mem_movingFrontier
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_not_commutes_complement_of_not_commutes_restriction
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_mem_incidentGeneratorUnion_of_mem_generatorSupport
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_mem_violatedGenerators
import Theorems.Thm_QEC_Locality_commutes_of_disjoint_support
import Theorems.Thm_QEC_Locality_restrictBinaryTo_vector_add_of_support_subset_union
import Theorems.Thm_QEC_Locality_support_restrictBinaryTo_subset
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.mem_violatedGenerators



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open PauliSymplectic
open scoped Classical
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
open QEC.Coding.StabilizerCode QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
variable {κ : Type*} [Fintype κ]
namespace QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
theorem _root_.solution
    {L r stripStart stripWidth n : Nat}
    (H : LocalStabilizerHamiltonian
      (ι := StripGeometry.Site L) (κ := κ))
    (hL : 0 < L)
    (hRowLocal :
      StripGeometry.HasOpenRowIntervalGeneratorSupport H r)
    (Q : Binary (StripGeometry.Site L))
    (hQNormalizer : H.code.1.InBinaryNormalizer Q)
    (hQStrip :
      support Q ⊆
        StripGeometry.openVerticalInterval L stripStart stripWidth) :
    H.violatedGenerators
        (Locality.restrictBinaryTo (StripGeometry.rowMajorPrefix L n) Q) ⊆
      H.incidentGeneratorUnion
        (StripGeometry.movingFrontier
          L stripStart stripWidth (n / L) r) := by
  intro j hj
  rw [mem_violatedGenerators] at hj
  let R := StripGeometry.rowMajorPrefix L n
  let E := Locality.restrictBinaryTo R Q
  let F := Locality.restrictBinaryTo Rᶜ Q
  have hnotDisjointE :
      ¬ Disjoint (support E) (support (H.generators j)) := by
    intro hdisjoint
    exact hj (QEC.Locality.commutes_of_disjoint_support E
      (H.generators j) hdisjoint)
  obtain ⟨p, hpE, hpGenerator⟩ :=
    Finset.not_disjoint_iff.mp hnotDisjointE
  have hpR : p ∈ R :=
    Locality.support_restrictBinaryTo_subset R Q hpE
  have hpQ : p ∈ support Q :=
    StripGeometry.support_restrictBinaryTo_subset_support R Q hpE
  have hRDisjoint : Disjoint R Rᶜ := by
    apply Finset.disjoint_left.mpr
    intro i hiR hiCompl
    exact (Finset.mem_compl.mp hiCompl) hiR
  have hQCover : support Q ⊆ R ∪ Rᶜ := by
    intro i _hi
    by_cases hiR : i ∈ R
    · exact Finset.mem_union_left _ hiR
    · exact Finset.mem_union_right _ (Finset.mem_compl.mpr hiR)
  have hdecomp : Q.vector = E.vector + F.vector := by
    exact
      Locality.restrictBinaryTo_vector_add_of_support_subset_union
        R Rᶜ Q hRDisjoint hQCover
  have hFNotCommutes : ¬ Commutes F (H.generators j) :=
    H.not_commutes_complement_of_not_commutes_restriction
      Q E F j hQNormalizer hdecomp hj
  have hnotDisjointF :
      ¬ Disjoint (support F) (support (H.generators j)) := by
    intro hdisjoint
    exact hFNotCommutes
      (QEC.Locality.commutes_of_disjoint_support F
        (H.generators j) hdisjoint)
  obtain ⟨q, hqF, hqGenerator⟩ :=
    Finset.not_disjoint_iff.mp hnotDisjointF
  have hqCompl : q ∈ Rᶜ :=
    Locality.support_restrictBinaryTo_subset Rᶜ Q hqF
  have hqNotR : q ∉ R := Finset.mem_compl.mp hqCompl
  have hRows :=
    StripGeometry.rowMajorPrefix_row_bounds hL p q hpR hqNotR
  have hpFrontier :
      p ∈ StripGeometry.movingFrontier
        L stripStart stripWidth (n / L) r :=
    StripGeometry.open_crossing_mem_movingFrontier
      H hRowLocal j p q hpGenerator hqGenerator
        (hQStrip hpQ) hRows.1 hRows.2
  exact
    H.mem_incidentGeneratorUnion_of_mem_generatorSupport
      _ p j hpFrontier hpGenerator
end QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
