-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.violatedGenerators_subset_incidentGeneratorUnion_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:18:36.569534+00:00
-- url     : https://prove2.me/submissions/51372d95-1872-4c65-ac4c-952aaa43f604

import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Definitions.Def_QEC_Coding_Stabilizer_SupportEnergyBounds
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_mem_incidentGeneratorUnion_of_mem_generatorSupport
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_mem_violatedGenerators
import Theorems.Thm_QEC_Locality_commutes_of_disjoint_support
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.mem_violatedGenerators



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
open PauliSymplectic
open scoped Classical
universe u
variable {κ : Type u} [Fintype κ]
namespace QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
theorem _root_.solution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E : Binary ι) :
    H.violatedGenerators E ⊆ H.incidentGeneratorUnion (support E) := by
  intro j hj
  rw [mem_violatedGenerators] at hj
  have hnotDisjoint :
      ¬ Disjoint (support E) (support (H.generators j)) := by
    intro hdisjoint
    exact hj
      (QEC.Locality.commutes_of_disjoint_support
        E (H.generators j) hdisjoint)
  obtain ⟨i, hiE, hiGenerator⟩ :=
    Finset.not_disjoint_iff.mp hnotDisjoint
  exact
    H.mem_incidentGeneratorUnion_of_mem_generatorSupport
      (support E) i j hiE hiGenerator
end QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
