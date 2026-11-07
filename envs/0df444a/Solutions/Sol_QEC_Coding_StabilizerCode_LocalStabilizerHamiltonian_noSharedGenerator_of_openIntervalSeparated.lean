-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.noSharedGenerator_of_openIntervalSeparated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:35:30.239996+00:00
-- url     : https://prove2.me/submissions/00724f01-200e-4622-821b-29ebfac70c97

import Definitions.Def_QEC_Coding_Stabilizer_Cleaning
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_AlternatingStripDistance

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
open PauliSymplectic
namespace QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
theorem _root_.solution
    {L : Nat} {κ : Type*} [Fintype κ]
    (H : LocalStabilizerHamiltonian
      (ι := StripGeometry.Site L) (κ := κ))
    (r : Nat) (A B : Finset (StripGeometry.Site L))
    (hLocal : StripGeometry.HasOpenIntervalGeneratorSupport H r)
    (hSeparated : StripGeometry.OpenIntervalSeparated L r A B) :
    H.NoSharedGenerator A B := by
  intro j hboth
  obtain ⟨start, width, hwidth, hsupport⟩ := hLocal j
  rcases hSeparated start width hwidth with hA | hB
  · exact hboth.1
      (Finset.disjoint_of_subset_left hsupport hA)
  · exact hboth.2
      (Finset.disjoint_of_subset_left hsupport hB)
end QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
