-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.firstParity_periodic_pairwise_intervalSeparated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:59:18.933179+00:00
-- url     : https://prove2.me/submissions/f3edeeff-410d-4f83-ac49-f40e77907918

import Definitions.Def_QEC_Coding_Stabilizer_Cleaning
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_AlternatingStripDistance
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_periodicIntervalSeparated_of_gaps
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_firstParity_pairwise_openSeparatedByGap
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_firstParity_site_add_range_le_end
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_sum


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
open PauliSymplectic
open QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry
namespace QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry
theorem _root_.solution
    (L r : Nat) (widths : List Nat)
    (hSum : widths.sum = L)
    (hEven : Even widths.length)
    (hLower : ∀ width ∈ widths, r - 1 ≤ width) :
    (firstParity (openStripListAux L 0 widths)).Pairwise
      (PeriodicIntervalSeparated L r) := by
  let regions := firstParity (openStripListAux L 0 widths)
  have hDirect :
      regions.Pairwise (OpenSeparatedByGap r) :=
    firstParity_pairwise_openSeparatedByGap L r 0 widths hLower
  apply hDirect.imp_of_mem
  intro A B hA hB hAB
  apply periodicIntervalSeparated_of_gaps
  intro p hp q hq
  constructor
  · exact hAB p hp q hq
  · have hqEnd :=
      firstParity_site_add_range_le_end
        L r 0 widths hEven hLower hB hq
    omega
end QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry
