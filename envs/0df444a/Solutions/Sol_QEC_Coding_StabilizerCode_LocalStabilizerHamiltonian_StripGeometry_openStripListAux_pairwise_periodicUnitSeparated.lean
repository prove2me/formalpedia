-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.openStripListAux_pairwise_periodicUnitSeparated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:55:33.131865+00:00
-- url     : https://prove2.me/submissions/10e1e7b3-bab8-4e27-984f-584085695d18

import Definitions.Def_QEC_Coding_Stabilizer_Cleaning
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_AlternatingStripDistance
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_periodicIntervalSeparated_of_gaps
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_openStripListAux_pairwise_unitGap

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
    (L : Nat) (widths : List Nat)
    (hPositive : ∀ width ∈ widths, 1 ≤ width) :
    (openStripListAux L 0 widths).Pairwise
      (PeriodicIntervalSeparated L 1) := by
  have hDirect :=
    openStripListAux_pairwise_unitGap L 0 widths hPositive
  apply hDirect.imp
  intro A B hAB
  apply periodicIntervalSeparated_of_gaps
  intro p hp q hq
  constructor
  · exact hAB p hp q hq
  · have hqUpper : q.1.val < L := q.1.isLt
    omega
end QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry
