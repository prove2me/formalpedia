-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.openStripListAux_pairwise_openUnitSeparated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:55:29.176897+00:00
-- url     : https://prove2.me/submissions/995e2f79-ae0c-4979-94b5-78836f4d163d

import Definitions.Def_QEC_Coding_Stabilizer_Cleaning
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_AlternatingStripDistance
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_openIntervalSeparated_of_gap
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
    (L start : Nat) (widths : List Nat)
    (hPositive : ∀ width ∈ widths, 1 ≤ width) :
    (openStripListAux L start widths).Pairwise
      (OpenIntervalSeparated L 1) :=
  (openStripListAux_pairwise_unitGap
    L start widths hPositive).imp openIntervalSeparated_of_gap
end QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry
