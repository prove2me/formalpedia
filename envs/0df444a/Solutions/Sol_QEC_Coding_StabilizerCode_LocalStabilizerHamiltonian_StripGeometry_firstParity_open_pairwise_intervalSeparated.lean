-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.firstParity_open_pairwise_intervalSeparated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:55:40.04521+00:00
-- url     : https://prove2.me/submissions/0aa0e61b-f16e-40d9-afbb-bedc6a8793d4

import Definitions.Def_QEC_Coding_Stabilizer_Cleaning
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_AlternatingStripDistance
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_openIntervalSeparated_of_gap
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_firstParity_pairwise_openSeparatedByGap

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
    (L r start : Nat) (widths : List Nat)
    (hLower : ∀ width ∈ widths, r - 1 ≤ width) :
    (firstParity (openStripListAux L start widths)).Pairwise
      (OpenIntervalSeparated L r) :=
  (firstParity_pairwise_openSeparatedByGap
    L r start widths hLower).imp openIntervalSeparated_of_gap
end QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry
