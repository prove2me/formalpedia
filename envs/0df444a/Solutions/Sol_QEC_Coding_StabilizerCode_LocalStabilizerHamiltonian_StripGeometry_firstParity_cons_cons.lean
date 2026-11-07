-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.firstParity_cons_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:31:47.208702+00:00
-- url     : https://prove2.me/submissions/94b8e9e3-dea0-497b-8b7d-e7b52e6fe73a

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
open QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry
namespace QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry
theorem _root_.solution {α : Type*}
    (A B : α) (regions : List α) :
    firstParity (A :: B :: regions) = A :: firstParity regions := rfl
end QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry
