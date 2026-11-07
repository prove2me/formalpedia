-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.firstParity_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:31:34.566626+00:00
-- url     : https://prove2.me/submissions/9b9ea77b-bfa9-4355-ae05-7e3817eb9552

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
theorem _root_.solution {α : Type*} (A : α) :
    firstParity [A] = [A] := rfl
end QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry
