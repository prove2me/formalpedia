-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.secondParity_pairwise
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:36:04.732546+00:00
-- url     : https://prove2.me/submissions/d610a107-0b6d-4b42-9f44-7397ea1582a0

import Definitions.Def_QEC_Coding_Stabilizer_Cleaning
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_AlternatingStripDistance
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_secondParity_sublist

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
    {α : Type*} {relation : α → α → Prop} {regions : List α}
    (h : regions.Pairwise relation) :
    (secondParity regions).Pairwise relation :=
  h.sublist (secondParity_sublist regions)
end QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry
