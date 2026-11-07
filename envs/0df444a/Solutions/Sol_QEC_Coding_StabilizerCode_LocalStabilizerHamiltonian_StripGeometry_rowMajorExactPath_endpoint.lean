-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.rowMajorExactPath_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:15:17.599316+00:00
-- url     : https://prove2.me/submissions/12aac876-2ffc-40df-8ad8-23994001e76c

import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_AlternatingStripDistance
import Definitions.Def_QEC_Coding_Stabilizer_SupportEnergyBounds
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_StripLogicalPath

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open PauliSymplectic
open scoped Classical
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
open QEC.Coding.StabilizerCode QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry
namespace QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry
theorem _root_.solution
    {L : Nat} (Q : Binary (Site L)) :
    (rowMajorExactPath Q).endpoint = Q :=
  PauliErrorPath.orderedExact_endpoint Q (rowMajorSites L)
    (rowMajorSites_nodup L) (rowMajorSites_toFinset L)
end QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry
