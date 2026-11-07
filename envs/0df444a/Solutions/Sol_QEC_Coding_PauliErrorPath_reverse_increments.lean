-- Prove2me | solution 1 for QEC.Coding.PauliErrorPath.reverse_increments
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:31:44.867712+00:00
-- url     : https://prove2.me/submissions/d6311f4d-8e03-4d9e-9b8b-741a11f6ed0b

import Definitions.Def_QEC_Coding_Stabilizer_Energy
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open PauliSymplectic
open scoped Classical
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
open QEC.Coding.PauliErrorPath
namespace QEC.Coding.PauliErrorPath
theorem _root_.solution (γ : PauliErrorPath (ι := ι)) :
    γ.reverse.increments = γ.increments.reverse.map binaryDagger :=
  rfl
end QEC.Coding.PauliErrorPath
