-- Prove2me | solution 1 for QEC.Coding.PauliErrorPath.endpoint_reverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:58:22.664697+00:00
-- url     : https://prove2.me/submissions/57c5fc40-ea83-407a-9aa7-31c3c9846f29

import Definitions.Def_QEC_Coding_Stabilizer_Energy
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
import Theorems.Thm_QEC_Coding_PauliErrorPath_accumulate_reverse_map_binaryDagger

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
    γ.reverse.endpoint = binaryDagger γ.endpoint :=
  accumulate_reverse_map_binaryDagger γ.increments
end QEC.Coding.PauliErrorPath
