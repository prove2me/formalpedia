-- Prove2me | solution 1 for QEC.Locality.restrictBinaryTo_eq_embeddedLocalPauli
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:10:47.322713+00:00
-- url     : https://prove2.me/submissions/3fadd871-7a33-4373-903b-4d8ce465fe87

import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding
open PauliSymplectic
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution (S : FiniteSubsystem ι) (E : Binary ι) :
    restrictBinaryTo S.selected E = embeddedLocalPauli S (localIndexOfBinary S E) := by
  rfl
end QEC.Locality
