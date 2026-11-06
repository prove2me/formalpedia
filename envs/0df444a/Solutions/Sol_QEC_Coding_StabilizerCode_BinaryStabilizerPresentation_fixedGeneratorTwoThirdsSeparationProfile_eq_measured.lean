-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.fixedGeneratorTwoThirdsSeparationProfile_eq_measured
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:12:44.432042+00:00
-- url     : https://prove2.me/submissions/d4ee3c42-d838-4fbe-98f2-85a60029a6a6

import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Definitions.Def_QEC_Locality_SeparatorProfile_Core

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.StabilizerCode QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
open PauliSymplectic
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
namespace QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
theorem _root_.solution
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (scale : Nat) :
    P.fixedGeneratorTwoThirdsSeparationProfile scale =
      Locality.twoThirdsSeparationProfile P.fixedGeneratorInteractionGraph scale :=
  rfl
end QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
