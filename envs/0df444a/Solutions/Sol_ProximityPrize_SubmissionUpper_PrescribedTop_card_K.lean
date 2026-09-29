-- Prove2me | solution 1 for ProximityPrize.SubmissionUpper.PrescribedTop.card_K
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-09-27T05:13:02.637183+00:00
-- url     : https://prove2.me/submissions/6c6af8ba-0c1e-4eee-8e62-d9938ac776c8

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Definitions.Def_KoalaBear_fieldSize
import Definitions.Def_ProximityPrize_SubmissionUpper_PrescribedTop_K

namespace ProximityPrize.SubmissionUpper.PrescribedTop

theorem _root_.solution : Fintype.card K = 2 ^ 31 - 2 ^ 24 + 1 :=
  ZMod.card _root_.KoalaBear.fieldSize
end ProximityPrize.SubmissionUpper.PrescribedTop
