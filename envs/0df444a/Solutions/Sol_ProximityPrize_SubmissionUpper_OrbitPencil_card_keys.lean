-- Prove2me | solution 1 for ProximityPrize.SubmissionUpper.OrbitPencil.card_keys
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-09-27T05:14:14.139501+00:00
-- url     : https://prove2.me/submissions/5cbd5a81-1369-4db9-8d87-d2cce1767658

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Definitions.Def_KoalaBear_fieldSize
import Definitions.Def_ProximityPrize_SubmissionUpper_OrbitPencil_K
import Definitions.Def_ProximityPrize_SubmissionUpper_OrbitPencil_Small
import Definitions.Def_ProximityPrize_SubmissionUpper_PrescribedTop_K
import Theorems.Thm_ProximityPrize_SubmissionUpper_PrescribedTop_card_K

namespace ProximityPrize.SubmissionUpper.OrbitPencil

theorem _root_.solution : Fintype.card ((Fin 14 → K) × Small) =
    (2 ^ 31 - 2 ^ 24 + 1) ^ 14 * 512 := (by
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, PrescribedTop.card_K]
)
end ProximityPrize.SubmissionUpper.OrbitPencil
