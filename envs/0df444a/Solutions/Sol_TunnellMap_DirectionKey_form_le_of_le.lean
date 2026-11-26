-- Prove2me | solution 1 for TunnellMap.DirectionKey.form_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:30:05.606846+00:00
-- url     : https://prove2.me/submissions/b4b6ec0b-309e-4dd0-9a88-aaac84ffe4de

import Definitions.Def_TunnellMap_PrimitiveDirection
import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_ProjectiveKey
import Theorems.Thm_TunnellMap_DirectionKey_lt_iff

set_option autoImplicit true
open TunnellMap
open TunnellMap.DirectionKey
namespace TunnellMap.DirectionKey
theorem _root_.solution {a b : DirectionKey} (h : a ≤ b) : a.form ≤ b.form := by
  rcases lt_or_ge b a with hba | hab
  · exact absurd (lt_of_lt_of_le hba h) (lt_irrefl _)
  · rcases eq_or_lt_of_le h with rfl | hlt
    · exact le_refl _
    · rcases (lt_iff a b).mp hlt with hform | ⟨hform, _⟩
      · exact hform.le
      · exact hform.le
end TunnellMap.DirectionKey
