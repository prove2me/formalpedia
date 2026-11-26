-- Prove2me | solution 1 for TunnellMap.isHalfSum_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:17:06.383614+00:00
-- url     : https://prove2.me/submissions/069a9830-5dbc-4749-9e6c-552c4de60e55

import Definitions.Def_TunnellMap_MidpointRecord
import Definitions.Def_TunnellMap_OrthogonalFrameExistence
import Definitions.Def_TunnellMap_QuadraticRoots
import Definitions.Def_TunnellMap_TauLattice
import Definitions.Def_TunnellMap_GeneratorRecovery

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {h₁ h₂ E F : Triple}
    (h₁sum : IsHalfSum h₁ E F) (h₂sum : IsHalfSum h₂ E F) : h₁ = h₂ := by
  rcases h₁sum with ⟨h₁x, h₁y, h₁z⟩
  rcases h₂sum with ⟨h₂x, h₂y, h₂z⟩
  apply Triple.ext <;> omega
end TunnellMap
